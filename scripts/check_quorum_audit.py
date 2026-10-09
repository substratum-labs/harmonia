#!/usr/bin/env python3
"""Build and inspect the certified quorum audit and its isolated counterexamples."""

import re
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from check_distributed_audit import import_closure, scrub


ROOT = Path(__file__).resolve().parents[1]
CERTIFIED = {
    "Harmonia.Theorems.Quorum",
    "HarmoniaTests.QuorumTest",
    "HarmoniaTests.QuorumAxiomAudit",
}
REJECTION = "HarmoniaTests.QuorumRejection"
TARGETS = ("quorumTest", "quorumAudit", "quorumAuditRejection")
ROOTS = {
    "quorumTest": {"HarmoniaTests.QuorumTest"},
    "quorumAudit": {"HarmoniaTests.AuditPolicy", "HarmoniaTests.QuorumAxiomAudit"},
    "quorumAuditRejection": {REJECTION},
}
FORBIDDEN = re.compile(r"\b(sorry|admit|sorryAx|axiom|native_decide)\b")


def check() -> str:
    lakefile = (ROOT / "lakefile.lean").read_text()
    for target in TARGETS:
        match = re.search(
            rf"(?m)^lean_lib {target} where\s+roots := #\[(.*?)\]",
            lakefile, re.S,
        )
        if not match:
            raise ValueError(f"missing Lake target: {target}")
        roots = set(re.findall(r"`([A-Za-z_][\w.]*)", match.group(1)))
        if roots != ROOTS[target]:
            raise ValueError(f"incorrect roots for {target}: {sorted(roots)}")

    for module in CERTIFIED:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        token = FORBIDDEN.search(scrub(source))
        if token:
            raise ValueError(f"forbidden certified source token {token.group(1)} in {module}")
    product_imports = re.findall(r"(?m)^import\s+([^\s]+)",
                                 (ROOT / "Harmonia/Theorems/Quorum.lean").read_text())
    if product_imports != ["Init"]:
        raise ValueError(f"quorum theorem module must import only Init: {product_imports}")
    policy = scrub((ROOT / "HarmoniaTests/AuditPolicy.lean").read_text())
    manifest = re.search(r"\bdef quorumSourceModules : Array Name := #\[(.*?)\]", policy, re.S)
    if not manifest:
        raise ValueError("missing quorum axiom audit source manifest")
    modules = set(re.findall(r"`([A-Za-z_][\w.]*)", manifest.group(1)))
    if modules != CERTIFIED:
        raise ValueError(f"incorrect quorum audit source manifest: {sorted(modules)}")

    audit_closure = import_closure(ROOT, "HarmoniaTests.QuorumAxiomAudit")
    test_closure = import_closure(ROOT, "HarmoniaTests.QuorumTest")
    if not CERTIFIED <= audit_closure:
        raise ValueError(f"uncovered certified modules: {sorted(CERTIFIED - audit_closure)}")
    if REJECTION in audit_closure | test_closure:
        raise ValueError("counterexample fixture imported by certified target")
    rejection_closure = import_closure(ROOT, REJECTION)
    if REJECTION not in rejection_closure:
        raise ValueError("counterexample fixture missing from rejection closure")

    result = subprocess.run(
        ["lake", "build", *TARGETS], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    output = result.stdout
    if result.returncode:
        raise ValueError(f"Lake build failed ({result.returncode}):\n{output}")
    if "warning:" in output or "error:" in output:
        raise ValueError(f"Lake emitted diagnostics:\n{output}")
    if "QUORUM AUDIT PASS:" not in output:
        # Lake may reuse a completed target without printing its info messages.
        direct = subprocess.run(
            ["lake", "env", "lean", "HarmoniaTests/QuorumAxiomAudit.lean"],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False,
        )
        output = direct.stdout
        if direct.returncode or "QUORUM AUDIT PASS:" not in output:
            raise ValueError(f"quorum axiom audit did not pass:\n{output}")
    if "sorryAx" in output or "warning:" in output or "error:" in output:
        raise ValueError(f"audit output contains forbidden diagnostics:\n{output}")
    summary = re.search(r"QUORUM AUDIT PASS:.*?whitelist \[propext, Quot.sound, Classical.choice\]", output, re.S)
    if not summary:
        raise ValueError(f"missing quorum audit summary:\n{output}")
    observed = re.search(r"observed axioms \[(.*?)\]; whitelist", summary.group(), re.S)
    names = {part.strip() for part in observed.group(1).split(",")} if observed else set()
    if names != {"propext", "Quot.sound"}:
        raise ValueError(f"unexpected axiom dependencies: {sorted(names)}")
    return f"QUORUM CHECK PASS: {summary.group().replace(chr(10), ' ')}"


if __name__ == "__main__":
    try:
        print(check())
    except (OSError, ValueError) as exc:
        print(f"QUORUM CHECK REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1)

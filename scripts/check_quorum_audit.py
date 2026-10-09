#!/usr/bin/env python3
"""Build and inspect the certified quorum audit and its isolated counterexamples."""

import argparse
import re
import subprocess
import sys
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
from check_distributed_audit import import_closure, module_name, scrub


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


def name_array(body: str, label: str) -> set[str]:
    names = re.findall(r"`([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)", body)
    residue = re.sub(r"`[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", "", body)
    if re.sub(r"[\s,]", "", residue):
        raise ValueError(f"malformed {label}")
    if len(names) != len(set(names)):
        raise ValueError(f"duplicate {label}")
    return set(names)


def check_static(root: Path) -> None:
    root = root.resolve()
    lakefile = (root / "lakefile.lean").read_text()
    for target in TARGETS:
        match = re.search(
            rf"(?m)^lean_lib {target} where\s+roots := #\[(.*?)\]",
            lakefile, re.S,
        )
        if not match:
            raise ValueError(f"missing Lake target: {target}")
        roots = name_array(match.group(1), f"{target} roots")
        if roots != ROOTS[target]:
            raise ValueError(f"incorrect roots for {target}: {sorted(roots)}")

    products = set((root / "Harmonia/Theorems").rglob("*.lean"))
    probes = {path for path in (root / "HarmoniaTests").rglob("*.lean")
              if path.relative_to(root / "HarmoniaTests").parts[0].startswith("Quorum")}
    inventory = {module_name(root, path) for path in products | probes}
    inventory = {name for name in inventory
                 if name != REJECTION and not name.startswith(REJECTION + ".")}
    if not CERTIFIED <= inventory:
        raise ValueError(f"missing certified quorum modules: {sorted(CERTIFIED - inventory)}")
    for module in inventory:
        source = (root / (module.replace(".", "/") + ".lean")).read_text()
        token = FORBIDDEN.search(scrub(source))
        if token:
            raise ValueError(f"forbidden certified source token {token.group(1)} in {module}")
    for path in products:
        imports = re.findall(r"(?m)^import\s+([^\s]+)", path.read_text())
        if any(not (name == "Init" or name.startswith("Init.") or
                    name.startswith("Harmonia.Theorems.")) for name in imports):
            raise ValueError(f"nonstandard theorem import in {module_name(root, path)}: {imports}")
    policy = scrub((root / "HarmoniaTests/AuditPolicy.lean").read_text())
    manifest = re.search(r"\bdef quorumSourceModules : Array Name := #\[(.*?)\]", policy, re.S)
    if not manifest:
        raise ValueError("missing quorum axiom audit source manifest")
    modules = name_array(manifest.group(1), "quorum manifest")
    if modules != inventory:
        raise ValueError(f"quorum manifest mismatch: missing={sorted(inventory - modules)}, extra={sorted(modules - inventory)}")

    audit_closure = import_closure(root, "HarmoniaTests.QuorumAxiomAudit")
    test_closure = import_closure(root, "HarmoniaTests.QuorumTest")
    if not inventory <= audit_closure:
        raise ValueError(f"uncovered certified modules: {sorted(inventory - audit_closure)}")
    if REJECTION in audit_closure | test_closure:
        raise ValueError("counterexample fixture imported by certified target")
    project_closure = {name for name in audit_closure | test_closure
                       if name.startswith(("Harmonia.", "HarmoniaTests."))}
    unexpected = project_closure - inventory - {"HarmoniaTests.AuditPolicy"}
    if unexpected:
        raise ValueError(f"unknown certified import: {sorted(unexpected)}")
    rejection_closure = import_closure(root, REJECTION)
    if REJECTION not in rejection_closure:
        raise ValueError("counterexample fixture missing from rejection closure")


def check() -> str:
    check_static(ROOT)

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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        import test_quorum_audit
        suite = unittest.defaultTestLoader.loadTestsFromModule(test_quorum_audit)
        raise SystemExit(0 if unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful() else 1)
    try:
        print(check())
    except (OSError, ValueError) as exc:
        print(f"QUORUM CHECK REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1)

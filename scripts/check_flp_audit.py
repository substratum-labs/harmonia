#!/usr/bin/env python3
"""Build and inspect the certified FLP theorem, audit, and isolated probes."""

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
    "Harmonia.Theorems.FLP",
    "Harmonia.Theorems.FLPInitial",
    "Harmonia.Theorems.FLPIndistinguishability",
    "Harmonia.Theorems.FLPExtension",
    "Harmonia.Theorems.FLPBounds",
    "HarmoniaTests.FLPTest",
    "HarmoniaTests.FLPAxiomAudit",
}
REJECTION = "HarmoniaTests.FLPRejection"
ROOTS = {
    "flpTest": {"HarmoniaTests.FLPTest"},
    "flpAudit": {"HarmoniaTests.AuditPolicy", "HarmoniaTests.FLPAxiomAudit"},
    "flpAuditRejection": {REJECTION},
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
    for target, expected in ROOTS.items():
        match = re.search(
            rf"(?m)^lean_lib {target} where\s+roots := #\[(.*?)\]", lakefile, re.S
        )
        if not match:
            raise ValueError(f"missing Lake target: {target}")
        actual = name_array(match.group(1), f"{target} roots")
        if actual != expected:
            raise ValueError(f"incorrect roots for {target}: {sorted(actual)}")

    theorem_files = set((root / "Harmonia/Theorems/FLP").rglob("*.lean"))
    theorem_files.update((root / "Harmonia/Theorems").glob("FLP*.lean"))
    probe_files = {p for p in (root / "HarmoniaTests").rglob("*.lean")
                   if p.relative_to(root / "HarmoniaTests").parts[0].startswith("FLP")}
    inventory = {module_name(root, p) for p in theorem_files | probe_files}
    inventory = {m for m in inventory if m != REJECTION and not m.startswith(REJECTION + ".")}
    if not CERTIFIED <= inventory:
        raise ValueError(f"missing certified FLP modules: {sorted(CERTIFIED - inventory)}")
    for module in inventory:
        source = (root / (module.replace(".", "/") + ".lean")).read_text()
        token = FORBIDDEN.search(scrub(source))
        if token:
            raise ValueError(f"forbidden certified source token {token.group(1)} in {module}")
    for path in theorem_files:
        imports = re.findall(r"(?m)^import\s+([^\s]+)", path.read_text())
        if any(name not in {"Init", "Harmonia.Core.Execution"} and
               not name.startswith("Init.") and
               not name.startswith("Harmonia.Theorems.FLP") for name in imports):
            raise ValueError(f"nonstandard FLP theorem import in {module_name(root, path)}")

    policy = scrub((root / "HarmoniaTests/AuditPolicy.lean").read_text())
    match = re.search(r"\bdef flpSourceModules : Array Name := #\[(.*?)\]", policy, re.S)
    if not match:
        raise ValueError("missing FLP axiom audit source manifest")
    manifest = name_array(match.group(1), "FLP manifest")
    if manifest != inventory:
        raise ValueError(f"FLP manifest mismatch: missing={sorted(inventory - manifest)}, extra={sorted(manifest - inventory)}")

    audit_closure = import_closure(root, "HarmoniaTests.FLPAxiomAudit")
    test_closure = import_closure(root, "HarmoniaTests.FLPTest")
    if not inventory <= audit_closure:
        raise ValueError(f"uncovered certified FLP modules: {sorted(inventory - audit_closure)}")
    if REJECTION in audit_closure | test_closure:
        raise ValueError("counterexample fixture imported by certified target")
    project_closure = {m for m in audit_closure | test_closure
                       if m.startswith(("Harmonia.", "HarmoniaTests."))}
    expected = inventory | {"HarmoniaTests.AuditPolicy", "Harmonia.Core.TransitionSystem",
                            "Harmonia.Core.Execution"}
    unexpected = project_closure - expected
    if unexpected:
        raise ValueError(f"unknown certified import: {sorted(unexpected)}")
    if REJECTION not in import_closure(root, REJECTION):
        raise ValueError("counterexample fixture missing from rejection closure")


def check() -> str:
    check_static(ROOT)
    result = subprocess.run(["lake", "build", *ROOTS], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
    output = result.stdout
    if result.returncode or "warning:" in output or "error:" in output:
        raise ValueError(f"Lake build failed or emitted diagnostics:\n{output}")
    if "FLP AUDIT PASS:" not in output:
        result = subprocess.run(["lake", "env", "lean", "HarmoniaTests/FLPAxiomAudit.lean"],
                                cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
        output = result.stdout
        if result.returncode:
            raise ValueError(f"FLP axiom audit failed:\n{output}")
    match = re.search(r"FLP AUDIT PASS:.*?observed axioms \[(.*?)\]; whitelist \[propext, Quot.sound\]", output, re.S)
    if not match or "sorryAx" in output or "warning:" in output or "error:" in output:
        raise ValueError(f"missing or tainted FLP audit summary:\n{output}")
    observed = {part.strip() for part in match.group(1).split(",") if part.strip()}
    if not observed <= {"propext", "Quot.sound"}:
        raise ValueError(f"unexpected FLP axiom dependencies: {sorted(observed)}")
    return f"FLP CHECK PASS: {match.group().replace(chr(10), ' ')}"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        import test_flp_audit
        suite = unittest.defaultTestLoader.loadTestsFromModule(test_flp_audit)
        ok = unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful()
        raise SystemExit(0 if ok else 1)
    try:
        print(check())
    except (OSError, ValueError) as exc:
        print(f"FLP CHECK REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1)

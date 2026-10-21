#!/usr/bin/env python3
"""Check the finite causal-clock model, certified source, and Lean axiom audit."""

import hashlib
import re
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from check_distributed_audit import import_closure, module_name, scrub

ROOT = Path(__file__).resolve().parents[1]
CERTIFIED = {
    "Harmonia.Theorems.Causal", "Harmonia.Theorems.Lamport",
    "Harmonia.Theorems.VectorClock", "HarmoniaTests.CausalTest",
    "HarmoniaTests.CausalAxiomAudit",
}
REJECTION = "HarmoniaTests.CausalRejection"
ROOTS = {
    "causalTest": {"HarmoniaTests.CausalTest"},
    "causalAudit": {"HarmoniaTests.AuditPolicy", "HarmoniaTests.CausalAxiomAudit"},
    "causalAuditRejection": {REJECTION},
}
FORBIDDEN = re.compile(r"\b(sorry|admit|sorryAx|unsafe|axiom|native_decide)\b|Classical\s*\.\s*choice|\bchoice\b")


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
        match = re.search(rf"(?m)^lean_lib {target} where\s+roots := #\[(.*?)\]", lakefile, re.S)
        if not match or name_array(match.group(1), f"{target} roots") != expected:
            raise ValueError(f"incorrect or missing Lake target: {target}")

    inventory = {module_name(root, path) for path in
                 (root / "Harmonia/Theorems").rglob("*.lean")
                 if path.relative_to(root / "Harmonia/Theorems").parts[0].split(".")[0]
                 in {"Causal", "Lamport", "VectorClock"}}
    inventory |= {module_name(root, path) for path in
                  (root / "HarmoniaTests").rglob("*.lean")
                  if path.relative_to(root / "HarmoniaTests").parts[0].startswith("Causal")
                  and module_name(root, path) != REJECTION}
    if inventory != CERTIFIED:
        raise ValueError(f"causal inventory mismatch: {sorted(inventory ^ CERTIFIED)}")
    for module in inventory:
        source = (root / (module.replace(".", "/") + ".lean")).read_text()
        hit = FORBIDDEN.search(scrub(source))
        if hit:
            raise ValueError(f"forbidden certified source token {hit.group()} in {module}")
    for module in inventory:
        if not module.startswith("Harmonia.Theorems."):
            continue
        source = (root / (module.replace(".", "/") + ".lean")).read_text()
        imports = [name for line in re.findall(r"(?m)^import[ \t]+(.+)$", source)
                   for name in line.split()]
        if any(not (name == "Init" or name.startswith("Init.") or
                    name in {"Harmonia.Theorems.Causal", "Harmonia.Theorems.Lamport",
                             "Harmonia.Theorems.VectorClock"}) for name in imports):
            raise ValueError(f"nonstandard causal import in {module}: {imports}")
    workflow = (root / ".github/workflows/foundations.yml").read_text()
    if ("lake build causalTest causalAudit causalAuditRejection" not in workflow or
        "python3 scripts/test_causal_audit.py && python3 scripts/check_causal_audit.py" not in workflow):
        raise ValueError("causal CI gate missing")
    policy = scrub((root / "HarmoniaTests/AuditPolicy.lean").read_text())
    manifest = re.search(r"\bdef causalSourceModules : Array Name := #\[(.*?)\]", policy, re.S)
    if not manifest or name_array(manifest.group(1), "causal manifest") != inventory:
        raise ValueError("causal manifest mismatch")
    checker = re.search(r"\bdef checkCausalDeclaration\b(.*?)\bdef auditCausal\b", policy, re.S)
    if not checker or not re.search(
        r"unless ax == ``propext \|\| ax == ``Quot\.sound do", checker.group(1)
    ) or "Classical.choice" in checker.group(1):
        raise ValueError("causal whitelist must be exactly [propext, Quot.sound]")
    causal_audit = re.search(r"\bdef auditCausal\b(.*?)\bend HarmoniaAudit", policy, re.S)
    if not causal_audit or "info.isUnsafe && range.isSome" not in causal_audit.group(1) or "#audit_causal" not in (root / "HarmoniaTests/AuditPolicy.lean").read_text():
        raise ValueError("causal unsafe or command policy missing")
    # Pin the full causal auditor body: a dead whitelist line must not let
    # a widened checker or skipped declaration scan pass static review.
    causal_contract = re.sub(r"\s+", " ", policy[policy.index("def causalSourceModules"):]).strip()
    digest = hashlib.sha256(causal_contract.encode()).hexdigest()
    if digest != "9dfa0be6df0e27d37cb4a8a442860d89985eca6e6fdb19aea01c098924a3790a":
        raise ValueError("causal audit policy body changed")
    audit_closure = import_closure(root, "HarmoniaTests.CausalAxiomAudit")
    test_closure = import_closure(root, "HarmoniaTests.CausalTest")
    if not inventory <= audit_closure:
        raise ValueError(f"uncovered causal modules: {sorted(inventory - audit_closure)}")
    if REJECTION in audit_closure | test_closure:
        raise ValueError("causal rejection fixture imported by certified target")
    project_closure = {name for name in audit_closure | test_closure
                       if name.startswith(("Harmonia.", "HarmoniaTests."))}
    if project_closure - inventory - {"HarmoniaTests.AuditPolicy"}:
        raise ValueError("unknown certified causal import")
    if REJECTION not in import_closure(root, REJECTION):
        raise ValueError("causal rejection fixture missing")


def check() -> str:
    check_static(ROOT)
    build = subprocess.run(["lake", "build", *ROOTS], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if build.returncode or "warning:" in build.stdout or "error:" in build.stdout:
        raise ValueError(f"causal build failed:\n{build.stdout}")
    direct = subprocess.run(["lake", "env", "lean", "HarmoniaTests/CausalAxiomAudit.lean"],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    output = direct.stdout
    if direct.returncode or "warning:" in output or "error:" in output or "sorryAx" in output:
        raise ValueError(f"causal axiom audit failed:\n{output}")
    summary = re.search(r"CAUSAL AUDIT PASS:.*?observed axioms \[(.*?)\]; whitelist \[propext, Quot.sound\]", output, re.S)
    if not summary:
        raise ValueError(f"missing causal audit summary:\n{output}")
    observed = {part.strip() for part in summary.group(1).split(",") if part.strip()}
    if not observed <= {"propext", "Quot.sound"}:
        raise ValueError(f"unexpected causal axioms: {sorted(observed)}")
    return summary.group(0).replace("\n", " ")


if __name__ == "__main__":
    try:
        print(check())
    except (OSError, ValueError) as exc:
        print(f"CAUSAL CHECK REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1)

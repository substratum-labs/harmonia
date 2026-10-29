#!/usr/bin/env python3
"""Build an isolated, cache-free Harmonia copy and a local downstream consumer."""

import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = (
    "Harmonia.Foundation.ForwardSimulation.transfer_invariant",
    "Harmonia.Distributed.provenance_history",
    "Harmonia.Quorum.cft_intersection",
    "Harmonia.Quorum.cft_intersection_at_least",
    "Harmonia.CAP.cap_impossibility",
    "Harmonia.FLP.flp_impossibility",
    "Harmonia.Causal.Vector.Canonical.iff_happensBefore",
    "Harmonia.VerifiedProtocols.QuorumLease.quorum_lease_mutual_exclusion",
    "Harmonia.VerifiedProtocols.QuorumLease.fenced_commit_safety",
    "Harmonia.VerifiedProtocols.QuorumLease.quorum_lease_refines_spec",
    "Harmonia.VerifiedProtocols.TwoPhaseCommit.twoPC_atomic_agreement",
    "Harmonia.VerifiedProtocols.TwoPhaseCommit.twoPC_commit_validity",
    "Harmonia.VerifiedProtocols.TwoPhaseCommit.twoPC_refines_spec",
    "Harmonia.VerifiedProtocols.BFTQuorumCommit.bft_qc_unique",
    "Harmonia.VerifiedProtocols.BFTQuorumCommit.bft_commit_safety",
    "Harmonia.VerifiedProtocols.BFTQuorumCommit.bft_commit_refines_spec",

)
ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def run(command: list[str], cwd: Path) -> tuple[str, float]:
    start = time.perf_counter()
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    seconds = time.perf_counter() - start
    if result.returncode or re.search(r"\b(?:warning|error):", result.stdout):
        raise ValueError(f"{' '.join(command)} failed or emitted diagnostics:\n{result.stdout}")
    return result.stdout, seconds


def check_axioms(output: str) -> set[str]:
    observed: set[str] = set()
    for theorem in THEOREMS:
        pattern = re.escape("'" + theorem + "'") + (
            r" (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
        )
        reports = list(re.finditer(pattern, output))
        if len(reports) != 1:
            raise ValueError(f"expected one axiom report for {theorem}:\n{output}")
        axioms = {name.strip() for name in (reports[0].group(1) or "").split(",")
                  if name.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise ValueError(f"unexpected axioms for {theorem}: {sorted(axioms)}")
        observed |= axioms
    return observed


def check() -> dict:
    with tempfile.TemporaryDirectory(prefix="harmonia-external-") as temporary:
        base = Path(temporary)
        library = base / "harmonia"
        # Never clean the source worktree or reuse its compiled artifacts.
        shutil.copytree(ROOT, library, ignore=shutil.ignore_patterns(
            ".lake", ".git", "__pycache__", ".pytest_cache", "*.pyc"))
        if (library / ".lake").exists():
            raise ValueError("clean copy unexpectedly contains a Lake cache")
        _, clean_seconds = run(["lake", "build", "Harmonia"], library)
        consumer = base / "consumer"
        consumer.mkdir()
        shutil.copyfile(ROOT / "lean-toolchain", consumer / "lean-toolchain")
        # JSON strings are also valid Lean string literals for these paths.
        (consumer / "lakefile.lean").write_text(
            'import Lake\nopen Lake DSL\npackage consumer\n'
            f'require harmonia from {json.dumps(str(library))}\n'
            '@[default_target]\nlean_lib ConsumerSmoke\n')
        (consumer / "ConsumerSmoke.lean").write_text(
            "import Harmonia\n\n" + "\n".join(
                f"#check {name}\n#print axioms {name}" for name in THEOREMS) + "\n")
        run(["lake", "update"], consumer)
        _, consumer_seconds = run(["lake", "build"], consumer)
        # Force fresh elaboration: an up-to-date Lake build need not print reports.
        output, _ = run(["lake", "env", "lean", "ConsumerSmoke.lean"], consumer)
        observed = check_axioms(output)
        return {
            "clean_library_build_seconds": round(clean_seconds, 3),
            "consumer_build_seconds": round(consumer_seconds, 3),
            "theorems_checked": len(THEOREMS),
            "observed_axioms": sorted(observed),
            "whitelist": sorted(ALLOWED_AXIOMS),
            "warnings": 0, "errors": 0,
        }


if __name__ == "__main__":
    try:
        print("EXTERNAL CONSUMER PASS: " + json.dumps(check(), sort_keys=True))
    except (OSError, ValueError) as exc:
        print(f"EXTERNAL CONSUMER REJECTED: {exc}", file=sys.stderr)
        raise SystemExit(1)

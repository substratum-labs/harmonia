#!/usr/bin/env python3
"""Validate or normalize the Init-only Balance invariant source certificate.

Structural validation is a maintenance check. `lake build` must still elaborate
and kernel-check the expanded proof, followed by the strict Generated audit.
Normalization accepts a checked export; it preserves computational syntax and
only retargets model names and replaces diagnostic trace commands with `skip`.
"""
import argparse
import ast
import json
from pathlib import Path
import re
import sys

DEFAULT = Path(__file__).resolve().parents[1] / (
    "Harmonia/Applications/Kadmos/Generated/BalanceInvariantCertificate.lean")
NAME_PREFIX = "private def certificateNameRows : String := "
ROW_PREFIX = "private def certificateRows : String := "
TRACE = "|sLean|sParser|sTactic|straceMessage"
SKIP = "|sLean|sParser|sTactic|sskip"
NAMESPACE = "Harmonia.Applications.Kadmos.Generated.BalanceInvariantCertificate"
RENAMES = {
    "ownerCodeName": "balanceSourceCodeName",
    "ownerCodeJoin": "balanceSourceCodeJoin",
    "ownerFindStmtBody": "balanceSourceStmtBody",
    "ownerFindFunctionBody": "balanceSourceFunctionBody",
    "ownerSourceBody": "balanceSourceBody",
    **{"ownerPyLiteral" + suffix: "balanceInvariantPy" + suffix
       for suffix in ("Input", "InputFrame", "Final", "Bound", "Reset", "Copied")},
}
MODULE_DOC = '''/-! Source certificate for the emitted Python Balance invariant call.

This Init-only syntax DAG expands to ordinary kernel-checked proof steps. It
contains no evaluator, target execution definition, or trusted external result.
Names use `s`/`n` components; rows encode syntax nodes, identifiers, atoms, and
six caller-supplied terms. Each node refers only to earlier nodes. Diagnostic
trace commands from the checked export are replaced by `skip`.

The caller supplies the symbolic balance, its safe-integer bound, and the
constructive numeric facts. The expanded proof executes the actual source
method at fuel 74; normal elaboration and the strict application audit validate
it on every build. The source semantics and canonical heap models remain in
the application modules.
-/
'''


def literal(source, prefix):
    lines = [line[len(prefix):] for line in source.splitlines()
             if line.startswith(prefix)]
    if len(lines) != 1:
        raise ValueError(f"expected one {prefix!r} declaration")
    value = ast.literal_eval(lines[0])
    if not isinstance(value, str):
        raise ValueError("certificate table must be a literal string")
    return value, lines[0]


def natural(value):
    if not re.fullmatch(r"[0-9]+", value):
        raise ValueError("expected an ASCII natural-number index")
    return int(value)


def read(source):
    if re.findall(r"^import .*", source, re.M) != ["import Init"]:
        raise ValueError("expected exactly import Init")
    names = literal(source, NAME_PREFIX)[0].split("\n")
    rows = literal(source, ROW_PREFIX)[0].split("\n")
    roots = re.findall(r"return nodes\[(\d+)\]!", source)
    if len(roots) != 1 or not 0 <= int(roots[0]) < len(rows):
        raise ValueError("invalid or ambiguous root")
    for name in names:
        if name and (not name.startswith("|") or any(
                not part or part[0] not in "sn" or
                (part[0] == "n" and not re.fullmatch(r"[0-9]+", part[1:]))
                for part in name.split("|")[1:])):
            raise ValueError(f"malformed name: {name!r}")
    for index, row in enumerate(rows):
        try:
            if row.startswith("n"):
                kind, children = row[1:].split(":")
                if not 0 <= natural(kind) < len(names):
                    raise ValueError("kind index outside name table")
                child_indices = [] if children == "" else children.split(",")
                if any(not 0 <= natural(child) < index for child in child_indices):
                    raise ValueError("child must precede parent")
            elif row.startswith("i"):
                if not 0 <= natural(row[1:]) < len(names):
                    raise ValueError("identifier index outside name table")
            elif row.startswith("p"):
                if not 0 <= natural(row[1:]) < 6:
                    raise ValueError("parameter index outside six inputs")
            elif not (row.startswith("a") or row == "m"):
                raise ValueError("unknown row encoding")
        except ValueError as error:
            raise ValueError(f"row {index}: {error}") from error
    return names, rows, int(roots[0])


def normalize(source):
    names, rows, root = read(source)
    new_names, new_rows, name_ids, row_ids, memo = [], [], {}, {}, {}
    traces = 0

    def name_id(name):
        if name.startswith("|sCertificateProof|"):
            name = "".join("|s" + part for part in NAMESPACE.split(".")) + (
                name[len("|sCertificateProof"):])
        name = "|".join("s" + RENAMES.get(part[1:], part[1:])
                        if part.startswith("s") else part
                        for part in name.split("|"))
        if name not in name_ids:
            name_ids[name] = len(new_names)
            new_names.append(name)
        return name_ids[name]

    def intern(row):
        if row not in row_ids:
            row_ids[row] = len(new_rows)
            new_rows.append(row)
        return row_ids[row]

    def visit(index):
        nonlocal traces
        if index in memo:
            return memo[index]
        row = rows[index]
        if row.startswith("n"):
            kind, children = row[1:].split(":")
            kind = names[int(kind)]
            if kind == TRACE:
                traces += 1
                result = intern(f"n{name_id(SKIP)}:{intern('askip')}")
            else:
                args = [visit(int(child)) for child in children.split(",") if child]
                result = intern(f"n{name_id(kind)}:" + ",".join(map(str, args)))
        elif row.startswith("i"):
            result = intern(f"i{name_id(names[int(row[1:])])}")
        else:
            result = intern(row)
        memo[index] = result
        return result

    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
    new_root = visit(root)
    for prefix, value in ((NAME_PREFIX, "\n".join(new_names)),
                          (ROW_PREFIX, "\n".join(new_rows))):
        source = source.replace(prefix + literal(source, prefix)[1],
                                prefix + json.dumps(value, ensure_ascii=False))
    source = source.replace(f"return nodes[{root}]!", f"return nodes[{new_root}]!")
    source = source.replace("namespace CertificateProof", "namespace " + NAMESPACE)
    source = source.replace("end CertificateProof", "end " + NAMESPACE)
    if 'macro "certificate_proof"' in source:
        source = source.replace('macro "certificate_proof"',
                                'macro "balance_python_invariant_certificate"')
        source = source.replace(
            ': term => return ⟨certificateSyntax (ps.getElems.map (·.raw))⟩',
            ': term => do\n  unless ps.getElems.size == 6 do\n'
            '    Macro.throwError "expected n, bound, absolute bound, float, zero, '
            'and comparison proofs"\n'
            '  return ⟨certificateSyntax (ps.getElems.map (·.raw))⟩')
    if MODULE_DOC not in source:
        source = source.replace("import Init\n", "import Init\n\n" + MODULE_DOC + "\n", 1)
    read(source)
    return source, traces


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", nargs="?", type=Path, const=DEFAULT)
    mode.add_argument("--normalize", type=Path, metavar="CHECKED_EXPORT")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.check:
        if args.output:
            parser.error("--output requires --normalize")
        names, rows, root = read(args.check.read_text())
        print(f"BALANCE CERTIFICATE STRUCTURE PASS: {len(names)} names; "
              f"{len(rows)} topological rows; root {root}; six parameter slots")
    else:
        if not args.output:
            parser.error("--normalize requires --output")
        output, traces = normalize(args.normalize.read_text())
        args.output.write_text(output)
        print(f"Normalized certificate; {traces} unique diagnostic traces replaced")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, SyntaxError, OSError, RecursionError) as error:
        print(f"BALANCE CERTIFICATE STRUCTURE FAIL: {error}", file=sys.stderr)
        sys.exit(1)

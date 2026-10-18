# Canonical DEBIT certificate packaging

These Python standard-library tools reproduce the bounded private-definition
families used by the Python canonical DEBIT proofs. The pinned input is a
serialized Lean syntax DAG. Packaging preserves its syntax, closes each
private definition over its required root parameters, and preserves explicit
application arguments. The generated syntax decoder uses Init only.

Python structural checks establish syntax preservation. Ordinary Lean kernel
checking of the generated module establishes the theorem. Generation alone
is not proof acceptance.

From the repository root, reproduce the prefix without changing the checked
source (choose a scratch output path):

```sh
python3 scripts/balance_step_certificates/emit_private_certificate.py \
  --certificate scripts/balance_step_certificates/prefix.input.lean \
  --schema scripts/balance_step_certificates/prefix-schema.json \
  --template scripts/balance_step_certificates/prefix-template.lean.in \
  --output /tmp/ReproducedPrefix.lean
cmp /tmp/ReproducedPrefix.lean Harmonia/Applications/Kadmos/Generated/BalanceStepPythonPrefix.lean
python3 scripts/balance_step_certificates/verify_certificate_roundtrip.py \
  --certificate scripts/balance_step_certificates/prefix.input.lean \
  --schema scripts/balance_step_certificates/prefix-schema.json \
  --output /tmp/prefix-roundtrip.json
```

The schema pins the original input SHA-256, exact root parameter types and
their dependencies, and unique macro/helper names. Templates contain product
imports, theorem statements and witness proofs; the certificate data retains
original project/Init constant names. The emitter writes a hash manifest next
to its output. Paths supplied to the CLI are explicit; no scratch workspace
is required by the tools or generated product imports.

Run the portable packaging mutation tests and byte-exact checks for every
configured product certificate:

```sh
python3 scripts/balance_step_certificates/test_certificate_packaging.py
python3 scripts/balance_step_certificates/check_certificates.py
```

`certificates.json` records each product module and its encoding option.
The raw prefix and guard retain literal names. A kind-only encoding interns
parser syntax kinds while retaining exact identifier names; it uses
`--intern-kinds`. This encoding must still pass the full ordinary kernel check.

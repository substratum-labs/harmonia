#!/usr/bin/env bash
set -euo pipefail

# Build the Lean project
lake build

LEAN_TOOLCHAIN="${LEAN_TOOLCHAIN:-/Users/yong/.elan/toolchains/leanprover--lean4---v4.16.0}"

echo "Compiling C initialization shim..."
clang -c -O3 -o .lake/build/ir/Harmonia/Gatekeeper/shim.o Harmonia/Gatekeeper/shim.c

echo "Linking libharmonia_gatekeeper.dylib..."
mkdir -p .lake/build/lib
clang -dynamiclib -o .lake/build/lib/libharmonia_gatekeeper.dylib \
  -install_name @rpath/libharmonia_gatekeeper.dylib \
  .lake/build/ir/Harmonia/Gatekeeper/shim.o \
  .lake/build/ir/Harmonia/Gatekeeper/CExport.c.o.export \
  -L "${LEAN_TOOLCHAIN}/lib/lean" \
  -L "${LEAN_TOOLCHAIN}/lib" \
  -L /opt/homebrew/lib \
  -lleancpp -lInit -lleanrt -lc++ -lgmp -luv

codesign -s - -f .lake/build/lib/libharmonia_gatekeeper.dylib

echo "✓ Successfully built .lake/build/lib/libharmonia_gatekeeper.dylib"

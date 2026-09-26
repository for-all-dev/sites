#!/usr/bin/env bash
# Full verification run: escape-hatch audit, build, tests, independent kernel re-check.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== escape-hatch audit"
# Strip line comments and block comments, then look for the banned keywords in code.
banned='partial def|partial instance|noncomputable|unsafe|implemented_by|native_decide|sorry|^axiom |opaque'
if find Sites Example -name '*.lean' -print0 | xargs -0 cat Main.lean Test.lean Sites.lean Example.lean \
    | sed -e 's/--.*$//' \
    | awk 'BEGIN{skip=0} /\/-/{skip=1} skip==0{print} /-\//{skip=0}' \
    | grep -nE "$banned"; then
  echo "error: banned escape hatch found" >&2
  exit 1
fi
echo "ok: no partial, noncomputable, unsafe, implemented_by, native_decide, sorry, axiom or opaque"

echo "== build"
lake build

echo "== tests and axiom audit"
lake build Test

echo "== independent kernel re-check (leanchecker, from oleans)"
lake env leanchecker Sites Example

echo "all checks passed"

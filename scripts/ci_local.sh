#!/usr/bin/env bash
# Reproduce the CI pipeline locally without touching a root-owned Mathlib.
#
# The workflow in .github/workflows/build.yml clones the pinned Mathlib and fetches its
# prebuilt cache.  Lake needs to *write* next to those objects (hash files), so it cannot
# use a read-only installation.  This script copies the installed Mathlib once into a
# writable directory, points a scratch copy of the project at it as a path dependency,
# and then runs the same three steps the workflow runs.
#
#   scripts/ci_local.sh            # full run
#   scripts/ci_local.sh build      # only the build
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
CONTAINER="$(dirname "$REPO")"
CIROOT="${CIROOT:-$CONTAINER/.ci}"
MATHLIB_SRC="${MATHLIB_SRC:-/opt/mathlib}"
WORK="$CIROOT/work"

mkdir -p "$CIROOT"
if [ ! -d "$CIROOT/mathlib" ]; then
  echo "== copying $MATHLIB_SRC to $CIROOT/mathlib (one off, ~7 GB)"
  cp -a "$(readlink -f "$MATHLIB_SRC")" "$CIROOT/mathlib"
  chmod -R u+w "$CIROOT/mathlib"
fi

rm -rf "$WORK"
mkdir -p "$WORK"
cp -a "$REPO/RelationalAtlas" "$REPO/FalseControls" "$REPO/scripts" "$REPO/lean-toolchain" "$WORK/"
python3 - "$REPO/lakefile.toml" "$WORK/lakefile.toml" <<'PY'
import sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
s = s.replace('git = "https://github.com/leanprover-community/mathlib4.git"', 'path = "../mathlib"')
s = "\n".join(l for l in s.splitlines() if not l.strip().startswith('rev = "v4.35.0"')) + "\n"
open(dst, "w").write(s)
PY

cd "$WORK"
echo "== lake build"
lake build
if [ "${1:-all}" = build ]; then exit 0; fi

echo "== lake env leanchecker (independent kernel replay)"
for m in $(python3 -c "import json;print(' '.join(x['module'] for x in json.load(open('scripts/config.json'))['modules']))"); do
  echo "-- $m"
  lake env leanchecker "$m"
done

echo "== scripts/verify.py (inventory, axiom audit, false controls)"
python3 scripts/verify.py

#!/bin/sh
# Check the five proof modules against the local project and audit the final theorem's axioms.
set -eu
proof=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=${1:-$(git -C "$proof" rev-parse --show-toplevel)}
repo=$(CDPATH= cd -- "$repo" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cd "$repo/lean"
lake build PEqualNP.Defs.TopForm PEqualNP.MetaComplexity.Helpers.PermInputs >/dev/null
if [ -f PEqualNP/Defs/ReadK.lean ]; then
  lake build PEqualNP.Defs.ReadK >/dev/null
else
  # This checkout predates ReadK. Use the verified upstream blob in the project's local Git store.
  rel=PEqualNP/Defs/ReadK
  mkdir -p "$scratch/src/PEqualNP/Defs" "$scratch/PEqualNP/Defs"
  git -C "$repo" cat-file blob 8279c37a8c272dcbbf33b4085344faeab19885bf > "$scratch/src/$rel.lean"
  python3 - "$scratch/PEqualNP" <<'PY'
from pathlib import Path
import sys
root = Path('.lake/build/lib/lean/PEqualNP').resolve()
overlay = Path(sys.argv[1])
for directory in (Path('.'), Path('Defs')):
    for source in (root / directory).iterdir():
        target = overlay / directory / source.name
        if not target.exists():
            target.symlink_to(source)
PY
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -R "$1/src" -o "$1/$2.olean" "$1/src/$2.lean"' sh "$scratch" "$rel"
fi
lake env sh -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for module in FirstGateBound GraphSensitivity Plane256 BipartitePlane Refutation; do
    lean -R "$2" -o "$1/$module.olean" "$2/$module.lean" || exit 1
  done
  echo "import Refutation" > "$1/Audit.lean"
  echo "#print axioms Meta2796.refutation" >> "$1/Audit.lean"
  exec lean "$1/Audit.lean"
' sh "$scratch" "$proof"

#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo=${1:-$(git -C "$project_dir" rev-parse --show-toplevel)}
lean_dir="$repo/lean"
compiled=$(mktemp -d)
trap 'rm -rf "$compiled"' EXIT
cd "$lean_dir"
lake build PEqualNP.MetaComplexity.L649
for module in PinnedNonedge PinCircuit; do
  lake env lean -R "$project_dir" -o "$compiled/$module.olean" "$project_dir/$module.lean"
done
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean "$2"' sh "$compiled" "$project_dir/RangeTwoBound.lean"

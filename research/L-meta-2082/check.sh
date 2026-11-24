#!/bin/sh
# Check the formula results with the project's pinned Lean and Mathlib.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
{
  echo 'import Mathlib'
  for unit in RankSamples PlaneFormulaTree; do
    awk '!/^import /' "$here/../L-meta-2794/$unit.lean"
  done
  for unit in LeafProtocol StarRank StarCount StarFactors PlaneStarFormula; do
    awk '!/^import /' "$here/../L-meta-3364/$unit.lean"
  done
  for unit in TightOwner FormulaDirection TrackedTiles EdgeReadOnce; do
    awk '!/^import /' "$here/$unit.lean"
  done
  echo '#print axioms PlaneFormula.Tree.direction_of_gain'
  echo '#print axioms PlaneStarFormula.edgeReadOnce'
} > "$scratch/Edge.lean"
lake env lean "$scratch/Edge.lean"

#!/bin/sh
# Run from the upstream lean/ directory with its pinned Lake dependencies.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
lake build PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph PEqualNP.MetaComplexity.Helpers.ForestBound \
  PEqualNP.MetaComplexity.L106 PEqualNP.Outside.L_meta_548 PEqualNP.Outside.L_meta_1602
{
  echo 'import Mathlib'
  echo 'import PEqualNP.Defs'
  echo 'import PEqualNP.MetaComplexity.Helpers.CoverCircuitGraph'
  echo 'import PEqualNP.MetaComplexity.Helpers.ForestBound'
  echo 'import PEqualNP.MetaComplexity.L106'
  echo 'import PEqualNP.Outside.L_meta_548'
  echo 'import PEqualNP.Outside.L_meta_1602'
  for unit in HonestCover LeastCases CostEquiv SolvedChildren; do
    awk '!/^import /' "$here/$unit.lean"
  done
  for decl in builder forests cycles characterization solvedForestOrCycle solvedHonestUpper; do
    echo "#print axioms HonestCover1904.$decl"
  done
} > "$scratch/Children.lean"
lake env lean "$scratch/Children.lean"

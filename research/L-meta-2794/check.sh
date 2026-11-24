#!/bin/sh
# Invoke from a Lean project with this repository's pinned Mathlib available.
set -eu
sources=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
{
  echo 'import Mathlib'
  for unit in LiveCone PlaneGeometry PrivateInputs PrivateFanout ConeBound OutputBudget \
    SparseExactness PlaneFormulaTree FormulaRank FormulaPartition RankSamples UnfoldCircuit \
    PathBudget BoundedPaths FullRankFactor PlaneKernel ExactPathBudget
  do
    awk '!/^import /' "$sources/$unit.lean"
  done
  echo '#print axioms PlaneOutputBudget.through299'
  echo '#print axioms PlanePathBudget.pathMass'
  echo '#print axioms PlanePathBudget.bounded100'
  echo '#print axioms PlanePathBudget.boundedAverage100'
} > "$scratch/PlaneBound.lean"
lake env lean "$scratch/PlaneBound.lean"

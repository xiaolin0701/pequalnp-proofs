#!/bin/sh
# Run from the repository’s Lean project, which provides the pinned dependencies.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
plane="$here/../L-meta-2794"
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
{
  echo 'import Mathlib'
  echo 'import PEqualNP.Defs'
  echo 'import PEqualNP.Defs.TopForm'
  for unit in LiveCone PlaneGeometry PrivateInputs PrivateFanout ConeBound OutputBudget \
      SparseExactness PlaneFormulaTree FormulaRank FormulaPartition RankSamples UnfoldCircuit \
      PathBudget BoundedPaths FullRankFactor PlaneKernel ExactPathBudget
  do
    awk '!/^import /' "$plane/$unit.lean"
  done
  awk '!/^import /' "$here/../L-meta-2582/StarProgram.lean"
  for unit in RectangleCost PlaneCover LeafProtocol StarRank StarCount StarFactors PlaneStarFormula \
      StarPathBudget StarWitness OptimalFormula CompressSignals FirstGate FixedInput \
      PinnedExchange PinIndices Plane299
  do
    awk '!/^import /' "$here/$unit.lean"
  done
  echo '#print axioms PlaneStarFormula.minimumLeaves'
  for decl in through298 pathBudget belowAverage100 average100 endpointResidues starPathMass starPathCover \
      markedStarPathMass hasStarPathMass markedStarCover allAverage100 threeTimes through299
  do
    echo "#print axioms PlaneCover3364.$decl"
  done
} > "$scratch/Cover.lean"
lake env lean "$scratch/Cover.lean"

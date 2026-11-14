#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# With a built Mathlib, pass its Lean search path as the first argument.
# With no argument, use the Mathlib dependency in this Lake project.
if [[ $# -gt 1 ]]; then
  echo "Usage: $0 [mathlib-lean-path]" >&2
  exit 2
fi
mathlib_path="${1:-}"
if [[ -z "$mathlib_path" ]]; then
  mathlib_path="$(lake env printenv LEAN_PATH)"
fi
mkdir -p build/Fresh
export LEAN_PATH="$PWD/build:$mathlib_path"

echo "== X24Compute"
lean X24Compute.lean -R . -o build/X24Compute.olean -c build/X24Compute.c
leanc -O3 -DLEAN_EXPORTING -shared -o build/libX24Compute_shared.so build/X24Compute.c

echo "== HarmonicCompute"
lean HarmonicCompute.lean -R . -o build/HarmonicCompute.olean -c build/HarmonicCompute.c
leanc -O3 -DLEAN_EXPORTING -shared -o build/libHarmonicCompute_shared.so build/HarmonicCompute.c

modules=(
  Framework Cascade KTaxonomy Localisation CascadeAnchor CascadeRejection CascadeNeighbours CascadeRadiusGrowth CascadeTwoDeviations CascadeReplacementCell CascadeFourthReading CascadeFifthReading OneMoverA CascadeLanding FrontierFamilyCap
  FilterSkeleton CarveExclusionCerts FilterAssembly SpineSound SpineTotalData
  FilterAssemblyPerBox FilterAssemblyPerBoxV2 PinchCert BandNoCarve BandPinchData
  Grid PathForm Dilation TailFast TailFastLadder TransferChecks
  Dmax GridNearFails ExactCellRestoration FilterShortcuts SymbolicWindow GapSplice GapPairs
  X24Sound X24Total X24Checked X24Theorem
  FiniteRelations FiniteKernels RankFour PhaseFibres CircuitProjection SmallCircuits LowRankFibres
  FourCircleGeometry RankFourTransfer RankLadder HarmonicCutoff
  HarmonicLift HarmonicSlow HarmonicDBM HarmonicArcs HarmonicPhase HarmonicFrontier
  HarmonicChecked HarmonicFrontierChecked HarmonicFrontierVerified HarmonicRates FourCircleComplete FibreMargin
  RationalAnnihilator TorusPolynomial TorusAverage FibreTest ProjectedTest BufferedFast
  BufferedSectors HarmonicFinite LatticeRounding PairedSlow ThreeFast
  ExactFourReduction WindowObstruction SlowFiveReduction UniformPhaseAverage ExactClassicalReduction
  ExplicitFourierKernel BoundedClassicalProfiles
)
for module in "${modules[@]}"; do
  echo "== Fresh.$module"
  if [[ "$module" == X24Checked ]]; then
    lean --plugin="$PWD/build/libX24Compute_shared.so" "Fresh/$module.lean" -R . -o "build/Fresh/$module.olean"
  elif [[ "$module" == HarmonicChecked || "$module" == HarmonicFrontierChecked ]]; then
    lean --plugin="$PWD/build/libHarmonicCompute_shared.so" -DmaxHeartbeats=0 "Fresh/$module.lean" -R . -o "build/Fresh/$module.olean"
  else
    lean "Fresh/$module.lean" -R . -o "build/Fresh/$module.olean"
  fi
done

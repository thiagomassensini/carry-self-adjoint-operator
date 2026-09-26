import CarrySelfAdjointOperator.CompletedNativeIndependentReflectedHolomorphicGreen
import CarrySelfAdjointOperator.BR2CausalTfvdMetricShift
import CarrySelfAdjointOperator.BR2BracketTfvdIncidenceTransport
import CarrySelfAdjointOperator.CompletedC3SymplecticNaimarkLimitBridge
import Mathlib.Tactic

/-!
# Established real bracket readout and its boundary with the holomorphic Green jet

This file records the exact real chain already available for C3 causal
responses: weighted second difference, centered bracket, and the retained
trace metric.  It deliberately stops before an unproved identification with
the camera-resolved holomorphic Green central inner product.

The discrete second difference acts in the carry/depth coordinate.
The complex derivative acts in the spectral height coordinate.
The theorems below do not identify these operators.
They identify their scalar readouts only after the canonical representation
crosswalks that are actually present in the repository.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera

noncomputable section
set_option autoImplicit false

/-! ## Real second-difference / bracket side -/

/-- The scalar carry second difference is the discrete bracket after the
amplitude gauge, with its explicit nonzero carry factor retained.  Its index
`n` is a carry/depth index, not a spectral derivative order. -/
theorem weightedScalarSecondDifference_gauge_eq_bracket
    (q : ℂ) (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarSecondDifference q (carryAmplitudeGauge q x) n =
      q ^ (n + 1) * DiscreteValve.bracket x n := by
  exact carryWeightedScalarSecondDifference_gauge q hq x n

/-- The actual TFVD metric readout of two C3 causal bracket responses.  By
construction it retains both the centered-bracket contribution and the trace
contribution until the C3 trace theorem is applied. -/
def br2C3RealSecondDifferenceBracketReadout
    (q : ℝ) (i j : ℕ) : ℂ :=
  inner ℂ
    (carryTfvdMetricState q (br2CameraBracketCausalGreenResponse q 3 1 i))
    (carryTfvdMetricState q (br2CameraBracketCausalGreenResponse q 3 1 j))

/-- Before C3 trace specialization, the real metric readout is exactly the
centered-bracket inner product plus the explicit trace metric. -/
theorem br2C3RealSecondDifferenceBracketReadout_eq_bracket_add_trace
    (q : ℝ) (i j : ℕ) :
    br2C3RealSecondDifferenceBracketReadout q i j =
      inner ℂ
        (carryWeightedVerticalCenteredBracket q
          (br2CameraBracketCausalGreenResponse q 3 1 i))
        (carryWeightedVerticalCenteredBracket q
          (br2CameraBracketCausalGreenResponse q 3 1 j)) +
      carryTfvdTraceMetric q
        (carryWeightedVerticalTrace q
          (br2CameraBracketCausalGreenResponse q 3 1 i))
        (carryWeightedVerticalTrace q
          (br2CameraBracketCausalGreenResponse q 3 1 j)) := by
  unfold br2C3RealSecondDifferenceBracketReadout
  rw [carryTfvdMetricState_inner,
    carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace]

/-- The explicit trace correction vanishes for the actual base-three,
radius-one causal C3 family. -/
theorem br2C3RealSecondDifferenceBracketReadout_trace_eq_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (i j : ℕ) :
    carryTfvdTraceMetric q
      (carryWeightedVerticalTrace q
        (br2CameraBracketCausalGreenResponse q 3 1 i))
      (carryWeightedVerticalTrace q
        (br2CameraBracketCausalGreenResponse q 3 1 j)) = 0 := by
  rw [br2C3CausalResponse_trace_zero q hq0 hq1 i,
    br2C3CausalResponse_trace_zero q hq0 hq1 j]
  simp [carryTfvdTraceMetric]

/-- After the C3 trace specialization, the real TFVD metric readout is the
centered-bracket scalar readout, without silently dropping the trace term. -/
theorem br2C3RealSecondDifferenceBracketReadout_eq_centeredBracket
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (i j : ℕ) :
    br2C3RealSecondDifferenceBracketReadout q i j =
      inner ℂ
        (carryWeightedVerticalCenteredBracket q
          (br2CameraBracketCausalGreenResponse q 3 1 i))
        (carryWeightedVerticalCenteredBracket q
          (br2CameraBracketCausalGreenResponse q 3 1 j)) := by
  rw [br2C3RealSecondDifferenceBracketReadout_eq_bracket_add_trace,
    br2C3RealSecondDifferenceBracketReadout_trace_eq_zero q hqpos.le hq1]
  simp

/-- The centered bracket of each C3 causal response is exactly its original
vertical bracket incidence state. -/
theorem br2C3RealSecondDifferenceBracketReadout_eq_sourceInner
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (i j : ℕ) :
    br2C3RealSecondDifferenceBracketReadout q i j =
      inner ℂ (br2CameraBracketVerticalState 3 1 i)
        (br2CameraBracketVerticalState 3 1 j) := by
  exact br2C3CausalTfvdMetric_inner_eq_source q hqpos hq1 i j

/-! ## Faithfulness of the available real-to-complex representations -/

/-- Complexifying a real BR2 incidence loses no zero/nonzero information. -/
theorem br2RealIncidenceComplexification_eq_zero_iff
    (incidence : ℕ →₀ ℝ) :
    br2RealIncidenceComplexification incidence = 0 ↔ incidence = 0 := by
  constructor
  · intro hzero
    apply br2RealIncidenceComplexification_injective
    simpa using hzero
  · intro hzero
    simp [hzero]

/-- The finite C3 real-coordinate realization is likewise faithful. -/
theorem finiteC3LegRealCoordinateIsometry_eq_zero_iff
    (M : ℕ) (x : NativeCarryC3Crosswalk.FiniteC3GreenBoundarySpace M) :
    finiteC3LegRealCoordinateIsometry M x = 0 ↔ x = 0 := by
  constructor
  · intro hzero
    apply (finiteC3LegRealCoordinateIsometry M).injective
    simpa using hzero
  · intro hzero
    simp [hzero]

/- ## Boundary of the established crosswalk

The established real readout is indexed by BR2 causal incidence indices
`i,j` and has value
`inner ℂ (br2CameraBracketVerticalState 3 1 i)
          (br2CameraBracketVerticalState 3 1 j)`.

The holomorphic first-jet theorem instead contains
`canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner`,
an inner product between a reconstructed independent-reflected direct source
and a reconstructed reflected source in `FiniteC3GreenBoundarySpace (3*M)`.

The nearby theorem
`canonicalCompletedC3DirichletGradientPrefixState_eq_br2Response_iff` is only
a conditional comparison of a one-parameter Dirichlet prefix with a BR2
response: it still requires the corresponding bracket/source equality.  It
does not identify either source with the independent-reflected `wSource` and
`reflectedZSource` pair above.  Thus no map identifying these two source pairs
is supplied by the imported realification, incidence, TFVD-reconstruction, or
finite-leg-isometry APIs.
Consequently this file proves the real chain and the faithful representation
facts, but intentionally does **not** assert `I(0) = Breal`. -/

end

end CarrySelfAdjointOperator

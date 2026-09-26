import CarrySelfAdjointOperator.CompletedNativeHolomorphicGreenBracketCrosswalk
import CarrySelfAdjointOperator.ProjectiveValveCarryEnergyFrontier
import CarrySelfAdjointOperator.CompletedNativeProductClockQuotientGreenAudit
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets
import CarrySelfAdjointOperator.NativeLogEvolution
import Mathlib.Tactic

/-!
# Holomorphic C3 Green first jet through the full TFVD reconstruction

The discrete second difference belongs to the carry/depth coordinate, while
the holomorphic derivative belongs to the spectral-parameter coordinate.
This file does not identify those operators.  It identifies the scalar readout
of the first holomorphic Green jet with the full reconstructed TFVD pairing:
the Green/bracket and return/trace pieces in both arguments, including the two
cross terms.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open FiniteNativeCarryOperator.Camera

noncomputable section
set_option autoImplicit false

/-! ## Central source legs in the TFVD Hilbert space -/

/-- The C3 carry ratio used by the TFVD reconstruction channels. -/
def canonicalC3TfvdRatio : ℝ :=
  canonicalBR2CarryAmplitudeRatio 3

/-- Zero-extend the finite ordinary direct leg used by the holomorphic first
jet into the common `CarryVerticalL2` TFVD space.  The finite leg has cutoff
`3 * M`; this is an extension of the actual jet leg, not a change of cutoff. -/
def canonicalC3CameraResolvedHolomorphicDirectCenterState
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (directCamera : ℕ) :
    CarryVerticalL2 :=
  finiteC3LegL2Extension (3 * M)
    (cameraResolvedIndependentReflectedUndressedDirectGreenPort
      M q hq0 hq1 S u 0 directCamera).1

/-- Zero-extend the finite ordinary reflected leg at the central spectral
parameter into the common `CarryVerticalL2` TFVD space. -/
def canonicalC3CameraResolvedHolomorphicReflectedCenterState
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (reflectedCamera : ℕ) :
    CarryVerticalL2 :=
  finiteC3LegL2Extension (3 * M)
    (cameraResolvedIndependentReflectedUndressedReflectedGreenPort
      M q hq0 hq1 S u 0 reflectedCamera).1

/-- The finite central Green inner product is preserved exactly by the
existing zero-extension isometry into `CarryVerticalL2`. -/
theorem canonicalC3CameraResolvedHolomorphicCentralInner_eq_tfvdInner
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
      M q hq0 hq1 S u directCamera reflectedCamera 0 =
      inner ℂ
        (canonicalC3CameraResolvedHolomorphicDirectCenterState
          M q hq0 hq1 S u directCamera)
        (canonicalC3CameraResolvedHolomorphicReflectedCenterState
          M q hq0 hq1 S u reflectedCamera) := by
  unfold canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
    canonicalC3CameraResolvedHolomorphicDirectCenterState
    canonicalC3CameraResolvedHolomorphicReflectedCenterState
  symm
  exact (finiteC3LegL2ExtensionIsometry (3 * M)).inner_map_map _ _

/-! ## The four reconstructed TFVD channels -/

/-- Green reconstruction of the direct central leg from its centered bracket
data. -/
def canonicalC3CameraResolvedHolomorphicDirectGreenChannel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (directCamera : ℕ) :
    CarryVerticalL2 :=
  carryVerticalL2WeightedGreen canonicalC3TfvdRatio
    (carryWeightedVerticalCenteredBracket canonicalC3TfvdRatio
      (canonicalC3CameraResolvedHolomorphicDirectCenterState
        M q hq0 hq1 S u directCamera))

/-- Green reconstruction of the reflected central leg from its centered
bracket data. -/
def canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (reflectedCamera : ℕ) :
    CarryVerticalL2 :=
  carryVerticalL2WeightedGreen canonicalC3TfvdRatio
    (carryWeightedVerticalCenteredBracket canonicalC3TfvdRatio
      (canonicalC3CameraResolvedHolomorphicReflectedCenterState
        M q hq0 hq1 S u reflectedCamera))

/-- Boundary-return reconstruction of the direct central trace datum. -/
def canonicalC3CameraResolvedHolomorphicDirectReturnChannel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (directCamera : ℕ) :
    CarryVerticalL2 :=
  carryWeightedVerticalReturn canonicalC3TfvdRatio
    (canonicalBR2CarryAmplitudeRatio_pos (by norm_num [IsSupported] : IsSupported 3)).le
    (canonicalBR2CarryAmplitudeRatio_lt_one (by norm_num [IsSupported] : IsSupported 3))
    (carryWeightedVerticalTrace canonicalC3TfvdRatio
      (canonicalC3CameraResolvedHolomorphicDirectCenterState
        M q hq0 hq1 S u directCamera))

/-- Boundary-return reconstruction of the reflected central trace datum. -/
def canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (reflectedCamera : ℕ) :
    CarryVerticalL2 :=
  carryWeightedVerticalReturn canonicalC3TfvdRatio
    (canonicalBR2CarryAmplitudeRatio_pos (by norm_num [IsSupported] : IsSupported 3)).le
    (canonicalBR2CarryAmplitudeRatio_lt_one (by norm_num [IsSupported] : IsSupported 3))
    (carryWeightedVerticalTrace canonicalC3TfvdRatio
      (canonicalC3CameraResolvedHolomorphicReflectedCenterState
        M q hq0 hq1 S u reflectedCamera))

/-- The direct ordinary state is reconstructed from its Green/bracket leg and
its boundary-return/trace leg. -/
theorem canonicalC3CameraResolvedHolomorphicDirectCenterState_green_add_return
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (directCamera : ℕ) :
    canonicalC3CameraResolvedHolomorphicDirectGreenChannel
        M q hq0 hq1 S u directCamera +
      canonicalC3CameraResolvedHolomorphicDirectReturnChannel
        M q hq0 hq1 S u directCamera =
      canonicalC3CameraResolvedHolomorphicDirectCenterState
        M q hq0 hq1 S u directCamera := by
  let hbase3 : IsSupported 3 := by norm_num [IsSupported]
  ext n
  exact carryWeightedVerticalTfvd_apply canonicalC3TfvdRatio
    (canonicalBR2CarryAmplitudeRatio_pos hbase3)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase3)
    (canonicalC3CameraResolvedHolomorphicDirectCenterState
      M q hq0 hq1 S u directCamera) n

/-- The reflected ordinary state is reconstructed from its Green/bracket leg
and its boundary-return/trace leg. -/
theorem canonicalC3CameraResolvedHolomorphicReflectedCenterState_green_add_return
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ) (reflectedCamera : ℕ) :
    canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
        M q hq0 hq1 S u reflectedCamera +
      canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
        M q hq0 hq1 S u reflectedCamera =
      canonicalC3CameraResolvedHolomorphicReflectedCenterState
        M q hq0 hq1 S u reflectedCamera := by
  let hbase3 : IsSupported 3 := by norm_num [IsSupported]
  ext n
  exact carryWeightedVerticalTfvd_apply canonicalC3TfvdRatio
    (canonicalBR2CarryAmplitudeRatio_pos hbase3)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase3)
    (canonicalC3CameraResolvedHolomorphicReflectedCenterState
      M q hq0 hq1 S u reflectedCamera) n

/-- The exact reconstruction identity for the central ordinary-source inner
product.  `GG`, `GR`, `RG`, and `RR` all remain visible: this is the synthesis
pairing, not the distinct TFVD analysis metric. -/
theorem canonicalC3CameraResolvedHolomorphicCentralInner_eq_tfvdFourChannel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenCentralInner
      M q hq0 hq1 S u directCamera reflectedCamera 0 =
      inner ℂ
        (canonicalC3CameraResolvedHolomorphicDirectGreenChannel
          M q hq0 hq1 S u directCamera)
        (canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
          M q hq0 hq1 S u reflectedCamera) +
      inner ℂ
        (canonicalC3CameraResolvedHolomorphicDirectGreenChannel
          M q hq0 hq1 S u directCamera)
        (canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
          M q hq0 hq1 S u reflectedCamera) +
      inner ℂ
        (canonicalC3CameraResolvedHolomorphicDirectReturnChannel
          M q hq0 hq1 S u directCamera)
        (canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
          M q hq0 hq1 S u reflectedCamera) +
      inner ℂ
        (canonicalC3CameraResolvedHolomorphicDirectReturnChannel
          M q hq0 hq1 S u directCamera)
        (canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
          M q hq0 hq1 S u reflectedCamera) := by
  let hbase3 : IsSupported 3 := by norm_num [IsSupported]
  rw [canonicalC3CameraResolvedHolomorphicCentralInner_eq_tfvdInner]
  simpa [canonicalC3TfvdRatio,
    canonicalC3CameraResolvedHolomorphicDirectGreenChannel,
    canonicalC3CameraResolvedHolomorphicReflectedGreenChannel,
    canonicalC3CameraResolvedHolomorphicDirectReturnChannel,
    canonicalC3CameraResolvedHolomorphicReflectedReturnChannel] using
    canonicalCarryTfvd_inner_eq_fourChannel hbase3
      (canonicalC3CameraResolvedHolomorphicDirectCenterState
        M q hq0 hq1 S u directCamera)
      (canonicalC3CameraResolvedHolomorphicReflectedCenterState
        M q hq0 hq1 S u reflectedCamera)

/-- The distinct TFVD analysis metric of the same two central states.  It has
one bracket block and one trace-metric block; unlike the reconstructed Hilbert
pairing above, it does not contain the two synthesis cross terms. -/
theorem canonicalC3CameraResolvedHolomorphicCenterAnalysisMetric_eq_bracket_add_trace
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    inner ℂ
      (carryTfvdCausalSecondDifference canonicalC3TfvdRatio
        (canonicalC3CameraResolvedHolomorphicDirectCenterState
          M q hq0 hq1 S u directCamera))
      (carryTfvdCausalSecondDifference canonicalC3TfvdRatio
        (canonicalC3CameraResolvedHolomorphicReflectedCenterState
          M q hq0 hq1 S u reflectedCamera)) =
      inner ℂ
        (carryWeightedVerticalCenteredBracket canonicalC3TfvdRatio
          (canonicalC3CameraResolvedHolomorphicDirectCenterState
            M q hq0 hq1 S u directCamera))
        (carryWeightedVerticalCenteredBracket canonicalC3TfvdRatio
          (canonicalC3CameraResolvedHolomorphicReflectedCenterState
            M q hq0 hq1 S u reflectedCamera)) +
      carryTfvdTraceMetric canonicalC3TfvdRatio
        (carryWeightedVerticalTrace canonicalC3TfvdRatio
          (canonicalC3CameraResolvedHolomorphicDirectCenterState
            M q hq0 hq1 S u directCamera))
        (carryWeightedVerticalTrace canonicalC3TfvdRatio
          (canonicalC3CameraResolvedHolomorphicReflectedCenterState
            M q hq0 hq1 S u reflectedCamera)) := by
  exact carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace
    canonicalC3TfvdRatio
    (canonicalC3CameraResolvedHolomorphicDirectCenterState
      M q hq0 hq1 S u directCamera)
    (canonicalC3CameraResolvedHolomorphicReflectedCenterState
      M q hq0 hq1 S u reflectedCamera)

/-- The first holomorphic Green coefficient reads the complete reconstructed
TFVD Hilbert pairing.  In particular, no individual bracket, trace, or mixed
channel is silently discarded. -/
theorem canonicalC3CameraResolvedHolomorphicGreenFirstJet_eq_tfvdFourChannel
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext) (u : ℂ)
    (directCamera reflectedCamera : ℕ) :
    canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient
      M q hq0 hq1 S u directCamera reflectedCamera 1 =
      holomorphicC3EigenvalueDerivativeAtZero *
        (inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectGreenChannel
            M q hq0 hq1 S u directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
            M q hq0 hq1 S u reflectedCamera) +
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectGreenChannel
            M q hq0 hq1 S u directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
            M q hq0 hq1 S u reflectedCamera) +
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectReturnChannel
            M q hq0 hq1 S u directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedGreenChannel
            M q hq0 hq1 S u reflectedCamera) +
        inner ℂ
          (canonicalC3CameraResolvedHolomorphicDirectReturnChannel
            M q hq0 hq1 S u directCamera)
          (canonicalC3CameraResolvedHolomorphicReflectedReturnChannel
            M q hq0 hq1 S u reflectedCamera)) := by
  rw [canonicalC3CameraResolvedIndependentReflectedHolomorphicGreenJetCoefficient_one_eq_scaledCentralInner,
    canonicalC3CameraResolvedHolomorphicCentralInner_eq_tfvdFourChannel]

/-! ## Discrete bracket and logarithmic clock scalars -/

/-- The bracket input to each Green channel is the vertical realization of
the carry bracket.  Coordinatewise, the latter is the gauged weighted second
difference supplied by `weightedScalarSecondDifference_gauge_eq_bracket`.
No claim equates that discrete operator with the holomorphic derivative. -/
theorem carryWeightedVerticalCenteredBracket_succ_eq_scalarSecondDifference
    (q : ℝ) (hq : 0 < q) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracket q x (n + 1) =
      carryWeightedScalarSecondDifference (q : ℂ) (fun k => x k) n := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [carryWeightedVerticalCenteredBracket_succ,
    carryWeightedScalarSecondDifference_eq hqC]

/-- After the amplitude gauge, the scalar second-difference readout is the
ordinary discrete bracket with its exact carry factor.  Together with
`carryWeightedVerticalCenteredBracket_succ_eq_scalarSecondDifference`, this
is the coordinatewise origin of the bracket input to the Green channels. -/
theorem canonicalC3TfvdBracket_is_gaugedSecondDifference
    (q : ℂ) (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarSecondDifference q (carryAmplitudeGauge q x) n =
      q ^ (n + 1) * DiscreteValve.bracket x n :=
  weightedScalarSecondDifference_gauge_eq_bracket q hq x n

/-- The C3 holomorphic eigenvalue is the critical amplitude transported by
the logarithmic clock frequency `-I log 3`. -/
theorem holomorphicC3EigenvalueAlongHeight_eq_logClockOrbit
    (z : ℂ) :
    holomorphicC3EigenvalueAlongHeight z =
      nativeCriticalDirichletAmplitude 3 *
        Complex.exp ((-Complex.I * (Real.log (3 : ℝ) : ℂ)) * z) := by
  exact natDirichletTerm_operatorHeightParameter_eq_logOrbit (by norm_num) z

/-- The first C3 eigenvalue coefficient is the critical amplitude multiplied
by the scalar logarithmic-clock frequency. -/
theorem holomorphicC3EigenvalueDerivativeAtZero_eq_logClockFrequency :
    holomorphicC3EigenvalueDerivativeAtZero =
      nativeCriticalDirichletAmplitude 3 *
        (-Complex.I * (Real.log (3 : ℝ) : ℂ)) := by
  unfold holomorphicC3EigenvalueDerivativeAtZero nativeCriticalDirichletAmplitude
    natLogDirichletTerm
  ring_nf

/-- The scalar frequency in the C3 eigenvalue is `-I` times the native
logarithmic-generator eigenvalue on the basis vector indexed by `2`, whose
native label is `2 + 1 = 3`. -/
theorem holomorphicC3LogClockFrequency_smul_basisVector_two :
    (-Complex.I * (Real.log (3 : ℝ) : ℂ)) • infiniteRealSpectralBasisVector 2 =
      (-Complex.I) •
        nativeLogGenerator
          ⟨infiniteRealSpectralBasisVector 2, nativeLogBasisVector_mem_domain 2⟩ := by
  rw [nativeLogGenerator_basisVector_log]
  norm_num
  rw [smul_smul]

end

end CarrySelfAdjointOperator

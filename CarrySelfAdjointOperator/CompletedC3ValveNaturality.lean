import CarrySelfAdjointOperator.CompletedC3SameStructuredBoundaryState
import CarrySelfAdjointOperator.ProjectiveValveAlgebra
import CarrySelfAdjointOperator.GreenMultiplicativeValveMass
import CarrySelfAdjointOperator.DiscreteValveSeries
import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdFinite
import CPFormal.Analytic.CpFiniteLogJetCommutator
import NativeCarryC3Crosswalk.CompletedTfvdGreenIntertwining
import Mathlib.Tactic

/-!
# Completed C3 valve naturality

The repository contains several exact descriptions of the same native/C3
geometry which were built at historically different layers:

* the weighted vertical TFVD used by the native/C3 geometry;
* the additive `DiscreteValve` in the original depth coordinate `X`;
* the Green channel and logarithmic potential feeding the multiplicative
  valve;
* the projective depth coordinate `Y = X/(1-X)` used by `ProjectiveValve`;
* the concrete ordinary/log-jet completed C3 ledger and its six-camera Gamma
  source;
* the completed scalar product whose value/companion are `(F,-F')`.

This module begins the target-specific naturality theorem tying those layers
without identifying different coordinate systems by fiat.

1. Multiplication of a sequence by the carry amplitude `q^n` conjugates the
   ordinary additive first/second differences to the weighted TFVD
   differences.
2. The Green reconstruction of the additive valve is literally the
   `greenChannelSeries` already used by the multiplicative valve.
3. The concrete Cp log-block identity becomes an equality of curvature series
   in `X`; transporting all three terms with `toProjective` gives the same
   equality in `Y`.
4. `projectiveValveMass_add` then sends that exact additive split to a product
   of normalized multiplicative masses.  By the fundamental theorem this is
   the same Green-mass construction as the original `X`-coordinate curvature.
5. The ordinary and log-jet coefficients are literally the ones stored by the
   completed C3 ledger; that ledger reconstructs the C3 port packed into the
   six-camera source used by Gamma.
6. Independently, the completed characteristic is already the product of the
   xi-completion factor and the normalized C3 value, and its boundary
   companion is the corresponding product-rule companion.

No Gamma--Wronskian sewing identity is assumed here.  The point is to remove
change-of-clothes ambiguity one commuting square at a time.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open PowerSeries

noncomputable section

/-! ## 1. Weighted TFVD as the additive valve in amplitude coordinates -/

/-- Dress an unweighted sequence by the geometric carry amplitude `q^n`. -/
def carryAmplitudeGauge (q : ℂ) (x : ℕ → ℂ) : ℕ → ℂ :=
  fun n => q ^ n * x n

/-- Remove the same geometric carry amplitude. -/
def carryAmplitudeUngauge (q : ℂ) (x : ℕ → ℂ) : ℕ → ℂ :=
  fun n => q⁻¹ ^ n * x n

/-- Dressing followed by undressing is the identity away from `q = 0`. -/
theorem carryAmplitudeUngauge_gauge
    (q : ℂ) (hq : q ≠ 0) (x : ℕ → ℂ) :
    carryAmplitudeUngauge q (carryAmplitudeGauge q x) = x := by
  funext n
  unfold carryAmplitudeUngauge carryAmplitudeGauge
  rw [inv_pow]
  field_simp [hq]

/-- The weighted first difference is the ordinary first difference in the
`q^n` amplitude gauge. -/
theorem carryWeightedScalarFirstDifference_gauge
    (q : ℂ) (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarFirstDifference q (carryAmplitudeGauge q x) n =
      q ^ n * DiscreteValve.fdiff x n := by
  unfold carryWeightedScalarFirstDifference carryAmplitudeGauge
    DiscreteValve.fdiff
  rw [pow_succ]
  field_simp [hq]

/-- The weighted second difference/bracket is exactly the ordinary additive
bracket, conjugated by one extra carry amplitude. -/
theorem carryWeightedScalarSecondDifference_gauge
    (q : ℂ) (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarSecondDifference q (carryAmplitudeGauge q x) n =
      q ^ (n + 1) * DiscreteValve.bracket x n := by
  unfold carryWeightedScalarSecondDifference
  rw [carryWeightedScalarFirstDifference_gauge q hq x (n + 1),
    carryWeightedScalarFirstDifference_gauge q hq x n,
    DiscreteValve.bracket_eq_fdiff_sub, pow_succ]
  ring

/-! ## 2. Additive Green reconstruction is the multiplicative valve channel -/

/-- The Green sum reconstructed by `DiscreteValve` is exactly the formal
Green channel which the multiplicative-valve layer integrates logarithmically.
No asymptotic or analytic limit is involved. -/
theorem mk_discreteValveGreenSum_eq_greenChannelSeries
    (x : ℕ → ℂ) :
    mk (fun n => DiscreteValve.greenSum x n) =
      GreenMultiplicativeValveBridge.greenChannelSeries
        (mk (DiscreteValve.bracket x)) := by
  rw [DiscreteValve.mk_greenSum]
  rfl

/-! ## 3. The concrete Cp log block inside the additive curvature space -/

/-- Infinite ordinary-gradient series whose first three coefficients are the
ordinary provenance leg of one complete C3 block. -/
def canonicalCpOrdinaryGradientSeries (s : ℂ) : PowerSeries ℂ :=
  mk (positiveDirichletGradient s)

/-- Infinite logarithmic-jet gradient series. -/
def canonicalCpLogJetGradientSeries (s : ℂ) : PowerSeries ℂ :=
  mk (positiveLogDirichletGradient s)

/-- The actual Cp log-block sequence, promoted coefficientwise to the original
`X`-coordinate curvature space. -/
def canonicalCpLogBlockGradientSeries (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  mk (cpLogBlockGradient p s)

/-- The transported logarithmic-jet summand in the Cp block identity. -/
def canonicalCpTransportedLogJetSeries (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  mk (fun n => natDirichletTerm s p * positiveLogDirichletGradient s n)

/-- The radial/log-scale ordinary-gradient summand in the same identity. -/
def canonicalCpLogScaleOrdinarySeries (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  mk (fun n => cpLogScaleCoefficient p s * positiveDirichletGradient s n)

/-- The Cp log-jet commutator as a curvature series. -/
def canonicalCpLogJetCommutatorSeries (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  mk (cpLogJetCommutator p s)

@[simp] theorem coeff_canonicalCpOrdinaryGradientSeries
    (s : ℂ) (n : ℕ) :
    coeff n (canonicalCpOrdinaryGradientSeries s) =
      positiveDirichletGradient s n := by
  simp [canonicalCpOrdinaryGradientSeries]

@[simp] theorem coeff_canonicalCpLogJetGradientSeries
    (s : ℂ) (n : ℕ) :
    coeff n (canonicalCpLogJetGradientSeries s) =
      positiveLogDirichletGradient s n := by
  simp [canonicalCpLogJetGradientSeries]

/-- The concrete local Leibniz rule is literally an additive decomposition in
`ℂ⟦X⟧`. -/
theorem canonicalCpLogBlockGradientSeries_eq_add
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    canonicalCpLogBlockGradientSeries p s =
      canonicalCpTransportedLogJetSeries p s +
        canonicalCpLogScaleOrdinarySeries p s := by
  ext n
  simp [canonicalCpLogBlockGradientSeries,
    canonicalCpTransportedLogJetSeries,
    canonicalCpLogScaleOrdinarySeries,
    cpLogBlockGradient_eq_eigenvalue_mul_logJet_add_logScale p hp s n]

/-- The logarithmic commutator is not a new independent curvature direction:
it is exactly the ordinary-gradient log-scale summand. -/
theorem canonicalCpLogJetCommutatorSeries_eq_logScaleOrdinary
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    canonicalCpLogJetCommutatorSeries p s =
      canonicalCpLogScaleOrdinarySeries p s := by
  ext n
  simp [canonicalCpLogJetCommutatorSeries,
    canonicalCpLogScaleOrdinarySeries,
    cpLogJetCommutator_eq_logScale_mul_gradient p hp s n]

/-! ## 4. Transport the concrete split into the projective depth chart -/

/-- Full Cp log-block curvature in the projective depth coordinate `Y`. -/
def canonicalCpLogBlockProjectiveCurvature
    (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  ProjectiveDepth.toProjective (canonicalCpLogBlockGradientSeries p s)

/-- Transported log-jet curvature in the same `Y` coordinate. -/
def canonicalCpTransportedLogJetProjectiveCurvature
    (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  ProjectiveDepth.toProjective (canonicalCpTransportedLogJetSeries p s)

/-- Transported ordinary/log-scale curvature in `Y`. -/
def canonicalCpLogScaleOrdinaryProjectiveCurvature
    (p : ℕ) (s : ℂ) : PowerSeries ℂ :=
  ProjectiveDepth.toProjective (canonicalCpLogScaleOrdinarySeries p s)

/-- The additive Cp split survives the exact `X ↔ Y` coordinate change. -/
theorem canonicalCpLogBlockProjectiveCurvature_eq_add
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    canonicalCpLogBlockProjectiveCurvature p s =
      canonicalCpTransportedLogJetProjectiveCurvature p s +
        canonicalCpLogScaleOrdinaryProjectiveCurvature p s := by
  unfold canonicalCpLogBlockProjectiveCurvature
    canonicalCpTransportedLogJetProjectiveCurvature
    canonicalCpLogScaleOrdinaryProjectiveCurvature
  rw [canonicalCpLogBlockGradientSeries_eq_add p hp s,
    ProjectiveDepth.toProjective_add]

/-- Projective-valve naturality for the concrete Cp logarithmic block: after
transporting the actual `X`-coordinate curvatures to `Y`, the mass attached to
the full block is exactly the product of the masses attached to its two
additive channels. -/
theorem projectiveValveMass_canonicalCpLogBlock_eq_mul
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    ProjectiveValve.projectiveValveMass
        (canonicalCpLogBlockProjectiveCurvature p s) =
      ProjectiveValve.projectiveValveMass
          (canonicalCpTransportedLogJetProjectiveCurvature p s) *
        ProjectiveValve.projectiveValveMass
          (canonicalCpLogScaleOrdinaryProjectiveCurvature p s) := by
  rw [canonicalCpLogBlockProjectiveCurvature_eq_add p hp s,
    ProjectiveValve.projectiveValveMass_add]

/-- The full projective-valve mass is definitionally the Green-derived
multiplicative mass of the original Cp curvature after the exact coordinate
change. -/
theorem projectiveValveMass_canonicalCpLogBlock_eq_projectiveGreenMass
    (p : ℕ) (s : ℂ) :
    ProjectiveValve.projectiveValveMass
        (canonicalCpLogBlockProjectiveCurvature p s) =
      GreenMultiplicativeValveBridge.projectiveGreenMass
        (canonicalCpLogBlockGradientSeries p s) := by
  unfold canonicalCpLogBlockProjectiveCurvature
  exact ProjectiveValve.projectiveValveMass_toProjective
    (canonicalCpLogBlockGradientSeries p s)

/-! ## 5. The valve series are the same ordinary/log-jet data stored by C3 -/

/-- At one complete C3 block, the ordinary ledger edge is literally the
matching coefficient of the ordinary valve curvature series. -/
theorem seededCompletedTfvdGreenLedger_ordinary_eq_valveSeriesCoeff
    (s : ℂ) (i : Fin 3) :
    (seededCompletedTfvdGreenLedger 1 s).1.1.2 i =
      coeff i.val (canonicalCpOrdinaryGradientSeries s) := by
  have hi : i.val < 3 := i.isLt
  simp [seededCompletedTfvdGreenLedger,
    c2DirichletGradientPrefixCore_apply,
    canonicalCpOrdinaryGradientSeries, hi]

/-- The logarithmic-jet ledger edge is the matching coefficient of the
log-jet valve curvature series. -/
theorem seededCompletedTfvdGreenLedger_logJet_eq_valveSeriesCoeff
    (s : ℂ) (i : Fin 3) :
    (seededCompletedTfvdGreenLedger 1 s).1.2.2 i =
      coeff i.val (canonicalCpLogJetGradientSeries s) := by
  have hi : i.val < 3 := i.isLt
  simp [seededCompletedTfvdGreenLedger,
    c2LogJetPrefixCore_apply,
    canonicalCpLogJetGradientSeries, hi]

/-- The Gamma source obtained from the structured one-point C3 state is also
literally the faithful packing of the C3 port reconstructed from the same
ordinary/log-jet completed ledger. -/
theorem canonicalCompletedC3StructuredGammaSource_eq_ledgerPacking
    (z : ℂ) :
    canonicalCompletedC3StructuredGammaSource z =
      c3SixCameraPacking
        (completedTfvdGreenLedgerC3Port (operatorHeightParameter z)
          (seededCompletedTfvdGreenLedger 1 (operatorHeightParameter z))) := by
  rw [canonicalCompletedC3StructuredGammaSource_eq_canonical,
    canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState]
  rfl

/-! ## 6. The completed scalar trace is the same multiplicative product -/

/-- The completed characteristic itself is already the product of the
archimedean completion mass and the normalized C3 value read from the same
completed TFVD state. -/
theorem completedNativeOperatorCharacteristic_eq_completion_mul_c3Value
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorCharacteristic z =
      nativeXiCompletionFactor z *
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z := by
  calc
    completedNativeOperatorCharacteristic z =
        canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z :=
      (canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hs).symm
    _ = nativeXiCompletionFactor z *
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout z := rfl

/-- Its canonical companion is the product-rule companion of precisely those
same two factors. -/
theorem completedNativeOperatorBoundaryCompanion_eq_productCompanion
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorBoundaryCompanion z =
      productBoundaryCompanion
        nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion
        canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout
        canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout z := by
  calc
    completedNativeOperatorBoundaryCompanion z =
        canonicalCompletedC3EnrichedTfvdBoundaryCompanion z :=
      (canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hs).symm
    _ = _ := rfl

/-- Compact capstone: on the actual completed C3 family, the two first
provenance channels are coefficient restrictions of the formal valve
curvatures, their exact local log-block split survives the projective depth
change and becomes a product of normalized masses, and their reconstructed C3
port is exactly the source fed to Gamma. -/
theorem canonicalCompletedC3ValveNaturality
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    (∀ i : Fin 3,
      (seededCompletedTfvdGreenLedger 1 s).1.1.2 i =
        coeff i.val (canonicalCpOrdinaryGradientSeries s)) ∧
    (∀ i : Fin 3,
      (seededCompletedTfvdGreenLedger 1 s).1.2.2 i =
        coeff i.val (canonicalCpLogJetGradientSeries s)) ∧
    canonicalCpLogBlockProjectiveCurvature p s =
      canonicalCpTransportedLogJetProjectiveCurvature p s +
        canonicalCpLogScaleOrdinaryProjectiveCurvature p s ∧
    ProjectiveValve.projectiveValveMass
        (canonicalCpLogBlockProjectiveCurvature p s) =
      ProjectiveValve.projectiveValveMass
          (canonicalCpTransportedLogJetProjectiveCurvature p s) *
        ProjectiveValve.projectiveValveMass
          (canonicalCpLogScaleOrdinaryProjectiveCurvature p s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact seededCompletedTfvdGreenLedger_ordinary_eq_valveSeriesCoeff s i
  · intro i
    exact seededCompletedTfvdGreenLedger_logJet_eq_valveSeriesCoeff s i
  · exact canonicalCpLogBlockProjectiveCurvature_eq_add p hp s
  · exact projectiveValveMass_canonicalCpLogBlock_eq_mul p hp s

end

end CarrySelfAdjointOperator

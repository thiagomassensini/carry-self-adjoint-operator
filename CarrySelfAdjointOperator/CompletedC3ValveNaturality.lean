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

The repository now contains two exact valve formalisms which were built at
historically different layers:

* the weighted vertical TFVD used by the native/C3 geometry;
* the additive `DiscreteValve` and multiplicative/projective valve written in
  formal power series.

This module begins the target-specific identification of those layers.  It
proves three literal compatibility statements.

1.  Multiplication of a sequence by the carry amplitude `q^n` conjugates the
    ordinary additive first/second differences to the weighted TFVD
    differences.  In particular the weighted bracket is the ordinary bracket
    in amplitude coordinates.
2.  The concrete Cp log-block identity from `CPFormal` becomes an equality of
    formal curvature series: the log-block is exactly the sum of a transported
    log-jet channel and the ordinary radial/log-scale channel.
3.  The projective valve sends that exact additive split to a multiplicative
    factorization of the canonical normalized masses.

Finally the ordinary and log-jet series are identified coefficientwise with
exactly the two provenance-preserving prefixes stored by the completed C3
ledger.  The same ledger reconstructs the C3 Green port which is packed into
the six-camera source used by the Gamma field.

No Gamma--Wronskian sewing identity is assumed here.  The point is to remove a
change-of-clothes ambiguity: the native weighted bracket, the C3
ordinary/log-jet ledger, and the additive/multiplicative valve are now tied by
explicit maps on the concrete canonical family.
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
  ring

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

/-! ## 2. The concrete Cp log block inside the additive curvature space -/

/-- Infinite ordinary-gradient series whose first three coefficients are the
ordinary provenance leg of one complete C3 block. -/
def canonicalCpOrdinaryGradientSeries (s : ℂ) : PowerSeries ℂ :=
  mk (positiveDirichletGradient s)

/-- Infinite logarithmic-jet gradient series. -/
def canonicalCpLogJetGradientSeries (s : ℂ) : PowerSeries ℂ :=
  mk (positiveLogDirichletGradient s)

/-- The actual Cp log-block sequence, promoted coefficientwise to the same
formal curvature space used by the projective valve. -/
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

/-! ## 3. The same additive split becomes a multiplicative factorization -/

/-- Projective-valve naturality for the concrete Cp logarithmic block: the
mass attached to the full block is exactly the product of the masses attached
to its two additive curvature channels. -/
theorem projectiveValveMass_canonicalCpLogBlock_eq_mul
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    ProjectiveValve.projectiveValveMass
        (canonicalCpLogBlockGradientSeries p s) =
      ProjectiveValve.projectiveValveMass
          (canonicalCpTransportedLogJetSeries p s) *
        ProjectiveValve.projectiveValveMass
          (canonicalCpLogScaleOrdinarySeries p s) := by
  rw [canonicalCpLogBlockGradientSeries_eq_add p hp s,
    ProjectiveValve.projectiveValveMass_add]

/-! ## 4. The valve series are the same ordinary/log-jet data stored by C3 -/

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

/-- Compact capstone: on the actual completed C3 family, the two first
provenance channels are coefficient restrictions of the formal valve
curvatures, while their reconstructed C3 port is exactly the source fed to the
Gamma field.  Together with `projectiveValveMass_canonicalCpLogBlock_eq_mul`,
this is the target-specific naturality bridge from the C3 ledger to the
additive/multiplicative valve. -/
theorem canonicalCompletedC3ValveNaturality
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    (∀ i : Fin 3,
      (seededCompletedTfvdGreenLedger 1 s).1.1.2 i =
        coeff i.val (canonicalCpOrdinaryGradientSeries s)) ∧
    (∀ i : Fin 3,
      (seededCompletedTfvdGreenLedger 1 s).1.2.2 i =
        coeff i.val (canonicalCpLogJetGradientSeries s)) ∧
    canonicalCpLogBlockGradientSeries p s =
      canonicalCpTransportedLogJetSeries p s +
        canonicalCpLogScaleOrdinarySeries p s ∧
    ProjectiveValve.projectiveValveMass
        (canonicalCpLogBlockGradientSeries p s) =
      ProjectiveValve.projectiveValveMass
          (canonicalCpTransportedLogJetSeries p s) *
        ProjectiveValve.projectiveValveMass
          (canonicalCpLogScaleOrdinarySeries p s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact seededCompletedTfvdGreenLedger_ordinary_eq_valveSeriesCoeff s i
  · intro i
    exact seededCompletedTfvdGreenLedger_logJet_eq_valveSeriesCoeff s i
  · exact canonicalCpLogBlockGradientSeries_eq_add p hp s
  · exact projectiveValveMass_canonicalCpLogBlock_eq_mul p hp s

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.NativeIncidenceCauchyPorts
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite-support TFVD valve and two traces, synthesized in the ORIGINAL
completed continuous two-leg representatives, then mapped into the original Lp.
Input coefficients precede the amplitude. No inverse or unitary Laguerre map
is assumed; the corrected Green numerator remains an exact vector identity. -/
namespace CarrySelfAdjointOperator.NativeCauchyPorts
open scoped BigOperators
open FirstEdgeSewing
noncomputable section
set_option autoImplicit false

def coefficientShift : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ Nat.succ
def coefficientLeftShift : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  Finsupp.lcomapDomain Nat.succ Nat.succ_injective

theorem coefficientShift_zero (x : ℕ →₀ ℂ) : coefficientShift x 0 = 0 := by
  exact Finsupp.mapDomain_notin_range x 0 (by simp)

theorem coefficientShift_succ (x : ℕ →₀ ℂ) (j : ℕ) : coefficientShift x (j+1) = x j :=
  Finsupp.mapDomain_apply Nat.succ_injective x j

def finiteCoefficientValve (q : ℝ) (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  (q : ℂ)⁻¹ • x - (2 : ℂ) • coefficientShift x +
    (q : ℂ) • coefficientShift (coefficientShift x)

def finiteTrace0 (x : ℕ →₀ ℂ) : ℂ := x 0
def finiteTrace1 (q : ℝ) (x : ℕ →₀ ℂ) : ℂ := (q : ℂ)⁻¹*x 1-x 0

def finiteTfvdBulk (q : ℝ) (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  coefficientLeftShift (finiteCoefficientValve q x) -
    Finsupp.single 0 (finiteTrace1 q x-finiteTrace0 x)

theorem finiteTfvdBulk_zero (q : ℝ) (x : ℕ →₀ ℂ) : finiteTfvdBulk q x 0=0 := by
  simp [finiteTfvdBulk, finiteCoefficientValve, finiteTrace0, finiteTrace1,
    coefficientLeftShift, coefficientShift_zero, coefficientShift_succ]
  ring

/-- Literal bulk formula, matching the original zero-based TFVD convention. -/
theorem finiteTfvdBulk_succ (q : ℝ) (x : ℕ →₀ ℂ) (j : ℕ) :
    finiteTfvdBulk q x (j+1) = (q : ℂ)⁻¹*x (j+2)-2*x (j+1)+(q : ℂ)*x j := by
  simp [finiteTfvdBulk, finiteCoefficientValve, coefficientLeftShift,
    coefficientShift_succ, Nat.add_assoc]

theorem finiteCoefficientValve_two_traces (q : ℝ) (x : ℕ →₀ ℂ) :
    finiteCoefficientValve q x =
      Finsupp.single 0 ((q : ℂ)⁻¹*finiteTrace0 x) +
      Finsupp.single 1 (finiteTrace1 q x-finiteTrace0 x) +
      coefficientShift (finiteTfvdBulk q x) := by
  ext j
  rcases j with _ | j
  · simp [finiteCoefficientValve, finiteTrace0, coefficientShift_zero]
  · rcases j with _ | j
    · simp [finiteCoefficientValve, finiteTrace0, finiteTrace1, coefficientShift_zero,
        coefficientShift_succ, finiteTfvdBulk_zero]
      ring
    · simp [finiteCoefficientValve, finiteTfvdBulk_succ, coefficientShift_succ, Nat.add_assoc]

def completedFiniteSynthesis (k : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ]
    (C(unitInterval, ℂ) × C(unitInterval, ℂ)) :=
  Finsupp.linearCombination ℂ (completedContinuousPair k)

def completedFiniteResidual (k : ℕ) : (ℕ →₀ ℂ) →ₗ[ℂ]
    (C(unitInterval, ℂ) × C(unitInterval, ℂ)) :=
  Finsupp.linearCombination ℂ (continuousAdvanceResidual k)

theorem completedFiniteSynthesis_shift (k : ℕ) (x : ℕ →₀ ℂ) :
    completedFiniteSynthesis k (coefficientShift x) =
      pairGeometricAdvance (completedFiniteSynthesis k x) + completedFiniteResidual k x := by
  change Finsupp.linearCombination ℂ (completedContinuousPair k) (Finsupp.mapDomain Nat.succ x) = _
  rw [Finsupp.linearCombination_mapDomain]
  simp only [completedFiniteSynthesis, completedFiniteResidual,
    Finsupp.linearCombination_apply, continuousAdvanceResidual, Finsupp.sum,
    Function.comp_apply, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  abel

theorem completedFiniteSynthesis_valve (q : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    completedFiniteSynthesis k (finiteCoefficientValve q x) =
      (q : ℂ)⁻¹ • completedFiniteSynthesis k x -
      (2 : ℂ) • pairGeometricAdvance (completedFiniteSynthesis k x) +
      (q : ℂ) • pairGeometricAdvance (pairGeometricAdvance (completedFiniteSynthesis k x)) -
      (2 : ℂ) • completedFiniteResidual k x +
      (q : ℂ) • (pairGeometricAdvance (completedFiniteResidual k x) +
        completedFiniteResidual k (coefficientShift x)) := by
  simp only [finiteCoefficientValve, map_add, map_sub, map_smul,
    completedFiniteSynthesis_shift]
  module

/-- Corrected Green numerator: seed, both independent traces, E b, E x and
E Sx are conserved before pairing. Inversion is a separate functional gate. -/
theorem completedFiniteGreen_corrected_numerator (q : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) :
    (q : ℂ)⁻¹ • completedFiniteSynthesis k x -
      (2 : ℂ) • pairGeometricAdvance (completedFiniteSynthesis k x) +
      (q : ℂ) • pairGeometricAdvance (pairGeometricAdvance (completedFiniteSynthesis k x)) =
      pairGeometricAdvance (completedFiniteSynthesis k (finiteTfvdBulk q x)) +
      completedFiniteResidual k (finiteTfvdBulk q x) +
      ((q : ℂ)⁻¹*finiteTrace0 x) • completedContinuousPair k 0 +
      (finiteTrace1 q x-finiteTrace0 x) • completedContinuousPair k 1 +
      (2 : ℂ) • completedFiniteResidual k x -
      (q : ℂ) • (pairGeometricAdvance (completedFiniteResidual k x) +
        completedFiniteResidual k (coefficientShift x)) := by
  have hc := completedFiniteSynthesis_valve q k x
  rw [finiteCoefficientValve_two_traces] at hc
  simp only [map_add] at hc
  have hsingle (j : ℕ) (a : ℂ) : completedFiniteSynthesis k (Finsupp.single j a) =
      a • completedContinuousPair k j := by simp [completedFiniteSynthesis]
  rw [hsingle, hsingle, completedFiniteSynthesis_shift] at hc
  linear_combination -hc

/-- Channel-by-channel adapter to the original physical Lp states. -/
theorem completedFiniteSynthesis_to_original (k : ℕ) (x : ℕ →₀ ℂ) :
    continuousPairToSource (completedFiniteSynthesis k x) =
      Finsupp.linearCombination ℂ (canonicalCompletedNativeRadialProjectiveChiralState k) x := by
  simp only [completedFiniteSynthesis, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, completedContinuousPair_toSource]

theorem completedFiniteResidual_to_original_channels (k : ℕ) (x : ℕ →₀ ℂ) :
    continuousPairToSource (completedFiniteResidual k x) =
      Finsupp.linearCombination ℂ (radialChiralAnalyticResidual k) x := by
  simp only [completedFiniteResidual, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact completedPair_advance_residual k j

/-- The gap between the two ORIGINAL normalized chiral coordinates is
constant on the regular section. Both denominators are explicit. -/
theorem normalized_chiral_gap (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    completedNativeNormalizedPositiveChiralAmplitude z -
      completedNativeNormalizedPositiveChiralAmplitude z *
        completedNativeHermiteBiehlerChiralQuotient z =
      (2 : ℂ)*Complex.I / (Real.sqrt 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne'
  have hm : completedNativeNormalizedPositiveChiralAmplitude z *
      completedNativeHermiteBiehlerChiralQuotient z =
      canonicalCompletedC3FullWronskianChiralNormalization z *
        completedNativeNegativeHermiteBiehlerCoordinate z := by
    unfold completedNativeNormalizedPositiveChiralAmplitude completedNativeHermiteBiehlerChiralQuotient
    field_simp [hP]
  rw [hm]
  unfold completedNativeNormalizedPositiveChiralAmplitude
  rw [← mul_sub]
  unfold canonicalCompletedC3FullWronskianChiralNormalization
    completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
  field_simp [hs, hF]
  ring

theorem regular_residual_equal_legs (k j : ℕ)
    (hreg : ∀ i ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (radialChiralAnalyticResidual k j).1 = (radialChiralAnalyticResidual k j).2 := by
  rw [radialAnalyticResidual_incident, radialAnalyticResidual_returned]
  congr 1
  have h0 := normalized_chiral_gap (canonicalCompletedC3RadialTiltPoint k j)
    (hreg j (by simp)).1 (hreg j (by simp)).2
  have h1 := normalized_chiral_gap (canonicalCompletedC3RadialTiltPoint k (j+1))
    (hreg (j+1) (by simp)).1 (hreg (j+1) (by simp)).2
  linear_combination h1-h0

theorem regular_residual_signed_pairing_zero (k i j : ℕ)
    (hi : ∀ a ∈ ({i,i+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k a) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k a) ≠ 0)
    (hj : ∀ a ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k a) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k a) ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (radialChiralAnalyticResidual k i) (radialChiralAnalyticResidual k j) = 0 := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [regular_residual_equal_legs k i hi, regular_residual_equal_legs k j hj, sub_self, mul_zero]

theorem regular_finiteResidual_equal_legs (k : ℕ) (x : ℕ →₀ ℂ)
    (hreg : ∀ j ∈ x.support, ∀ i ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (continuousPairToSource (completedFiniteResidual k x)).1 =
      (continuousPairToSource (completedFiniteResidual k x)).2 := by
  rw [completedFiniteResidual_to_original_channels]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum]
  change (AddMonoidHom.fst CanonicalCompletedNativeChiralCauchyCarrier
      CanonicalCompletedNativeChiralCauchyCarrier) (∑ j ∈ x.support, x j • radialChiralAnalyticResidual k j) =
    (AddMonoidHom.snd CanonicalCompletedNativeChiralCauchyCarrier
      CanonicalCompletedNativeChiralCauchyCarrier) (∑ j ∈ x.support, x j • radialChiralAnalyticResidual k j)
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change x j • (radialChiralAnalyticResidual k j).1 = x j • (radialChiralAnalyticResidual k j).2
  rw [regular_residual_equal_legs k j (hreg j hj)]

theorem regular_finiteResidual_signed_pairing_zero (k : ℕ) (x y : ℕ →₀ ℂ)
    (hx : ∀ j ∈ x.support, ∀ i ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hy : ∀ j ∈ y.support, ∀ i ∈ ({j,j+1} : Finset ℕ),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (continuousPairToSource (completedFiniteResidual k x))
      (continuousPairToSource (completedFiniteResidual k y)) = 0 := by
  unfold canonicalCompletedNativeProjectiveChiralForm
  rw [regular_finiteResidual_equal_legs k x hx,
    regular_finiteResidual_equal_legs k y hy, sub_self, mul_zero]

/-- All four sectors are preserved. Null self-pairing never deletes mixed crosses. -/
theorem completed_residual_four_sectors (C E D F : CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (C+E) (D+F) =
      canonicalCompletedNativeProjectiveChiralForm C D +
      canonicalCompletedNativeProjectiveChiralForm C F +
      canonicalCompletedNativeProjectiveChiralForm E D +
      canonicalCompletedNativeProjectiveChiralForm E F := by
  simp only [canonicalCompletedNativeProjectiveChiralForm, Prod.fst_add, Prod.snd_add,
    inner_add_left, inner_add_right]
  ring

end
end CarrySelfAdjointOperator.NativeCauchyPorts

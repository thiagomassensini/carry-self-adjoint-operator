import CarrySelfAdjointOperator.NativeGammaCollisionMaterialLedger
import CarrySelfAdjointOperator.CompletedNativeChiralReturnCompletionSplit

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators ComplexConjugate InnerProductSpace
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Boundary ChiralReturn
noncomputable section
set_option autoImplicit false

theorem nativeCompanion_centerChannels_cancel_nontrivially :
    nativeXiCompletionFactor 0 * nativeHeightScalarBoundaryCompanion 0 ≠ 0 ∧
    nativeXiCompletionBoundaryCompanion 0 * nativeHeightScalar 0 ≠ 0 ∧
    nativeXiCompletionFactor 0 * nativeHeightScalarBoundaryCompanion 0 +
      nativeXiCompletionBoundaryCompanion 0 * nativeHeightScalar 0 = 0 := by
  refine ⟨mul_ne_zero (nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain)
    (neg_ne_zero.mpr nativeHeightScalar_deriv_zero_ne_zero),
    mul_ne_zero (neg_ne_zero.mpr nativeXiCompletionFactor_deriv_zero_ne_zero)
      nativeHeightScalar_zero_ne_zero, nativeArchimedeanCompanionChannels_zero_cancel⟩

theorem nativeXi_native_centerWronskians_cancel_nontrivially :
    nativeHeightScalar 0 * conj (nativeHeightScalar 0) *
      completedGreenWronskian nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion 0 0 ≠ 0 ∧
    nativeXiCompletionFactor 0 * conj (nativeXiCompletionFactor 0) *
      completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 ≠ 0 ∧
    nativeHeightScalar 0 * conj (nativeHeightScalar 0) *
        completedGreenWronskian nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion 0 0 +
      nativeXiCompletionFactor 0 * conj (nativeXiCompletionFactor 0) *
        completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 = 0 := by
  have hA := nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  have hAc : conj (nativeXiCompletionFactor 0) ≠ 0 := by simpa using hA
  have hnative := mul_ne_zero (mul_ne_zero hA hAc)
    nativeHeightScalar_centerWronskian_ne_zero
  have hcancel := nativeXi_native_centerWronskians_weighted_cancel
  refine ⟨?_, hnative, hcancel⟩
  intro hzero
  rw [hzero, zero_add] at hcancel
  exact hnative hcancel

theorem nativeXi_native_centerNormWeightedWronskians_cancel_nontrivially :
    ((‖nativeHeightScalar 0‖ ^ 2 : ℝ) : ℂ) *
      completedGreenWronskian nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion 0 0 ≠ 0 ∧
    ((‖nativeXiCompletionFactor 0‖ ^ 2 : ℝ) : ℂ) *
      completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 ≠ 0 ∧
    ((‖nativeHeightScalar 0‖ ^ 2 : ℝ) : ℂ) *
        completedGreenWronskian nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion 0 0 +
      ((‖nativeXiCompletionFactor 0‖ ^ 2 : ℝ) : ℂ) *
        completedGreenWronskian nativeHeightScalar nativeHeightScalarBoundaryCompanion 0 0 = 0 := by
  simpa only [Complex.mul_conj, Complex.normSq_eq_norm_sq] using
    nativeXi_native_centerWronskians_cancel_nontrivially

theorem nativeXiCompletionFactor_centerWronskian_ne_zero :
    completedGreenWronskian nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion 0 0 ≠ 0 := by
  intro hzero
  have h := nativeXi_native_centerWronskians_cancel_nontrivially.1
  rw [hzero, mul_zero] at h
  exact h rfl

/-- The completion correction cancels a NONZERO weighted native Green value. -/
theorem nativeArchimedean_centerCorrection_cancel_nontrivially :
    canonicalArchimedeanBoundaryGreenCorrection 0 0 ≠ 0 ∧
    canonicalArchimedeanBoundaryGreenCorrection 0 0 =
      -(conj (nativeXiCompletionFactor 0) * nativeXiCompletionFactor 0 *
        canonicalNativeUndressedGreenForm 0 0) := by
  refine ⟨?_, canonicalArchimedeanBoundaryGreenCorrection_zero_cancel⟩
  rw [canonicalArchimedeanBoundaryGreenCorrection_zero_cancel, neg_ne_zero,
    canonicalNativeUndressedGreenForm_eq_nativeWronskian]
  have hA := nativeXiCompletionFactor_ne_zero zero_mem_completedNativeHeightDomain
  exact mul_ne_zero (mul_ne_zero (by simpa using hA) hA) nativeHeightScalar_centerWronskian_ne_zero

/-- Whole original incident/returned vectors, with the unchanged denominators.
No independent positive-energy replacement of the two channels is made. -/
theorem nativeCoupledCompletion_originalSource_legs (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hs : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hp : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    sourceCompanion k c r = nativeDressedCompanion k c r + completionCompanion k c r ∧
    (∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) • completedNativeRadialChiralCauchyState k i) =
      nativeDressedCompanion k c r + completionCompanion k c r + Complex.I • sourceValue k c r ∧
    (∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1)) • completedNativeRadialChiralMultiplierState k i) =
      nativeDressedCompanion k c r + completionCompanion k c r - Complex.I • sourceValue k c r := by
  refine ⟨sourceCompanion_eq_native_add_completion k c r hs, ?_, ?_⟩
  · rw [incident_synthesis_eq_source k c r hp, sourceCompanion_eq_native_add_completion k c r hs]
  · rw [returned_synthesis_eq_source k c r hp, sourceCompanion_eq_native_add_completion k c r hs]

/-- Independent finite inputs and depths; every ordered physical crossing
keeps both native/product and archimedean factors before contraction. -/
theorem nativeCoupledCompletion_source_polarized_product_sum (k l : ℕ) {N M : ℕ}
    (c : Fin N → ℂ) (d : Fin M → ℂ) (r s : ℝ)
    (hs : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (ht : ∀ j : Fin M, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint l j) ∈ genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let w := fun j : Fin M => canonicalCompletedC3RadialTiltPoint l j
    let a := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    let b := fun j : Fin M => d j * (s : ℂ) ^ ((j : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (w j)
    inner ℂ (sourceValue k c r) (sourceCompanion l d s) -
      inner ℂ (sourceCompanion k c r) (sourceValue l d s) =
      ∑ i, ∑ j, conj (a i) * b j *
        inner ℂ (completedNativeRadialChiralCauchyState k i) (completedNativeRadialChiralCauchyState l j) *
        (conj (nativeXiCompletionFactor (z i)) * nativeXiCompletionFactor (w j) *
          canonicalNativeUndressedGreenForm (z i) (w j) + canonicalArchimedeanBoundaryGreenCorrection (z i) (w j)) := by
  dsimp only
  unfold sourceValue sourceCompanion
  simp only [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection (hs i) (ht j)]
  simp only [canonicalCompletedC3ScalarBoundaryPair, greenForm, RCLike.inner_apply,
    completedNativeOperatorBoundaryCompanion]
  simp only [map_mul, map_neg, div_eq_mul_inv]
  ring

end
end CarrySelfAdjointOperator.GammaMaterialSewing

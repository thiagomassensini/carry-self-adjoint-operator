import CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenFormCrosswalk
import CarrySelfAdjointOperator.NativeBoundaryArchimedeanDressingSeparation

/-!
# Vector completion split of the complete chiral source

Separate the two product-rule companion channels in the existing Cauchy
Hilbert carrier before taking the signed source pairing. The exact TFVD
head/tail readouts provide both native traces at every cutoff. The completion
channel is the existing negative derivative of the xi factor times the native
value, with the unchanged chiral denominator. No moment, positive kernel,
new metric or fitted defect vector defines these channels.
-/

namespace CarrySelfAdjointOperator
open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Both chart-normalized, tail-completed traces are the actual native
companion/value pair, at every cutoff. This does not invert their projection. -/
theorem canonicalC3BracketTfvdNormalizedTracePair_eq_native
    (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalC3BracketTfvdNormalizedLogJetReadout M z,
      canonicalC3BracketTfvdNormalizedValueReadout M z) =
      (nativeHeightScalarBoundaryCompanion z, nativeHeightScalar z) := by
  apply Prod.ext
  · rw [canonicalC3BracketTfvdNormalizedLogJetReadout_eq_cutoff,
      canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout_eq_completed M hz,
      canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion hz]
  · rw [canonicalC3BracketTfvdNormalizedValueReadout_eq_cutoff,
      canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout_eq_completed M hz,
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar hz]

/-- Centered cancellation of the two product-rule companion coefficients.
The factors remain separate; no zeroth moment or sign premise is used. -/
theorem nativeArchimedeanCompanionChannels_zero_cancel :
    nativeXiCompletionFactor 0 * nativeHeightScalarBoundaryCompanion 0 +
      nativeXiCompletionBoundaryCompanion 0 * nativeHeightScalar 0 = 0 := by
  unfold nativeHeightScalarBoundaryCompanion nativeXiCompletionBoundaryCompanion
  have h := nativeCompletionFactor_nativeHeightScalar_firstDerivative_cancel
  linear_combination -h

/-- At the center the archimedean mixed correction cancels the weighted
native Green form. This is an oriented cancellation, not a sum of squares. -/
theorem canonicalArchimedeanBoundaryGreenCorrection_zero_cancel :
    canonicalArchimedeanBoundaryGreenCorrection 0 0 =
      -((starRingEnd ℂ) (nativeXiCompletionFactor 0) *
        nativeXiCompletionFactor 0 * canonicalNativeUndressedGreenForm 0 0) := by
  have hd : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  have h := canonicalCompletedC3ScalarGreenForm_eq_scaledNative_add_archimedeanCorrection
    zero_mem_completedNativeHeightDomain zero_mem_completedNativeHeightDomain
  have hg : greenForm (𝕜 := ℂ)
      (canonicalCompletedC3ScalarBoundaryPair 0)
      (canonicalCompletedC3ScalarBoundaryPair 0) = 0 := by
    simp [canonicalCompletedC3ScalarBoundaryPair, completedNativeOperatorBoundaryCompanion,
      hd, greenForm]
  rw [hg] at h
  linear_combination -h

namespace ChiralReturn
open Filter

/-- Material companion after xi weighting, synthesized before scalarization.
Finite synthesis uses the existing Cauchy vectors and denominator. -/
def nativeDressedCompanion (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
    (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
      nativeHeightScalarBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i)) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)) •
    completedNativeRadialChiralCauchyState k i

/-- Exact companion supplied by the derivative of completion: -A' times Z.
This is a vector channel, not a norm square assigned from a scalar defect. -/
def completionCompanion (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
    (nativeXiCompletionBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i) *
      nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i)) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)) •
    completedNativeRadialChiralCauchyState k i

/-- The value is the product of the unchanged completion factor and native
value, synthesized in the same existing carrier. -/
theorem sourceValue_eq_native_product (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ) :
    sourceValue k c r =
      ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
        (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
          nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i)) /
        completedNativePositiveHermiteBiehlerCoordinate
          (canonicalCompletedC3RadialTiltPoint k i)) •
        completedNativeRadialChiralCauchyState k i := by
  rfl

/-- Exact vector product rule on a regular finite source family. No
nonvanishing denominator is needed for this algebraic split. -/
theorem sourceCompanion_eq_native_add_completion (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    sourceCompanion k c r = nativeDressedCompanion k c r + completionCompanion k c r := by
  unfold sourceCompanion nativeDressedCompanion completionCompanion
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  have hp := completedNativeOperatorBoundaryCompanion_eq_product (hstrip i)
  change -deriv completedNativeOperatorCharacteristic _ = _ at hp
  rw [hp]
  unfold productBoundaryCompanion
  congr 1
  ring

/-- Both separated companions come from the same tail-completed TFVD source
at any cutoff. Nothing is reconstructed from the scalar trace. -/
theorem companion_channels_eq_bracketTfvd (M k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    (nativeDressedCompanion k c r, completionCompanion k c r) =
      (∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
          (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
            canonicalC3BracketTfvdNormalizedLogJetReadout M
              (canonicalCompletedC3RadialTiltPoint k i)) /
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i)) •
          completedNativeRadialChiralCauchyState k i,
       ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) *
          (nativeXiCompletionBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i) *
            canonicalC3BracketTfvdNormalizedValueReadout M
              (canonicalCompletedC3RadialTiltPoint k i)) /
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i)) •
          completedNativeRadialChiralCauchyState k i) := by
  apply Prod.ext
  · dsimp only
    unfold nativeDressedCompanion
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg Prod.fst
      (canonicalC3BracketTfvdNormalizedTracePair_eq_native M (hstrip i))
    dsimp only at h
    rw [h]
  · dsimp only
    unfold completionCompanion
    apply Finset.sum_congr rfl
    intro i _
    have h := congrArg Prod.snd
      (canonicalC3BracketTfvdNormalizedTracePair_eq_native M (hstrip i))
    dsimp only at h
    rw [h]

/-- The completion vector has exactly the existing archimedean Green form
as its polarized skew pairing. Every ordered Cauchy cross term remains. -/
theorem completion_pairing_skew_eq_archimedean_sum (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    inner ℂ (sourceValue k c r) (completionCompanion k c r) -
        inner ℂ (completionCompanion k c r) (sourceValue k c r) =
      ∑ i : Fin N, ∑ j : Fin N,
        star (d i) * d j * inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
          canonicalArchimedeanBoundaryGreenCorrection (z i) (z j) := by
  dsimp only
  have hs := mixed_synthesis_eq_wronskian_sum
    (fun i : Fin N => completedNativeRadialChiralCauchyState k i)
    (fun i => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
      nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => nativeXiCompletionBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i) *
      nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i))
  have hV : (∑ i : Fin N,
      (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) *
        (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
          nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i))) •
          completedNativeRadialChiralCauchyState k i) = sourceValue k c r := by
    rw [sourceValue_eq_native_product]
    simp only [div_mul_eq_mul_div]
  have hC : (∑ i : Fin N,
      (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) *
        (nativeXiCompletionBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i) *
          nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i))) •
          completedNativeRadialChiralCauchyState k i) = completionCompanion k c r := by
    simp only [completionCompanion, div_mul_eq_mul_div]
  rw [hV, hC] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold mixedScalarBoundaryWedge canonicalArchimedeanBoundaryGreenCorrection
  simp only [map_mul, starRingEnd_apply]
  ring

/-- The material companion realizes the weighted native Green form in the
same Cauchy skew pairing. There is no diagonal-only or positive-norm claim. -/
theorem native_pairing_skew_eq_weighted_green_sum (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    inner ℂ (sourceValue k c r) (nativeDressedCompanion k c r) -
        inner ℂ (nativeDressedCompanion k c r) (sourceValue k c r) =
      ∑ i : Fin N, ∑ j : Fin N,
        star (d i) * d j * inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
          ((starRingEnd ℂ) (nativeXiCompletionFactor (z i)) *
            nativeXiCompletionFactor (z j) * canonicalNativeUndressedGreenForm (z i) (z j)) := by
  dsimp only
  have hs := mixed_synthesis_eq_wronskian_sum
    (fun i : Fin N => completedNativeRadialChiralCauchyState k i)
    (fun i => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
      nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i))
    (fun i => nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
      nativeHeightScalarBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i))
  have hV : (∑ i : Fin N,
      (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) *
        (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
          nativeHeightScalar (canonicalCompletedC3RadialTiltPoint k i))) •
          completedNativeRadialChiralCauchyState k i) = sourceValue k c r := by
    rw [sourceValue_eq_native_product]
    simp only [div_mul_eq_mul_div]
  have hC : (∑ i : Fin N,
      (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) *
        (nativeXiCompletionFactor (canonicalCompletedC3RadialTiltPoint k i) *
          nativeHeightScalarBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k i))) •
          completedNativeRadialChiralCauchyState k i) = nativeDressedCompanion k c r := by
    simp only [nativeDressedCompanion, div_mul_eq_mul_div]
  rw [hV, hC] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [canonicalNativeUndressedGreenForm_eq_nativeWronskian]
  unfold mixedScalarBoundaryWedge completedGreenWronskian
  simp only [map_mul, starRingEnd_apply]
  ring

/-- The completed source transports the full product Green form as one
ordered skew sum, preserving both factor channels and every cross term. -/
theorem source_pairing_skew_eq_product_green_sum (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    inner ℂ (sourceValue k c r) (sourceCompanion k c r) -
        inner ℂ (sourceCompanion k c r) (sourceValue k c r) =
      ∑ i : Fin N, ∑ j : Fin N,
        star (d i) * d j * inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
          ((starRingEnd ℂ) (nativeXiCompletionFactor (z i)) *
            nativeXiCompletionFactor (z j) * canonicalNativeUndressedGreenForm (z i) (z j) +
            canonicalArchimedeanBoundaryGreenCorrection (z i) (z j)) := by
  have hn := native_pairing_skew_eq_weighted_green_sum k c r
  have ha := completion_pairing_skew_eq_archimedean_sum k c r
  dsimp only at hn ha ⊢
  rw [sourceCompanion_eq_native_add_completion k c r hstrip,
    inner_add_right, inner_add_left]
  calc
    _ = (inner ℂ (sourceValue k c r) (nativeDressedCompanion k c r) -
        inner ℂ (nativeDressedCompanion k c r) (sourceValue k c r)) +
      (inner ℂ (sourceValue k c r) (completionCompanion k c r) -
        inner ℂ (completionCompanion k c r) (sourceValue k c r)) := by ring
    _ = _ := by
      rw [hn, ha, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The real completion orientation is the imaginary part of its complete
archimedean Green sum; it is not its Hilbert norm or a diagonal-only readout. -/
theorem completion_orientation_eq_archimedean_sum (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ) :
    let z := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i
    let d := fun i : Fin N => c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (z i)
    4 * (inner ℂ (sourceValue k c r) (completionCompanion k c r)).im =
      2 * (∑ i : Fin N, ∑ j : Fin N,
        star (d i) * d j * inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
          canonicalArchimedeanBoundaryGreenCorrection (z i) (z j)).im := by
  have hs := completion_pairing_skew_eq_archimedean_sum k c r
  dsimp only at hs ⊢
  rw [← hs, Complex.sub_im]
  have hconj := congrArg Complex.im
    (inner_conj_symm (sourceValue k c r) (completionCompanion k c r))
  simp only [Complex.conj_im] at hconj
  linarith

/-- The full signed orientation splits only after both vector syntheses.
Their cross terms are retained, with no independent sign asserted. -/
theorem source_cross_eq_native_add_completion (k : ℕ) {N : ℕ}
    (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    4 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im =
      4 * (inner ℂ (sourceValue k c r) (nativeDressedCompanion k c r)).im +
      4 * (inner ℂ (sourceValue k c r) (completionCompanion k c r)).im := by
  rw [sourceCompanion_eq_native_add_completion k c r hstrip, inner_add_right,
    Complex.add_im]
  ring

/-- Uniform finite-family regularity supplies this decomposition for all
coefficients and internal radii, with no new global assumption. -/
theorem sourceCompanion_eventually_eq_native_add_completion (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ, ∀ r : ℝ,
      sourceCompanion k c r = nativeDressedCompanion k c r + completionCompanion k c r := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk c r
  exact sourceCompanion_eq_native_add_completion k c r (fun i => (hk i).1)

/-- Exact accumulated storage in the two source-derived vector orientations.
This equality alone is not a proof of nonnegative storage. -/
theorem storage_eventually_eq_native_add_completion (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin N → ℂ, ∀ r : ℝ,
      (storage k c r).re =
        4 * (inner ℂ (sourceValue k c r) (nativeDressedCompanion k c r)).im +
        4 * (inner ℂ (sourceValue k c r) (completionCompanion k c r)).im := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk c r
  rw [storage_re_eq_source_cross k c r (fun i => (hk i).2.2)]
  exact source_cross_eq_native_add_completion k c r (fun i => (hk i).1)

end ChiralReturn
end
end CarrySelfAdjointOperator

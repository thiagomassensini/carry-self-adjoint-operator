import CarrySelfAdjointOperator.CompletedNativeChiralReturnPolarizedGreen
import CarrySelfAdjointOperator.CompletedC3CoisometricWronskianProjectionGate

/-!
# Testing the existing coisometric split on the complete chiral source

The camera vectors are synthesized before taking a pairing. The radial
Cauchy scale cancels the existing spectral separation exactly. The remaining
term is the already geometric four-channel coisometric/Wronskian discrepancy,
not a complement selected from a target Gram. Its sign or vanishing is not
assumed. The retained Naimark escape has zero boundary readout even after
independent coefficient syntheses.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Infinite Filter
noncomputable section
set_option autoImplicit false

/-- The old radial scale and old Green separation cancel without new weights. -/
theorem radialCauchy_inner_mul_separation (k i j : ℕ) :
    inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) *
      (canonicalCompletedC3RadialTiltPoint k j -
        conj (canonicalCompletedC3RadialTiltPoint k i)) = Complex.I := by
  rw [inner_completedNativeRadialChiralCauchyState,
    ← canonicalCompletedC3RadialTilt_I_div_separation]
  exact div_mul_cancel₀ _ (canonicalCompletedC3RadialTilt_separation_ne_zero k i j)

/-- Geometric camera candidate using the same original source normalization.
Its construction uses no desired coefficient, metric or complementary norm. -/
def coisometricSourceSynthesis (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) : CarryGammaComplexCamera :=
  ∑ i, (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
    completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) •
    canonicalCompletedC3GammaCameraView
      (completedC3SymplecticCameraState
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)) (hhalf i))

/-- Full finite synthesis of the four existing correction channels. This
is not defined by subtracting a newly chosen Gram from the requested target. -/
def coisometricFourChannelBalance (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) : ℂ :=
  ∑ i, ∑ j,
    star (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) *
    (d j * (s : ℂ) ^ ((j : ℕ) + 1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) *
    inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) *
    canonicalCompletedC3CoisometricWronskianFourChannelDefect
      (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) (hhalf i) (hhalf j)

/-- Pointwise sewing keeps the existing completed TFVD Wronskian and the
literal four-channel discrepancy, in the correct left/right orientation. -/
theorem radialBracketWronskian_eq_coisometricGram_sub_defect (M k i j : ℕ)
    (hi : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip)
    (hj : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈
      genuineCriticalStrip) :
    inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) *
      canonicalC3BracketTfvdCompletedWronskianReadout M
        (canonicalCompletedC3RadialTiltPoint k j) (canonicalCompletedC3RadialTiltPoint k i) =
    Complex.I * inner ℂ
      (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)) hi.1))
      (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) hj.1)) -
    inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) *
      canonicalCompletedC3CoisometricWronskianFourChannelDefect
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) hi.1 hj.1 := by
  have hW : canonicalC3BracketTfvdCompletedWronskianReadout M
      (canonicalCompletedC3RadialTiltPoint k j) (canonicalCompletedC3RadialTiltPoint k i) =
      completedGreenWronskian completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion
        (canonicalCompletedC3RadialTiltPoint k j) (canonicalCompletedC3RadialTiltPoint k i) := by
    rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime M hj hi]
    simp only [completedGreenWronskian, completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  rw [hW, canonicalCompletedC3CoisometricWronskianFourChannelDefect_eq_sub
    _ _ (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
    (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) hi hj,
    canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel]
  have hc := radialCauchy_inner_mul_separation k i j
  linear_combination hc * inner ℂ
    (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
      (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)) hi.1))
    (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
      (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) hj.1))

/-- Complete-vector comparison with the actual coisometric camera candidate.
Every ordered cross term and all four geometric correction channels remain. -/
theorem polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance
    (M k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    polarizedSourceBalance k c d r s =
      2 * inner ℂ (coisometricSourceSynthesis k c r (fun i => (hstrip i).1))
        (coisometricSourceSynthesis k d s (fun i => (hstrip i).1)) +
      2 * Complex.I * coisometricFourChannelBalance k c d r s (fun i => (hstrip i).1) := by
  change ∀ i : Fin N, 0 < (operatorHeightParameter
    (canonicalCompletedC3RadialTiltPoint k i)).re ∧
    (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)).re < 1 at hstrip
  rw [polarizedSourceBalance_eq_bracketTfvd_sum M k c d r s hstrip]
  dsimp only
  unfold coisometricSourceSynthesis coisometricFourChannelBalance
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  have hp (i j : Fin N) := radialBracketWronskian_eq_coisometricGram_sub_defect
    M k i j (hstrip i) (hstrip j)
  calc
    _ = -2 * Complex.I * (∑ i : Fin N, ∑ j : Fin N,
        star (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
          completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) *
        (d j * (s : ℂ) ^ ((j : ℕ) + 1) /
          completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) *
        (Complex.I * inner ℂ
          (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
            (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)) (hstrip i).1))
          (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
            (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) (hstrip j).1)) -
        inner ℂ (completedNativeRadialChiralCauchyState k i)
          (completedNativeRadialChiralCauchyState k j) *
        canonicalCompletedC3CoisometricWronskianFourChannelDefect
          (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) (hstrip i).1 (hstrip j).1)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, hp i j]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [starRingEnd_apply]
      ring_nf
      simp [Complex.I_sq]

/-- The camera candidate matches exactly if and only if its synthesized
existing four-channel discrepancy vanishes. No vanishing is supplied. -/
theorem polarizedSourceBalance_eq_coisometricGram_iff_fourChannelBalance_zero
    (M k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip) :
    polarizedSourceBalance k c d r s =
      2 * inner ℂ (coisometricSourceSynthesis k c r (fun i => (hstrip i).1))
        (coisometricSourceSynthesis k d s (fun i => (hstrip i).1)) ↔
      coisometricFourChannelBalance k c d r s (fun i => (hstrip i).1) = 0 := by
  rw [polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance M k c d r s hstrip,
    add_eq_left, mul_eq_zero]
  simp

/-- The actual retained escape is invisible to every complete boundary
pair, even with independent coefficient families and all cross terms. -/
theorem coisometricEscapeBoundarySynthesis_eq_zero (k : ℕ) {N : ℕ}
    (c d : Fin N → ℂ) (r s : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) :
    (∑ i : Fin N, ∑ j : Fin N,
      star (c i * (r : ℂ) ^ ((i : ℕ) + 1) /
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) *
      (d j * (s : ℂ) ^ ((j : ℕ) + 1) /
        completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) *
      inner ℂ (completedNativeRadialChiralCauchyState k i)
        (completedNativeRadialChiralCauchyState k j) *
      canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
        (hhalf i) (hhalf j)) = 0 := by
  simp only [canonicalCompletedC3CoisometricAmbientLeakBoundaryReadout_eq_zero,
    mul_zero, Finset.sum_const_zero]

/-- The diagonal comparison isolates the exact signed correction to the
geometric camera energy. No sign of the correction is provided. -/
theorem storage_re_eq_coisometricEnergy_sub_fourChannelBalance
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c r).re =
      2 * ‖coisometricSourceSynthesis k c r (fun i => (hstrip i).1)‖ ^ 2 -
      2 * (coisometricFourChannelBalance k c c r r (fun i => (hstrip i).1)).im := by
  have h := polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance
    M k c c r r hstrip
  rw [polarizedSourceBalance_self_eq_storage k c r hpositive] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  norm_num [Complex.mul_re, Complex.mul_im] at hr
  change (storage k c r).re =
    2 * ((‖coisometricSourceSynthesis k c r (fun i => (hstrip i).1)‖ : ℂ) ^ 2).re +
    -(2 * (coisometricFourChannelBalance k c c r r (fun i => (hstrip i).1)).im) at hr
  have hreal (x : ℝ) : ((x : ℂ) ^ 2).re = x ^ 2 := by
    rw [← Complex.ofReal_pow]
    rfl
  rw [hreal] at hr
  simpa only [sub_eq_add_neg] using hr

/-- The old shrinking-grid theorem supplies the whole comparison uniformly
in both coefficient families and both internal radii. -/
theorem coisometricSource_comparison_eventually (N : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∃ hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re,
      (∀ c d : Fin N → ℂ, ∀ r s : ℝ,
        polarizedSourceBalance k c d r s =
          2 * inner ℂ (coisometricSourceSynthesis k c r hhalf)
            (coisometricSourceSynthesis k d s hhalf) +
          2 * Complex.I * coisometricFourChannelBalance k c d r s hhalf) ∧
      (∀ c : Fin N → ℂ, ∀ r : ℝ,
        (storage k c r).re = 2 * ‖coisometricSourceSynthesis k c r hhalf‖ ^ 2 -
          2 * (coisometricFourChannelBalance k c c r r hhalf).im) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N]
    with k hk
  let hstrip := fun i : Fin N => (hk i).1
  refine ⟨fun i => (hstrip i).1, ?_, ?_⟩
  · intro c d r s
    exact polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance
      0 k c d r s hstrip
  · intro c r
    exact storage_re_eq_coisometricEnergy_sub_fourChannelBalance
      0 k c r hstrip (fun i => (hk i).2.2)

/-- The completed response itself is in the promoted camera range. Its
escape is zero; this does not erase the induced source's independent leak. -/
theorem coisometricResponse_escape_eq_zero (z : ℂ)
    (hhalf : 0 < (operatorHeightParameter z).re) :
    canonicalCompletedC3AmbientPortEscape
      (completedC3SymplecticNaimarkState (operatorHeightParameter z) hhalf) = 0 := by
  rw [completedC3SymplecticNaimarkState,
    canonicalCompletedC3AmbientPortEscape_apply,
    canonicalCompletedC3AmbientPortProjection_realifiedNaimarkPort, sub_self]

end
end CarrySelfAdjointOperator.ChiralReturn

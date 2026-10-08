import CarrySelfAdjointOperator.CompletedNativeAdjacentClockCorrectedLedger
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixSampleStorage

/-!
# Complete synthesis cancels the three coisometric comparison channels

The Gamma vectors and the raw Gamma--Wronskian discrepancy are upstream
objects. The unchanged completed source weights synthesize both before
readout. The resulting identities hold for arbitrary finite families and
retain every ordered cross. They do not provide an all-order sign premise.
The finite six-sample strict bound reuses the certified actual source storage.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open CPFormal.Analytic.Cp NativeCarrySpectralWeyl.Infinite Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Full Gamma synthesis at the original radial nodes and completed source
weights. No coefficient of a moment sequence enters this vector. -/
def gammaSourceSynthesis (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ) :
    CarryGammaComplexNaimark :=
  ∑ i, (c i * (r : ℂ)^((i : ℕ)+1) /
    completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) •
    canonicalCompletedC3PolarizedGammaState (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)

/-- Complete polarization of the already geometric raw Gamma--Wronskian
channel, with the original Cauchy scale and all source cross terms. -/
def rawGammaWronskianBalance (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ) : ℂ :=
  ∑ i, ∑ j,
    star (c i * (r : ℂ)^((i : ℕ)+1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)) *
    (d j * (s : ℂ)^((j : ℕ)+1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) *
    inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) *
    canonicalCompletedC3RawGammaWronskianDefect
      (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)

/-- The three port/return comparison channels have the same spectral
separation as the unchanged Cauchy features. No strip or sign is needed. -/
theorem radialThreeCorrections_eq_gammaGram_difference (k i j : ℕ)
    (hi : 0 < (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)).re)
    (hj : 0 < (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)).re) :
    inner ℂ (completedNativeRadialChiralCauchyState k i)
      (completedNativeRadialChiralCauchyState k j) *
      canonicalCompletedC3CoisometricThreeBoundaryCorrections
        (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) hi hj =
      Complex.I * (inner ℂ
        (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
          (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)) hi))
        (canonicalCompletedC3GammaCameraView (completedC3SymplecticCameraState
          (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j)) hj)) -
        inner ℂ
          (canonicalCompletedC3PolarizedGammaState (canonicalCompletedC3RadialTiltPoint k i)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i))
          (canonicalCompletedC3PolarizedGammaState (canonicalCompletedC3RadialTiltPoint k j)
            (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j))) := by
  rw [canonicalCompletedC3CoisometricThreeBoundaryCorrections_eq_sub_gamma,
    canonicalCompletedC3CoisometricCompressedBoundaryReadout_eq_kernel,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  unfold canonicalCompletedC3PolarizedGammaKernel
  rw [← mul_sub, ← mul_assoc, radialCauchy_inner_mul_separation]

/-- Exact arbitrary-family reduction: the three coisometric channels are
an energy difference. They cancel after complete synthesis, not term deletion. -/
theorem coisometricFourChannelBalance_eq_rawGamma_add_gram_difference
    (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) :
    coisometricFourChannelBalance k c d r s hhalf =
      rawGammaWronskianBalance k c d r s + Complex.I *
        (inner ℂ (coisometricSourceSynthesis k c r hhalf)
          (coisometricSourceSynthesis k d s hhalf) -
         inner ℂ (gammaSourceSynthesis k c r) (gammaSourceSynthesis k d s)) := by
  unfold coisometricFourChannelBalance rawGammaWronskianBalance
    coisometricSourceSynthesis gammaSourceSynthesis
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  have hp (i j : Fin N) := radialThreeCorrections_eq_gammaGram_difference k i j (hhalf i) (hhalf j)
  simp only [canonicalCompletedC3CoisometricWronskianFourChannelDefect]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  rw [mul_sub]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination
    (star (c i * (r : ℂ)^((i : ℕ)+1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i))) *
    (d j * (s : ℂ)^((j : ℕ)+1) /
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)) * (hp i j)

/-- The same complete source, in every finite order, compared to the full
Gamma synthesis. The raw discrepancy remains explicit and unsigned. -/
theorem polarizedSourceBalance_eq_gammaGram_add_rawGammaBalance
    (M k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (r s : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    polarizedSourceBalance k c d r s =
      2 * inner ℂ (gammaSourceSynthesis k c r) (gammaSourceSynthesis k d s) +
        2 * Complex.I * rawGammaWronskianBalance k c d r s := by
  rw [polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance M k c d r s hstrip,
    coisometricFourChannelBalance_eq_rawGamma_add_gram_difference]
  ring_nf
  simp [Complex.I_sq]

/-- Full source storage is Gamma energy minus one raw signed channel.
This is an all-order identity, not an all-order positivity statement. -/
theorem storage_re_eq_gammaEnergy_sub_rawGammaBalance
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k c r).re = 2 * ‖gammaSourceSynthesis k c r‖^2 -
      2 * (rawGammaWronskianBalance k c c r r).im := by
  have h := polarizedSourceBalance_eq_gammaGram_add_rawGammaBalance M k c c r r hstrip
  rw [polarizedSourceBalance_self_eq_storage k c r hpositive,
    inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow, sub_eq_add_neg] using hr

/-- The requested four-channel energy bound is EXACTLY the raw Gamma bound.
Coisometry has supplied three-channel cancellation, without asserting a sign. -/
theorem coisometricCorrection_le_energy_iff_rawGammaCorrection_le_energy
    (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hhalf : ∀ i : Fin N, 0 < (operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i)).re) :
    (coisometricFourChannelBalance k c c r r hhalf).im ≤
      ‖coisometricSourceSynthesis k c r hhalf‖^2 ↔
      (rawGammaWronskianBalance k c c r r).im ≤ ‖gammaSourceSynthesis k c r‖^2 := by
  have h := congrArg Complex.im
    (coisometricFourChannelBalance_eq_rawGamma_add_gram_difference k c c r r hhalf)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hreal (x : ℝ) : ((x : ℂ)^2).re = x^2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, Complex.sub_re] at h
  change (coisometricFourChannelBalance k c c r r hhalf).im =
    (rawGammaWronskianBalance k c c r r).im +
      ((((‖coisometricSourceSynthesis k c r hhalf‖ : ℝ) : ℂ)^2).re -
       (((‖gammaSourceSynthesis k c r‖ : ℝ) : ℂ)^2).re) at h
  rw [hreal, hreal] at h
  constructor <;> intro hb <;> linarith

/-- The residual energy gap is exactly the mixed orientation of the SAME
completed source vectors, not an unknown camera normalization. -/
theorem rawGammaCorrection_energy_gap_eq_source_cross
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (rawGammaWronskianBalance k c c r r).im - ‖gammaSourceSynthesis k c r‖^2 =
      -2 * (inner ℂ (sourceValue k c r) (sourceCompanion k c r)).im := by
  have h := storage_re_eq_gammaEnergy_sub_rawGammaBalance M k c r hstrip hpositive
  rw [storage_re_eq_source_cross k c r hpositive] at h
  linarith

/-- Cauchy--Schwarz controls the COMPLETE correction gap in arbitrary order.
It gives a two-sided size bound, not the one-sided sign still required. -/
theorem rawGammaCorrection_energy_gap_abs_le_sourceNorms
    (M k : ℕ) {N : ℕ} (c : Fin N → ℂ) (r : ℝ)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hpositive : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    |(rawGammaWronskianBalance k c c r r).im - ‖gammaSourceSynthesis k c r‖^2| ≤
      2 * ‖sourceValue k c r‖ * ‖sourceCompanion k c r‖ := by
  rw [rawGammaCorrection_energy_gap_eq_source_cross M k c r hstrip hpositive, abs_mul]
  norm_num
  have hb := (Complex.abs_im_le_norm
    (inner ℂ (sourceValue k c r) (sourceCompanion k c r))).trans
      (norm_inner_le_norm (sourceValue k c r) (sourceCompanion k c r))
  nlinarith

/-- For each finite order, one radial threshold works simultaneously for
all independent source coefficients and internal radii. No sign is assumed. -/
theorem rawGammaCorrection_comparison_eventually_complete (N : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (∀ c d : Fin N → ℂ, ∀ r s : ℝ,
        polarizedSourceBalance k c d r s =
          2 * inner ℂ (gammaSourceSynthesis k c r) (gammaSourceSynthesis k d s) +
            2 * Complex.I * rawGammaWronskianBalance k c d r s) ∧
      (∀ c : Fin N → ℂ, ∀ r : ℝ,
        (storage k c r).re = 2 * ‖gammaSourceSynthesis k c r‖^2 -
          2 * (rawGammaWronskianBalance k c c r r).im) ∧
      (∀ c : Fin N → ℂ, ∀ r : ℝ,
        |(rawGammaWronskianBalance k c c r r).im - ‖gammaSourceSynthesis k c r‖^2| ≤
          2 * ‖sourceValue k c r‖ * ‖sourceCompanion k c r‖) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hreg
  refine ⟨?_, ?_, ?_⟩
  · intro c d r s
    exact polarizedSourceBalance_eq_gammaGram_add_rawGammaBalance 0 k c d r s
      (fun i => (hreg i).1)
  · intro c r
    exact storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k c r
      (fun i => (hreg i).1) (fun i => (hreg i).2.2)
  · intro c r
    exact rawGammaCorrection_energy_gap_abs_le_sourceNorms 0 k c r
      (fun i => (hreg i).1) (fun i => (hreg i).2.2)

/-- Source-certified strict domination in the full six-node family.
The actual source sign is reused only AFTER the arbitrary-family cancellation. -/
theorem rawGammaCorrection_six_eventually_lt_energy :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin 6 → ℂ, c ≠ 0 →
      (rawGammaWronskianBalance k c c 1 1).im < ‖gammaSourceSynthesis k c 1‖^2 := by
  filter_upwards [storage_one_original_sixSample_eventually_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hk hreg
  intro c hc
  have hs := hk c hc
  rw [storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k c 1
    (fun i => (hreg i).1) (fun i => (hreg i).2.2)] at hs
  linarith

/-- The strict six-node raw-channel bound transfers to the original four
channels, for every half-plane witness of the same radial samples. -/
theorem coisometricCorrection_six_eventually_lt_energy :
    ∀ᶠ k : ℕ in atTop, ∀ hhalf : ∀ i : Fin 6,
      0 < (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i)).re,
      ∀ c : Fin 6 → ℂ, c ≠ 0 →
      (coisometricFourChannelBalance k c c 1 1 hhalf).im <
        ‖coisometricSourceSynthesis k c 1 hhalf‖^2 := by
  filter_upwards [rawGammaCorrection_six_eventually_lt_energy] with k hk
  intro hhalf c hc
  have hp := hk c hc
  have h := congrArg Complex.im
    (coisometricFourChannelBalance_eq_rawGamma_add_gram_difference k c c 1 1 hhalf)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add, Complex.sub_re] at h
  have hreal (x : ℝ) : ((x : ℂ)^2).re = x^2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  change (coisometricFourChannelBalance k c c 1 1 hhalf).im =
    (rawGammaWronskianBalance k c c 1 1).im +
      ((((‖coisometricSourceSynthesis k c 1 hhalf‖ : ℝ) : ℂ)^2).re -
       (((‖gammaSourceSynthesis k c 1‖ : ℝ) : ℂ)^2).re) at h
  rw [hreal, hreal] at h
  linarith

/-- The full source boundary margin gives a quantitative raw-correction
bound in the same six-node geometric chart. Its metric is unchanged. -/
theorem rawGammaCorrection_six_eventually_boundary_margin :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, ∀ d : Fin 6 → ℂ,
      let c := radialCompletedInputCoefficients k d
      (rawGammaWronskianBalance k c c 1 1).im +
        ε * (∑ a : Fin 6, Complex.normSq
          (radialSixScaledBoundary (radialFourSourceStep k) d a)) ≤
        ‖gammaSourceSynthesis k c 1‖^2 := by
  obtain ⟨ε, he, hbound⟩ := storage_one_sixSample_eventually_boundary_coercive
  refine ⟨ε/2, div_pos he (by norm_num), ?_⟩
  filter_upwards [hbound,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 6] with k hk hreg
  intro d
  dsimp only
  have hb := hk d
  rw [storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k _ 1
    (fun i => (hreg i).1) (fun i => (hreg i).2.2)] at hb
  linarith

end
end CarrySelfAdjointOperator.ChiralReturn

import CarrySelfAdjointOperator.CompletedNativeChiralReturnSeventhSourceJet

/-!
# Source-first positivity of the three-boundary cancellation canary

The full four radial samples are retained. Analytic Taylor factorization gives
an exact eighth-order remainder, rather than replacing the source by its
seventh jet. This module proves only this fixed cancellation direction.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- The actual completed source combination on the existing radial grid. -/
def nativeSourceFourSampleCombination (h : ℂ) : ℂ :=
  -Complex.I * (14 * completedNativeOperatorLogDerivative (Complex.I * h) -
    14 * completedNativeOperatorLogDerivative (2 * Complex.I * h) +
    6 * completedNativeOperatorLogDerivative (3 * Complex.I * h) -
    completedNativeOperatorLogDerivative (4 * Complex.I * h))

/-- Exact local factorization: the cancelled lower source jets disappear,
but the entire higher analytic remainder is still present. -/
theorem nativeSourceFourSampleCombination_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      nativeSourceFourSampleCombination h =
        h ^ 7 * iteratedDeriv 7 completedNativeOperatorLogDerivative 0 + h ^ 8 * R h := by
  obtain ⟨G, hGa, hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 8
  let R : ℂ → ℂ := fun h => -Complex.I *
    (14 * G (Complex.I * h) - 3584 * G (2 * Complex.I * h) +
      39366 * G (3 * Complex.I * h) - 65536 * G (4 * Complex.I * h))
  have hg1 : AnalyticAt ℂ (fun h => G (Complex.I * h)) 0 := by
    exact hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hg2 : AnalyticAt ℂ (fun h => G (2 * Complex.I * h)) 0 := by
    exact hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hg3 : AnalyticAt ℂ (fun h => G (3 * Complex.I * h)) 0 := by
    exact hGa.fun_comp_of_eq (by fun_prop) (by simp)
  have hg4 : AnalyticAt ℂ (fun h => G (4 * Complex.I * h)) 0 := by
    exact hGa.fun_comp_of_eq (by fun_prop) (by simp)
  refine ⟨R, ?_, ?_⟩
  · unfold R
    have h1 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (14 : ℂ)) 0).fun_mul hg1
    have h2 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (3584 : ℂ)) 0).fun_mul hg2
    have h3 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (39366 : ℂ)) 0).fun_mul hg3
    have h4 := (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (65536 : ℂ)) 0).fun_mul hg4
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I) 0).fun_mul
      (((h1.fun_sub h2).fun_add h3).fun_sub h4)
  · obtain ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ := nativeSourceLogSlope_center_jets
    have hp (z : ℂ) :
        (∑ i ∈ Finset.range 8, (z ^ i / (i.factorial : ℂ)) •
          iteratedDeriv i completedNativeOperatorLogDerivative 0) =
        z * iteratedDeriv 1 completedNativeOperatorLogDerivative 0 +
        z ^ 3 / 6 * iteratedDeriv 3 completedNativeOperatorLogDerivative 0 +
        z ^ 5 / 120 * iteratedDeriv 5 completedNativeOperatorLogDerivative 0 +
        z ^ 7 / 5040 * iteratedDeriv 7 completedNativeOperatorLogDerivative 0 := by
      norm_num [Finset.sum_range_succ, hq0, hq2, hq4, hq6, smul_eq_mul]
    have ht1 : Tendsto (fun h : ℂ => Complex.I * h) (nhds 0) (nhds 0) := by
      simpa only [id_eq, mul_zero] using
        (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (Complex.I)
    have ht2 : Tendsto (fun h : ℂ => 2 * Complex.I * h) (nhds 0) (nhds 0) := by
      simpa only [id_eq, mul_zero] using
        (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (2 * Complex.I)
    have ht3 : Tendsto (fun h : ℂ => 3 * Complex.I * h) (nhds 0) (nhds 0) := by
      simpa only [id_eq, mul_zero] using
        (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (3 * Complex.I)
    have ht4 : Tendsto (fun h : ℂ => 4 * Complex.I * h) (nhds 0) (nhds 0) := by
      simpa only [id_eq, mul_zero] using
        (tendsto_id : Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul (4 * Complex.I)
    filter_upwards [ht1.eventually hG, ht2.eventually hG,
      ht3.eventually hG, ht4.eventually hG] with h h1 h2 h3 h4
    unfold nativeSourceFourSampleCombination R
    rw [h1, h2, h3, h4]
    simp only [hp]
    simp only [smul_eq_mul]
    ring_nf
    norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
    ring

/-- The normalized ACTUAL source combination has the positive seventh
source derivative as limit; the analytic remainder tends to zero. -/
theorem nativeSourceFourSampleCombination_normalized_tendsto :
    Tendsto (fun k : ℕ => nativeSourceFourSampleCombination (canonicalGreenJetStep k) /
      canonicalGreenJetStep k ^ 7) atTop
      (nhds (iteratedDeriv 7 completedNativeOperatorLogDerivative 0)) := by
  obtain ⟨R, hRa, hR⟩ := nativeSourceFourSampleCombination_exact_remainder
  have ht := canonicalGreenJetStep_tendsto_zero
  have hcont := hRa.continuousAt.tendsto.comp ht
  have hlim : Tendsto (fun k : ℕ => iteratedDeriv 7 completedNativeOperatorLogDerivative 0 +
      canonicalGreenJetStep k * R (canonicalGreenJetStep k)) atTop
      (nhds (iteratedDeriv 7 completedNativeOperatorLogDerivative 0)) := by
    simpa using tendsto_const_nhds.add (ht.mul hcont)
  apply hlim.congr'
  filter_upwards [ht.eventually hR] with k hk
  rw [hk]
  have hs : canonicalGreenJetStep k ≠ 0 := by
    unfold canonicalGreenJetStep
    apply inv_ne_zero
    exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
  field_simp [hs]

/-- Strict eventual sign follows from the upstream integral-derived limit. -/
theorem nativeSourceFourSampleCombination_normalized_eventually_re_pos :
    ∀ᶠ k : ℕ in atTop, 0 <
      (nativeSourceFourSampleCombination (canonicalGreenJetStep k) /
        canonicalGreenJetStep k ^ 7).re := by
  exact Filter.Tendsto.eventually_lt tendsto_const_nhds
    (Complex.continuous_re.continuousAt.tendsto.comp
      nativeSourceFourSampleCombination_normalized_tendsto)
    nativeSourceLogSlope_seventh_derivative_re_pos

open ChiralReturn

/-- These are exactly the four existing radial source samples, with no new
sampling points or normalization choices. -/
theorem nativeSourceFourSampleCombination_eq_radialSlopes (k : ℕ) :
    nativeSourceFourSampleCombination (canonicalGreenJetStep k) =
      14 * radialCompletedSlope k 0 - 14 * radialCompletedSlope k 1 +
        6 * radialCompletedSlope k 2 - radialCompletedSlope k 3 := by
  norm_num [nativeSourceFourSampleCombination, radialCompletedSlope,
    canonicalCompletedC3RadialTiltPoint, canonicalCompletedC3RadialTiltStep, mul_assoc]
  ring

/-- The fixed three-boundary-cancellation direction has strictly positive
FULL storage on sufficiently fine radial grids. This is not the all-family
contractivity gate. -/
theorem storage_one_thirdDifference_eventually_pos :
    ∀ᶠ k : ℕ in atTop, 0 <
      (storage k (radialCompletedInputCoefficients k (![1, -3, 3, -1] : Fin 4 → ℂ)) 1).re := by
  filter_upwards [nativeSourceFourSampleCombination_normalized_eventually_re_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk hreg
  have hs : 0 < (k : ℝ) + 1 := by positivity
  have hr : canonicalGreenJetStep k = ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    unfold canonicalGreenJetStep
    push_cast
    rfl
  have hpow : 0 < (((k : ℝ) + 1)⁻¹) ^ 7 := by positivity
  have hc : 0 < (nativeSourceFourSampleCombination (canonicalGreenJetStep k)).re := by
    have hd : 0 < (nativeSourceFourSampleCombination (canonicalGreenJetStep k)).re /
        (((k : ℝ) + 1)⁻¹) ^ 7 := by
      simpa only [hr, ← Complex.ofReal_pow, Complex.div_ofReal_re] using hk
    exact (div_pos_iff_of_pos_right hpow).mp hd
  rw [storage_one_completed_thirdDifference_eq_four_slopes k
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)]
  have heq := congrArg Complex.re (nativeSourceFourSampleCombination_eq_radialSlopes k)
  norm_num [Complex.mul_re] at heq
  rw [← heq]
  exact mul_pos (div_pos hs (by norm_num)) hc

/-- The exact higher vector remainder carries positive energy on this
nonzero cancellation direction. No source tail has been removed. -/
theorem thirdDifference_exact_remainder_pairing_eventually_pos :
    ∀ᶠ k : ℕ in atTop, 0 <
      (inner ℂ (radialIncidentSynthesis k 4 (![1, -3, 3, -1] : Fin 4 → ℂ))
        (radialCompletedOddSourceRemainderSynthesis k 4 3 (![1, -3, 3, -1] : Fin 4 → ℂ))).re := by
  filter_upwards [storage_one_thirdDifference_eventually_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk hreg
  rw [storage_one_boundary_cancellation_eq_odd_source_remainder k 4 3 _
    thirdDifference_mem_radialBoundaryJetKernel (fun i => (hreg i).2.1)
    (fun i => (hreg i).2.2)] at hk
  linarith

/-- This four-sample three-jet cancellation sector is exactly the line of
the geometric third difference. No change of Hilbert metric is involved. -/
theorem radialBoundaryJetKernel_four_three_characterization (d : Fin 4 → ℂ)
    (hd : d ∈ radialBoundaryJetKernel 4 3) :
    d = d 0 • (![1, -3, 3, -1] : Fin 4 → ℂ) := by
  have h0 := (mem_radialBoundaryJetKernel 4 3 d).mp hd 0 (by omega)
  have h1 := (mem_radialBoundaryJetKernel 4 3 d).mp hd 1 (by omega)
  have h2 := (mem_radialBoundaryJetKernel 4 3 d).mp hd 2 (by omega)
  norm_num [radialEulerBoundaryJet, Fin.sum_univ_succ] at h0 h1 h2
  change d 0 + (d 1 + (d 2 + d 3)) = 0 at h0
  change d 0 + (d 1 * 2 + (d 2 * 3 + d 3 * 4)) = 0 at h1
  change d 0 + (d 1 * 4 + (d 2 * 9 + d 3 * 16)) = 0 at h2
  funext i
  fin_cases i
  · change d 0 = d 0 * 1
    ring
  · change d 1 = d 0 * (-3)
    linear_combination 6 * h0 - (7 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2
  · change d 2 = d 0 * 3
    linear_combination -8 * h0 + 6 * h1 - h2
  · change d 3 = d 0 * (-1)
    linear_combination 3 * h0 - (5 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2

/-- Homogeneity of the ORIGINAL full storage; both coefficient families
and every cross term scale by the same norm square. -/
theorem chiralReturnStorage_smul (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (z : ℂ) (r : ℝ) :
    storage k (z • c) r = (Complex.normSq z : ℂ) * storage k c r := by
  simp only [storage, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum,
    Complex.normSq_eq_conj_mul_self]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Strict positivity holds UNIFORMLY in every nonzero coefficient family
of the whole four-sample, three-jet cancellation sector. Other sectors and
their mixed pairings remain outside this finite result. -/
theorem storage_one_four_sample_cancellation_sector_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ d : Fin 4 → ℂ,
      d ∈ radialBoundaryJetKernel 4 3 → d ≠ 0 →
      0 < (storage k (radialCompletedInputCoefficients k d) 1).re := by
  filter_upwards [storage_one_thirdDifference_eventually_pos] with k hk
  intro d hd hn
  have he := radialBoundaryJetKernel_four_three_characterization d hd
  have hdz : d 0 ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hn he
  have hi : radialCompletedInputCoefficients k d =
      d 0 • radialCompletedInputCoefficients k (![1, -3, 3, -1] : Fin 4 → ℂ) := by
    conv_lhs => rw [he]
    funext i
    simp [radialCompletedInputCoefficients, mul_div_assoc, mul_assoc]
  rw [hi, chiralReturnStorage_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (Complex.normSq_pos.mpr hdz) hk

/-- The exact higher-source vector pairing is positive on the entire same
cancellation sector, with one radial threshold for all its coefficients. -/
theorem four_sample_cancellation_sector_exact_remainder_eventually_pos :
    ∀ᶠ k : ℕ in atTop, ∀ d : Fin 4 → ℂ,
      d ∈ radialBoundaryJetKernel 4 3 → d ≠ 0 →
      0 < (inner ℂ (radialIncidentSynthesis k 4 d)
        (radialCompletedOddSourceRemainderSynthesis k 4 3 d)).re := by
  filter_upwards [storage_one_four_sample_cancellation_sector_eventually_pos,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk hreg
  intro d hd hn
  have hp := hk d hd hn
  rw [storage_one_boundary_cancellation_eq_odd_source_remainder k 4 3 d hd
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)] at hp
  linarith

/-- The leading scale of the FULL native canary is fixed by its actual
Cauchy geometry and seventh source derivative, including remainder control. -/
theorem storage_one_thirdDifference_sixthScale_tendsto :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1)^6 *
      (storage k (radialCompletedInputCoefficients k (![1, -3, 3, -1] : Fin 4 → ℂ)) 1).re)
      atTop (nhds ((iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re / 70)) := by
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp
    nativeSourceFourSampleCombination_normalized_tendsto).div_const (70 : ℝ)
  apply ht.congr'
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hreg
  dsimp only [Function.comp_def]
  rw [storage_one_completed_thirdDifference_eq_four_slopes k
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)]
  have he := congrArg Complex.re (nativeSourceFourSampleCombination_eq_radialSlopes k)
  norm_num [Complex.mul_re] at he
  rw [← he]
  have hr : canonicalGreenJetStep k = ((((k : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by
    unfold canonicalGreenJetStep
    push_cast
    rfl
  rw [hr, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  simp only [inv_pow, div_inv_eq_mul]
  ring

/-- A genuine asymptotic lower bound, with a source-derived margin.
No numerical cutoff or sharp all-family bound is claimed. -/
theorem storage_one_thirdDifference_eventually_source_margin :
    ∀ᶠ k : ℕ in atTop,
      (iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re /
        (140 * ((k : ℝ) + 1)^6) <
      (storage k (radialCompletedInputCoefficients k (![1, -3, 3, -1] : Fin 4 → ℂ)) 1).re := by
  have hp := nativeSourceLogSlope_seventh_derivative_re_pos
  have he := Filter.Tendsto.eventually_lt tendsto_const_nhds
    storage_one_thirdDifference_sixthScale_tendsto
    (show (iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re / 140 <
      (iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re / 70 by linarith)
  filter_upwards [he] with k hk
  have hpow : 0 < ((k : ℝ) + 1)^6 := by positivity
  have hdiv : (iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re /
      (140 * ((k : ℝ) + 1)^6) =
      ((iteratedDeriv 7 completedNativeOperatorLogDerivative 0).re / 140) /
        ((k : ℝ) + 1)^6 := by rw [div_div]
  rw [hdiv]
  exact (div_lt_iff₀ hpow).mpr (by nlinarith)

end
end CarrySelfAdjointOperator

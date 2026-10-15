import CarrySelfAdjointOperator.NativeCompletedSourceReductionChain

/-! The residual from PR #98 has a positive next source scale. Its value is
derived from the source Taylor identity, and its sign from the existing
theta-integral discriminant. This proves a third stage, not all stages. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

private theorem series_coeff_eq_jet
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    p.coeff n = completedGreenTaylorJet f n := by
  rcases hp with ⟨radius, hball⟩
  have hd := hball.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hd
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul] at hd
  have he : (n.factorial : ℂ) • p.coeff n = iteratedDeriv n f 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hd
  rw [completedGreenTaylorJet, ← he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

private theorem jet_dslope {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    completedGreenTaylorJet (dslope f 0) n = completedGreenTaylorJet f (n+1) := by
  rcases hf with ⟨p, hp⟩
  rw [← series_coeff_eq_jet hp.has_fpower_series_dslope_fslope,
    FormalMultilinearSeries.coeff_fslope, series_coeff_eq_jet hp]

private theorem jet_one (f : ℂ → ℂ) : completedGreenTaylorJet f 1 = deriv f 0 := by
  simp [completedGreenTaylorJet, iteratedDeriv_one]

private theorem jet_div_const (f : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    completedGreenTaylorJet (fun z => f z/a) n = completedGreenTaylorJet f n/a := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_div_const]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

private theorem jet_mul_two {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    completedGreenTaylorJet (f*g) 2 =
      f 0*completedGreenTaylorJet g 2 + deriv f 0*deriv g 0 +
        completedGreenTaylorJet f 2*g 0 := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ 2 f 0)
    (hg.contDiffAt : ContDiffAt ℂ 2 g 0)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul]
  ring

private theorem jet_mul_three {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    completedGreenTaylorJet (f*g) 3 =
      f 0*completedGreenTaylorJet g 3 + deriv f 0*completedGreenTaylorJet g 2 +
      completedGreenTaylorJet f 2*deriv g 0 + completedGreenTaylorJet f 3*g 0 := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ 3 f 0)
    (hg.contDiffAt : ContDiffAt ℂ 3 g 0)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul]
  ring

theorem sourceAxis_taylor (n : ℕ) :
    completedGreenTaylorJet sourceAxis n = completedNativeGreenResponseTaylorCoefficient (n+1) := by
  have he : sourceAxis = dslope sourceResponse 0 := funext sourceAxis_eq_dslope
  rw [he, jet_dslope sourceResponse_analyticAt_zero, sourceResponse_taylor]

private theorem axis_reduced_product_germ :
    sourceAxis*reducedResponse =ᶠ[nhds 0]
      (fun z => dslope sourceAxis 0 z/(sourceScale : ℂ)) := by
  filter_upwards [sourceAxis_eventually_ne_zero] with z hz
  change sourceAxis z*(dslope sourceAxis 0 z/((sourceScale : ℂ)*sourceAxis z)) = _
  field_simp

theorem reducedResponse_taylor_two : completedGreenTaylorJet reducedResponse 2 = 0 := by
  have he : completedGreenTaylorJet (sourceAxis*reducedResponse) 2 =
      completedGreenTaylorJet (fun z => dslope sourceAxis 0 z/(sourceScale : ℂ)) 2 := by
    unfold completedGreenTaylorJet
    rw [axis_reduced_product_germ.iteratedDeriv_eq 2]
  rw [jet_mul_two sourceAxis_analyticAt_zero reducedResponse_analyticAt_zero,
    jet_div_const, jet_dslope sourceAxis_analyticAt_zero] at he
  simp only [sourceAxis_taylor] at he
  rw [completedNativeGreenResponseTaylorCoefficient_even_eq_zero 2,
    sourceAxis_zero_eq_scale, deriv_sourceAxis_zero, reducedResponse_zero] at he
  simp only [zero_mul, mul_zero, add_zero, zero_div] at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast sourceScale_pos.ne')

/-- The first new reduced coefficient is extracted through the actual
analytic product equation, before using the source discriminant sign. -/
theorem reducedResponse_taylor_three : completedGreenTaylorJet reducedResponse 3 =
    (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)/(sourceScale : ℂ)^2 -
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)^2/(sourceScale : ℂ)^3 := by
  have he : completedGreenTaylorJet (sourceAxis*reducedResponse) 3 =
      completedGreenTaylorJet (fun z => dslope sourceAxis 0 z/(sourceScale : ℂ)) 3 := by
    unfold completedGreenTaylorJet
    rw [axis_reduced_product_germ.iteratedDeriv_eq 3]
  rw [jet_mul_three sourceAxis_analyticAt_zero reducedResponse_analyticAt_zero,
    jet_div_const, jet_dslope sourceAxis_analyticAt_zero] at he
  simp only [sourceAxis_taylor] at he
  rw [completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 2,
    sourceAxis_zero_eq_scale, deriv_sourceAxis_zero, reducedResponse_zero,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 1,
    reducedResponse_hasDerivAt_zero.deriv] at he
  simp only [zero_mul, mul_zero, add_zero] at he
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  have hs : completedGreenTaylorJet reducedResponse 3 =
      ((canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)/(sourceScale : ℂ) -
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)*
          ((canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)/(sourceScale : ℂ)^2)) /
            (sourceScale : ℂ) := by
    apply (eq_div_iff ha).mpr
    linear_combination he
  rw [hs]
  field_simp

theorem deriv_secondAxis_zero : deriv secondAxis 0 = 0 := by
  calc
    _ = completedGreenTaylorJet secondAxis 1 := (jet_one _).symm
    _ = completedGreenTaylorJet reducedResponse 2 :=
      jet_dslope reducedResponse_analyticAt_zero 1
    _ = 0 := reducedResponse_taylor_two

theorem secondReducedResponse_zero : secondReducedResponse 0 = 0 := by
  simp [secondReducedResponse, dslope_same, deriv_secondAxis_zero]

theorem secondReducedResponse_hasDerivAt_zero :
    HasDerivAt secondReducedResponse
      ((sourceScale*(sourceScale*canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 1^2 : ℝ) : ℂ) 0 := by
  have hD : deriv (dslope secondAxis 0) 0 = completedGreenTaylorJet reducedResponse 3 := by
    rw [← jet_one, jet_dslope secondAxis_analyticAt_zero]
    exact jet_dslope reducedResponse_analyticAt_zero 2
  rcases secondAxis_analyticAt_zero with ⟨p, hp⟩
  have hB := hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt.hasDerivAt
  rw [hD] at hB
  have hA := secondAxis_analyticAt_zero.differentiableAt.hasDerivAt
  have hb : (reducedSourceScale : ℂ) ≠ 0 := by exact_mod_cast reducedSourceScale_pos.ne'
  have hden : (reducedSourceScale : ℂ)*secondAxis 0 ≠ 0 := by
    rw [secondAxis_zero]
    exact mul_ne_zero hb hb
  have h := hB.div (hA.const_mul (reducedSourceScale : ℂ)) hden
  simp only [dslope_same, deriv_secondAxis_zero, secondAxis_zero, mul_zero, sub_zero] at h
  apply h.congr_deriv
  rw [reducedResponse_taylor_three, reducedSourceScale_eq]
  push_cast
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  have hm : (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) ≠ 0 := by
    have hh := nativeSourceMixedLeadingCoefficients_pos.2
    rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
      primeDepthGeometricMoment_eq_canonical] at hh
    exact_mod_cast (show canonicalCompletedNativeLogDerivativeMoment 1 ≠ 0 by linarith)
  field_simp [ha, hm]

theorem chainScale_two_eq : chainScale 2 =
    sourceScale*(sourceScale*canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1^2) /
        canonicalCompletedNativeLogDerivativeMoment 1^2 := by
  rw [chainScale, responseScale, responseAxis, dslope_same]
  rw [chainResponse_two_eq, secondReducedResponse_hasDerivAt_zero.deriv, Complex.ofReal_re]

/-- The NEW channel sign is supplied by the existing source-integral
discriminant, without a desired kernel or moment-positivity premise. -/
theorem chainScale_two_pos : 0 < chainScale 2 := by
  have hd := nativeSourceMixedDiscriminants_pos.1
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at hd
  have hm := nativeSourceMixedLeadingCoefficients_pos.2
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at hm
  have hdelta : 0 < sourceScale*canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1^2 := by
    rw [sourceScale_eq]
    nlinarith
  rw [chainScale_two_eq]
  exact div_pos (mul_pos sourceScale_pos hdelta) (sq_pos_of_pos (by linarith))

theorem chainAxis_two_zero_eq_scale : chainAxis 2 0 = (chainScale 2 : ℂ) := by
  rw [chainAxis, responseAxis, dslope_same]
  rw [chainResponse_two_eq, secondReducedResponse_hasDerivAt_zero.deriv, chainScale_two_eq]

theorem chainAxis_two_analyticAt_zero : AnalyticAt ℂ (chainAxis 2) 0 := by
  rcases secondReducedResponse_analyticAt_zero with ⟨p, hp⟩
  have he : chainAxis 2 = dslope secondReducedResponse 0 := by
    simp only [chainAxis, responseAxis, chainResponse_two_eq]
  rw [he]
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem chainResponse_three_analyticAt_zero : AnalyticAt ℂ (chainResponse 3) 0 := by
  rcases chainAxis_two_analyticAt_zero with ⟨p, hp⟩
  apply hp.has_fpower_series_dslope_fslope.analyticAt.div
    (analyticAt_const.mul chainAxis_two_analyticAt_zero)
  change (chainScale 2 : ℂ)*chainAxis 2 0 ≠ 0
  rw [chainAxis_two_zero_eq_scale]
  exact mul_ne_zero (by exact_mod_cast chainScale_two_pos.ne')
    (by exact_mod_cast chainScale_two_pos.ne')

theorem chain_first_three_centers (j : ℕ) (hj : j < 3) : chainResponse j 0 = 0 := by
  interval_cases j
  · exact sourceResponse_zero
  · rw [chainResponse_one_eq, reducedResponse_zero]
  · rw [chainResponse_two_eq, secondReducedResponse_zero]

theorem chain_first_three_real_scales (j : ℕ) (hj : j < 3) :
    chainAxis j 0 = (chainScale j : ℂ) := by
  interval_cases j
  · rw [chainAxis_zero_eq, chainScale_zero_eq, sourceAxis_zero_eq_scale]
  · rw [chainAxis_one_eq, chainScale_one_eq, secondAxis_zero]
  · exact chainAxis_two_zero_eq_scale

theorem chain_first_three_scales_pos (j : ℕ) (hj : j < 3) : 0 < chainScale j := by
  interval_cases j
  · rw [chainScale_zero_eq]; exact sourceScale_pos
  · rw [chainScale_one_eq]; exact reducedSourceScale_pos
  · exact chainScale_two_pos

/-- Three actual source-derived positive channels, with the complete next
residual, on a source-supplied neighborhood. No all-depth claim occurs. -/
theorem chain_three_positive_channels_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        sourceKernel z w = chainPrefixKernel 3 z w +
          conj (chainWeight 3 z)*chainWeight 3 w*chainKernel 3 z w := by
  have h2 : ∀ᶠ z : ℂ in nhds 0, chainAxis 2 z ≠ 0 := by
    apply chainAxis_two_analyticAt_zero.continuousAt.eventually_ne
    rw [chainAxis_two_zero_eq_scale]
    exact_mod_cast chainScale_two_pos.ne'
  have h1 : ∀ᶠ z : ℂ in nhds 0, secondAxis z ≠ 0 := by
    apply secondAxis_analyticAt_zero.continuousAt.eventually_ne
    rw [secondAxis_zero]
    exact_mod_cast reducedSourceScale_pos.ne'
  rcases mem_nhds_iff.mp (sourceAxis_eventually_ne_zero.and (h1.and h2)) with
    ⟨U, hU, hopen, hzero⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro z hz w hw hsep
  have hreg : ∀ t ∈ U, ∀ j < 3, chainAxis j t ≠ 0 := by
    intro t ht j hj
    interval_cases j
    · rw [chainAxis_zero_eq]; exact (hU ht).1
    · rw [chainAxis_one_eq]; exact (hU ht).2.1
    · exact (hU ht).2.2
  exact chainKernel_prefix 3 chain_first_three_centers chain_first_three_real_scales
    chain_first_three_scales_pos z w (hreg z hz) (hreg w hw) hsep

/-- Native two-input identification on an actual open source neighborhood.
The same -F'/(2F) is retained; only its exact residual is reduced again. -/
theorem nativeKernel_three_positive_channels_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w -
          conj (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z))/(w-conj z) =
          chainPrefixKernel 3 z w +
            conj (chainWeight 3 z)*chainWeight 3 w*chainKernel 3 z w := by
  rcases chain_three_positive_channels_local with ⟨U, hU, h0, hthree⟩
  rcases sourceKernel_eq_native_local with ⟨V, hV, hV0, hnative⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨h0, hV0⟩, ?_⟩
  intro z hz w hw hsep
  rw [← (hnative z hz.2 w hw.2).2.2]
  exact hthree z hz.1 w hw.1 hsep

end
end CarrySelfAdjointOperator.SourcePositiveReduction

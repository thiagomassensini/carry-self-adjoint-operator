import CarrySelfAdjointOperator.NativeCompletedSourceThirdPositiveChannel

/-! A fourth positive channel of the same completed source. Its scale is
extracted from analytic product germs, then signed by the independent theta
certificate. All finite-input crossings and the fourth residual are retained.
No all-stage positivity, infinite limit or physical defect transport is claimed. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

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
      f 0*completedGreenTaylorJet g 2 +
      deriv f 0*deriv g 0 +
      completedGreenTaylorJet f 2*g 0 := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ 2 f 0)
    (hg.contDiffAt : ContDiffAt ℂ 2 g 0)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, Nat.choose]
  ring

private theorem jet_mul_three {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    completedGreenTaylorJet (f*g) 3 =
      f 0*completedGreenTaylorJet g 3 +
      deriv f 0*completedGreenTaylorJet g 2 +
      completedGreenTaylorJet f 2*deriv g 0 +
      completedGreenTaylorJet f 3*g 0 := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ 3 f 0)
    (hg.contDiffAt : ContDiffAt ℂ 3 g 0)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, Nat.choose]
  ring

private theorem jet_mul_four {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    completedGreenTaylorJet (f*g) 4 =
      f 0*completedGreenTaylorJet g 4 +
      deriv f 0*completedGreenTaylorJet g 3 +
      completedGreenTaylorJet f 2*completedGreenTaylorJet g 2 +
      completedGreenTaylorJet f 3*deriv g 0 +
      completedGreenTaylorJet f 4*g 0 := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ 4 f 0)
    (hg.contDiffAt : ContDiffAt ℂ 4 g 0)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, Nat.choose]
  ring

private theorem jet_mul_five {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    completedGreenTaylorJet (f*g) 5 =
      f 0*completedGreenTaylorJet g 5 +
      deriv f 0*completedGreenTaylorJet g 4 +
      completedGreenTaylorJet f 2*completedGreenTaylorJet g 3 +
      completedGreenTaylorJet f 3*completedGreenTaylorJet g 2 +
      completedGreenTaylorJet f 4*deriv g 0 +
      completedGreenTaylorJet f 5*g 0 := by
  unfold completedGreenTaylorJet
  rw [iteratedDeriv_mul (hf.contDiffAt : ContDiffAt ℂ 5 f 0)
    (hg.contDiffAt : ContDiffAt ℂ 5 g 0)]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, Nat.choose]
  ring

private theorem secondAxis_taylor (n : ℕ) :
    completedGreenTaylorJet secondAxis n = completedGreenTaylorJet reducedResponse (n+1) := by
  change completedGreenTaylorJet (dslope reducedResponse 0) n = _
  exact jet_dslope reducedResponse_analyticAt_zero n

private theorem first_product_germ :
    sourceAxis*reducedResponse =ᶠ[nhds 0]
      (fun z => dslope sourceAxis 0 z/(sourceScale : ℂ)) := by
  filter_upwards [sourceAxis_eventually_ne_zero] with z hz
  change sourceAxis z*(dslope sourceAxis 0 z/((sourceScale : ℂ)*sourceAxis z)) = _
  field_simp

private theorem second_product_germ :
    secondAxis*secondReducedResponse =ᶠ[nhds 0]
      (fun z => dslope secondAxis 0 z/(reducedSourceScale : ℂ)) := by
  have hne : ∀ᶠ z : ℂ in nhds 0, secondAxis z ≠ 0 := by
    apply secondAxis_analyticAt_zero.continuousAt.eventually_ne
    rw [secondAxis_zero]
    exact_mod_cast reducedSourceScale_pos.ne'
  filter_upwards [hne] with z hz
  change secondAxis z*(dslope secondAxis 0 z/((reducedSourceScale : ℂ)*secondAxis z)) = _
  field_simp

theorem reducedResponse_taylor_four : completedGreenTaylorJet reducedResponse 4 = 0 := by
  have he : completedGreenTaylorJet (sourceAxis*reducedResponse) 4 =
      completedGreenTaylorJet (fun z => dslope sourceAxis 0 z/(sourceScale : ℂ)) 4 := by
    unfold completedGreenTaylorJet
    rw [first_product_germ.iteratedDeriv_eq 4]
  rw [jet_mul_four sourceAxis_analyticAt_zero reducedResponse_analyticAt_zero,
    jet_div_const, jet_dslope sourceAxis_analyticAt_zero] at he
  simp only [sourceAxis_taylor] at he
  rw [completedNativeGreenResponseTaylorCoefficient_even_eq_zero 2,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero 3,
    sourceAxis_zero_eq_scale, deriv_sourceAxis_zero, reducedResponse_zero,
    reducedResponse_taylor_two] at he
  simp only [zero_mul, mul_zero, add_zero, zero_div] at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast sourceScale_pos.ne')

theorem reducedResponse_taylor_five : completedGreenTaylorJet reducedResponse 5 =
    (m 3 : ℂ)/(sourceScale : ℂ)^2 -
      2*(m 1 : ℂ)*(m 2 : ℂ)/(sourceScale : ℂ)^3 +
      (m 1 : ℂ)^3/(sourceScale : ℂ)^4 := by
  have he : completedGreenTaylorJet (sourceAxis*reducedResponse) 5 =
      completedGreenTaylorJet (fun z => dslope sourceAxis 0 z/(sourceScale : ℂ)) 5 := by
    unfold completedGreenTaylorJet
    rw [first_product_germ.iteratedDeriv_eq 5]
  rw [jet_mul_five sourceAxis_analyticAt_zero reducedResponse_analyticAt_zero,
    jet_div_const, jet_dslope sourceAxis_analyticAt_zero] at he
  simp only [sourceAxis_taylor] at he
  rw [sourceAxis_zero_eq_scale, deriv_sourceAxis_zero, reducedResponse_zero,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero 2,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 1,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 2,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 3,
    reducedResponse_taylor_three, reducedResponse_hasDerivAt_zero.deriv] at he
  simp only [zero_mul, mul_zero, add_zero] at he
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  apply (mul_left_cancel₀ ha)
  field_simp [ha] at he ⊢
  linear_combination he

theorem secondReducedResponse_taylor_two :
    completedGreenTaylorJet secondReducedResponse 2 = 0 := by
  have he : completedGreenTaylorJet (secondAxis*secondReducedResponse) 2 =
      completedGreenTaylorJet (fun z => dslope secondAxis 0 z/(reducedSourceScale : ℂ)) 2 := by
    unfold completedGreenTaylorJet
    rw [second_product_germ.iteratedDeriv_eq 2]
  rw [jet_mul_two secondAxis_analyticAt_zero secondReducedResponse_analyticAt_zero,
    jet_div_const, jet_dslope secondAxis_analyticAt_zero] at he
  simp only [secondAxis_taylor] at he
  rw [reducedResponse_taylor_four] at he
  rw [secondAxis_zero, deriv_secondAxis_zero, secondReducedResponse_zero] at he
  simp only [zero_mul, mul_zero, add_zero, zero_div] at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast reducedSourceScale_pos.ne')

theorem secondReducedResponse_taylor_three :
    completedGreenTaylorJet secondReducedResponse 3 =
      (sourceScale : ℂ)^2*((m 1 : ℂ)*(m 3 : ℂ)-(m 2 : ℂ)^2)/(m 1 : ℂ)^3 := by
  have he : completedGreenTaylorJet (secondAxis*secondReducedResponse) 3 =
      completedGreenTaylorJet (fun z => dslope secondAxis 0 z/(reducedSourceScale : ℂ)) 3 := by
    unfold completedGreenTaylorJet
    rw [second_product_germ.iteratedDeriv_eq 3]
  rw [jet_mul_three secondAxis_analyticAt_zero secondReducedResponse_analyticAt_zero,
    jet_div_const, jet_dslope secondAxis_analyticAt_zero] at he
  simp only [secondAxis_taylor] at he
  rw [reducedResponse_taylor_five] at he
  rw [secondAxis_zero, deriv_secondAxis_zero, secondReducedResponse_zero,
    secondReducedResponse_hasDerivAt_zero.deriv, reducedResponse_taylor_three,
    reducedSourceScale_eq] at he
  simp only [zero_mul, mul_zero, add_zero] at he
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  have hm : (m 1 : ℂ) ≠ 0 := by
    have hh := nativeSourceMixedLeadingCoefficients_pos.2
    rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
      primeDepthGeometricMoment_eq_canonical] at hh
    exact_mod_cast (show m 1 ≠ 0 by linarith)
  push_cast at he
  have hb : (m 1 : ℂ)/(sourceScale : ℂ)^2 ≠ 0 := div_ne_zero hm (pow_ne_zero _ ha)
  apply (mul_left_cancel₀ hb)
  field_simp [ha, hm] at he ⊢
  linear_combination he

theorem nativeMoment_one_pos : 0 < m 1 := by
  have h := nativeSourceMixedLeadingCoefficients_pos.2
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at h
  linarith

theorem nativeMoment_first_discriminant_pos : 0 < m 0*m 2-m 1^2 := by
  have h := nativeSourceMixedDiscriminants_pos.1
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at h
  nlinarith

theorem nativeMoment_shifted_discriminant_pos : 0 < m 1*m 3-m 2^2 := by
  have h := nativeSourceMixedDiscriminants_pos.2
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at h
  nlinarith

theorem deriv_chainAxis_two_zero : deriv (chainAxis 2) 0 = 0 := by
  rw [← jet_one]
  simp only [chainAxis, responseAxis, chainResponse_two_eq]
  rw [jet_dslope secondReducedResponse_analyticAt_zero]
  exact secondReducedResponse_taylor_two

theorem chainResponse_three_zero : chainResponse 3 0 = 0 := by
  change dslope (chainAxis 2) 0 0 / ((chainScale 2 : ℂ)*chainAxis 2 0) = 0
  rw [dslope_same, deriv_chainAxis_two_zero, zero_div]

/-- The fourth scale is the derivative of the already-defined analytic
response. It is not defined by a target moment determinant. -/
theorem chainResponse_three_hasDerivAt_zero :
    HasDerivAt (chainResponse 3) ((m 1*(m 1*m 3-m 2^2)/(m 0*m 2-m 1^2)^2 : ℝ) : ℂ) 0 := by
  have hD : deriv (dslope (chainAxis 2) 0) 0 =
      completedGreenTaylorJet secondReducedResponse 3 := by
    rw [← jet_one, jet_dslope chainAxis_two_analyticAt_zero]
    simp only [chainAxis, responseAxis, chainResponse_two_eq]
    exact jet_dslope secondReducedResponse_analyticAt_zero 2
  rcases chainAxis_two_analyticAt_zero with ⟨p, hp⟩
  have hB := hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt.hasDerivAt
  rw [hD] at hB
  have hA := chainAxis_two_analyticAt_zero.differentiableAt.hasDerivAt
  have hb : (chainScale 2 : ℂ) ≠ 0 := by exact_mod_cast chainScale_two_pos.ne'
  have hden : (chainScale 2 : ℂ)*chainAxis 2 0 ≠ 0 := by
    rw [chainAxis_two_zero_eq_scale]
    exact mul_ne_zero hb hb
  have h := hB.div (hA.const_mul (chainScale 2 : ℂ)) hden
  simp only [dslope_same, deriv_chainAxis_two_zero, chainAxis_two_zero_eq_scale,
    mul_zero, sub_zero] at h
  apply h.congr_deriv
  rw [secondReducedResponse_taylor_three, chainScale_two_eq, sourceScale_eq]
  push_cast
  have hm0 : (m 0 : ℂ) ≠ 0 := by
    have hh := sourceScale_pos
    rw [sourceScale_eq] at hh
    exact_mod_cast hh.ne'
  have hm1 : (m 1 : ℂ) ≠ 0 := by exact_mod_cast nativeMoment_one_pos.ne'
  have hd0 : (m 0 : ℂ)*(m 2 : ℂ)-(m 1 : ℂ)^2 ≠ 0 := by
    exact_mod_cast nativeMoment_first_discriminant_pos.ne'
  field_simp [hm0, hm1, hd0]

theorem chainScale_three_eq : chainScale 3 =
    m 1*(m 1*m 3-m 2^2)/(m 0*m 2-m 1^2)^2 := by
  rw [chainScale, responseScale, responseAxis, dslope_same,
    chainResponse_three_hasDerivAt_zero.deriv, Complex.ofReal_re]

theorem chainScale_three_pos : 0 < chainScale 3 := by
  rw [chainScale_three_eq]
  exact div_pos (mul_pos nativeMoment_one_pos nativeMoment_shifted_discriminant_pos)
    (sq_pos_of_pos nativeMoment_first_discriminant_pos)

theorem chainAxis_three_zero_eq_scale : chainAxis 3 0 = (chainScale 3 : ℂ) := by
  rw [chainAxis, responseAxis, dslope_same, chainResponse_three_hasDerivAt_zero.deriv,
    chainScale_three_eq]

theorem chainAxis_three_analyticAt_zero : AnalyticAt ℂ (chainAxis 3) 0 := by
  rcases chainResponse_three_analyticAt_zero with ⟨p, hp⟩
  exact hp.has_fpower_series_dslope_fslope.analyticAt

theorem chainResponse_four_analyticAt_zero : AnalyticAt ℂ (chainResponse 4) 0 := by
  rcases chainAxis_three_analyticAt_zero with ⟨p, hp⟩
  apply hp.has_fpower_series_dslope_fslope.analyticAt.div
    (analyticAt_const.mul chainAxis_three_analyticAt_zero)
  change (chainScale 3 : ℂ)*chainAxis 3 0 ≠ 0
  rw [chainAxis_three_zero_eq_scale]
  exact mul_ne_zero (by exact_mod_cast chainScale_three_pos.ne')
    (by exact_mod_cast chainScale_three_pos.ne')

theorem chain_first_four_centers (j : ℕ) (hj : j < 4) : chainResponse j 0 = 0 := by
  by_cases h : j < 3
  · exact chain_first_three_centers j h
  · have he : j = 3 := by omega
    subst j
    exact chainResponse_three_zero

theorem chain_first_four_real_scales (j : ℕ) (hj : j < 4) :
    chainAxis j 0 = (chainScale j : ℂ) := by
  by_cases h : j < 3
  · exact chain_first_three_real_scales j h
  · have he : j = 3 := by omega
    subst j
    exact chainAxis_three_zero_eq_scale

theorem chain_first_four_scales_pos (j : ℕ) (hj : j < 4) : 0 < chainScale j := by
  by_cases h : j < 3
  · exact chain_first_three_scales_pos j h
  · have he : j = 3 := by omega
    subst j
    exact chainScale_three_pos

theorem chain_first_four_regular_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ j < 4, chainAxis j z ≠ 0 := by
  have h3 : ∀ᶠ z : ℂ in nhds 0, chainAxis 3 z ≠ 0 := by
    apply chainAxis_three_analyticAt_zero.continuousAt.eventually_ne
    rw [chainAxis_three_zero_eq_scale]
    exact_mod_cast chainScale_three_pos.ne'
  have h2 : ∀ᶠ z : ℂ in nhds 0, chainAxis 2 z ≠ 0 := by
    apply chainAxis_two_analyticAt_zero.continuousAt.eventually_ne
    rw [chainAxis_two_zero_eq_scale]
    exact_mod_cast chainScale_two_pos.ne'
  have h1 : ∀ᶠ z : ℂ in nhds 0, secondAxis z ≠ 0 := by
    apply secondAxis_analyticAt_zero.continuousAt.eventually_ne
    rw [secondAxis_zero]
    exact_mod_cast reducedSourceScale_pos.ne'
  rcases mem_nhds_iff.mp (sourceAxis_eventually_ne_zero.and (h1.and (h2.and h3))) with
    ⟨U, hU, hopen, hzero⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro z hz j hj
  interval_cases j
  · rw [chainAxis_zero_eq]; exact (hU hz).1
  · rw [chainAxis_one_eq]; exact (hU hz).2.1
  · exact (hU hz).2.2.1
  · exact (hU hz).2.2.2

theorem chain_four_positive_channels_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        sourceKernel z w = chainPrefixKernel 4 z w +
          conj (chainWeight 4 z)*chainWeight 4 w*chainKernel 4 z w := by
  rcases chain_first_four_regular_local with ⟨U, hU, h0, hreg⟩
  refine ⟨U, hU, h0, ?_⟩
  intro z hz w hw hsep
  exact chainKernel_prefix 4 chain_first_four_centers chain_first_four_real_scales
    chain_first_four_scales_pos z w (hreg z hz) (hreg w hw) hsep

theorem nativeKernel_four_positive_channels_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w -
          conj (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z))/(w-conj z) =
          chainPrefixKernel 4 z w +
            conj (chainWeight 4 z)*chainWeight 4 w*chainKernel 4 z w := by
  rcases chain_four_positive_channels_local with ⟨U, hU, h0, hfour⟩
  rcases sourceKernel_eq_native_local with ⟨V, hV, hV0, hnative⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨h0, hV0⟩, ?_⟩
  intro z hz w hw hsep
  rw [← (hnative z hz.2 w hw.2).2.2]
  exact hfour z hz.1 w hw.1 hsep

theorem chain_four_channel_finite_energy {N : ℕ}
    (c : Fin N → ℂ) (z : Fin N → ℂ)
    (haxis : ∀ i, ∀ j < 4, chainAxis j (z i) ≠ 0)
    (hsep : ∀ i j, z j ≠ conj (z i)) :
    ∑ i, ∑ j, conj (c i)*c j*chainKernel 0 (z i) (z j) =
      ((∑ k ∈ Finset.range 4, Complex.normSq (∑ i, c i*chainChannel k (z i)) : ℝ) : ℂ) +
        ∑ i, ∑ j, conj (c i*chainWeight 4 (z i))*(c j*chainWeight 4 (z j))*
          chainKernel 4 (z i) (z j) :=
  chainKernel_finite_energy 4 chain_first_four_centers chain_first_four_real_scales
    chain_first_four_scales_pos c z haxis hsep

end
end CarrySelfAdjointOperator.SourcePositiveReduction

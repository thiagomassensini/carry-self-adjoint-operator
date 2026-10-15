import CarrySelfAdjointOperator.NativeCompletedSourcePositiveReduction
import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses

/-! Exact native calibration of the source reduction. Its first reduced
central curvature is positive by the existing theta theorem. This is not
an all-order sign theorem for subsequent reductions. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open DividedVectorResponse Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private abbrev nativeResponse : ℂ → ℂ :=
  completedGreenNormalizedResponse completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion

theorem sourceResponse_eventuallyEq_native : sourceResponse =ᶠ[nhds 0] nativeResponse := by
  filter_upwards [canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed 1]
    with z hz
  exact (sourceVector_readout z).trans hz

/-- The normalization is forced by the original completed characteristic. -/
theorem sourceScale_eq_rawCurvature :
    (sourceScale : ℂ) = -iteratedDeriv 2 completedNativeOperatorCharacteristic 0 /
      (2*completedNativeOperatorCharacteristic 0) := by
  rw [sourceScale_eq]
  exact canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral

theorem sourceResponse_taylor (n : ℕ) :
    completedGreenTaylorJet sourceResponse n = completedNativeGreenResponseTaylorCoefficient n := by
  unfold completedGreenTaylorJet completedNativeGreenResponseTaylorCoefficient
  rw [sourceResponse_eventuallyEq_native.iteratedDeriv_eq n]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

private theorem series_coeff_eq_jet
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ}
    (hs : HasFPowerSeriesAt f series 0) (n : ℕ) :
    series.coeff n = completedGreenTaylorJet f n := by
  rcases hs with ⟨radius, hball⟩
  have hd := hball.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hd
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul] at hd
  have he : (n.factorial : ℂ) • series.coeff n = iteratedDeriv n f 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hd
  rw [completedGreenTaylorJet, ← he, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]

private theorem axis_series {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt sourceResponse p 0) :
    HasFPowerSeriesAt sourceAxis p.fslope 0 := by
  have he : sourceAxis = dslope sourceResponse 0 := funext sourceAxis_eq_dslope
  rw [he]
  exact hp.has_fpower_series_dslope_fslope

theorem deriv_sourceAxis_zero : deriv sourceAxis 0 = 0 := by
  rcases sourceResponse_analyticAt_zero with ⟨p, hp⟩
  rw [(axis_series hp).deriv]
  change p.fslope.coeff 1 = 0
  rw [FormalMultilinearSeries.coeff_fslope,
    series_coeff_eq_jet hp, sourceResponse_taylor]
  exact completedNativeGreenResponseTaylorCoefficient_even_eq_zero 1

theorem reducedResponse_zero : reducedResponse 0 = 0 := by
  simp [reducedResponse, dslope_same, deriv_sourceAxis_zero]

theorem deriv_second_sourceAxis_zero :
    deriv (dslope sourceAxis 0) 0 = (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  rcases sourceResponse_analyticAt_zero with ⟨p, hp⟩
  rw [(axis_series hp).has_fpower_series_dslope_fslope.deriv]
  change p.fslope.fslope.coeff 1 = (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)
  rw [FormalMultilinearSeries.coeff_fslope, FormalMultilinearSeries.coeff_fslope,
    series_coeff_eq_jet hp, sourceResponse_taylor]
  exact completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 1

/-- The reduced response is regular at the center. Its derivative is forced
by the source, with all original factors retained. -/
theorem reducedResponse_hasDerivAt_zero :
    HasDerivAt reducedResponse
      ((canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)/(sourceScale : ℂ)^2) 0 := by
  rcases sourceAxis_analyticAt_zero with ⟨p, hp⟩
  have hB := hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt.hasDerivAt
  rw [deriv_second_sourceAxis_zero] at hB
  have hA := sourceAxis_analyticAt_zero.differentiableAt.hasDerivAt
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  have hD : (sourceScale : ℂ)*sourceAxis 0 ≠ 0 := by
    rw [sourceAxis_zero_eq_scale]
    exact mul_ne_zero ha ha
  have h := hB.div (hA.const_mul (sourceScale : ℂ)) hD
  simp only [dslope_same, deriv_sourceAxis_zero, sourceAxis_zero_eq_scale,
    mul_zero, sub_zero] at h
  apply h.congr_deriv
  field_simp [ha]

/-- A second source scale, not selected to match a desired norm. -/
def reducedSourceScale : ℝ := (deriv reducedResponse 0).re

theorem reducedSourceScale_eq :
    reducedSourceScale = canonicalCompletedNativeLogDerivativeMoment 1 / sourceScale^2 := by
  rw [reducedSourceScale, reducedResponse_hasDerivAt_zero.deriv]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

theorem reducedSourceScale_pos : 0 < reducedSourceScale := by
  have hp := nativeSourceMixedLeadingCoefficients_pos.2
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at hp
  rw [reducedSourceScale_eq]
  exact div_pos (by linarith) (sq_pos_of_pos sourceScale_pos)

/-- Exact source continued-fraction equation. It neither removes a tail nor
postulates a Jacobi/spectral realization. -/
theorem sourceResponse_reconstruction (z : ℂ) (hz : sourceAxis z ≠ 0) :
    sourceResponse z * (1-(sourceScale : ℂ)*z*reducedResponse z) =
      (sourceScale : ℂ)*z := by
  have h := reducedResponse_source_equation z hz
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  have he := sourceResponse_eq_mul_axis z
  field_simp at h
  linear_combination -z*h + he

/-- Source-level comparison on an actual open neighborhood. This is the
original completed response, including completion and chart correction. -/
theorem sourceKernel_eq_native_local :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U,
        sourceAxis z ≠ 0 ∧ sourceAxis w ≠ 0 ∧
          sourceKernel z w = (nativeResponse w-conj (nativeResponse z))/(w-conj z) := by
  rcases mem_nhds_iff.mp
    (sourceResponse_eventuallyEq_native.and sourceAxis_eventually_ne_zero) with
    ⟨U, hU, hopen, hzero⟩
  refine ⟨U, hopen, hzero, ?_⟩
  intro z hz w hw
  refine ⟨(hU hz).2, (hU hw).2, ?_⟩
  simp only [sourceKernel, (hU hz).1, (hU hw).1]

end
end CarrySelfAdjointOperator.SourcePositiveReduction

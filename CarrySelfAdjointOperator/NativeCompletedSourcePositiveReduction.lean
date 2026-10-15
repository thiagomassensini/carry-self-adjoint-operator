import CarrySelfAdjointOperator.NativeCompletedVectorGreenReadout
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! A positive first channel extracted from the completed source itself.
The exact residual is another source response, not a discarded correction.
No moment Gram defines a vector or a metric. All finite source crossings
are kept. Positivity of the reduced kernel is an OPEN question. -/
namespace CarrySelfAdjointOperator.SourcePositiveReduction
open DividedVectorResponse Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Read the completed four-sector source only after its synthesis. -/
def sourceResponse (z : ℂ) : ℂ :=
  primeDepthNormalizedResponseVectorReadout (sourceVector z)

/-- The removable source quotient. Its central value is a derivative. -/
def sourceAxis (z : ℂ) : ℂ :=
  primeDepthNormalizedResponseVectorReadout (response 0 z)

theorem sourceResponse_analyticAt_zero : AnalyticAt ℂ sourceResponse 0 :=
  primeDepthNormalizedResponseVectorReadout.analyticAt _ |>.comp sourceVector_analyticAt_zero

theorem sourceResponse_zero : sourceResponse 0 = 0 := by
  rw [sourceResponse, sourceVector_readout]
  have he := canonicalCompletedC3FullOperatorNormalizedResponse_eventuallyEq_completed 1
  rw [he.eq_of_nhds]
  exact completedNativeGreenNormalizedResponse_zero

theorem sourceAxis_eq_dslope (z : ℂ) :
    sourceAxis z = dslope sourceResponse 0 z := by
  exact (primeDepthNormalizedResponseVectorReadout.dslope_comp sourceVector 0 z
    (fun _ => sourceVector_analyticAt_zero.differentiableAt)).symm

theorem sourceAxis_analyticAt_zero : AnalyticAt ℂ sourceAxis 0 := by
  rcases sourceResponse_analyticAt_zero with ⟨p, hp⟩
  have h := hp.has_fpower_series_dslope_fslope
  have he : sourceAxis = dslope sourceResponse 0 := funext sourceAxis_eq_dslope
  rw [he]
  exact h.analyticAt

/-- The scale is extracted from the source, before its moment identification. -/
def sourceScale : ℝ := (sourceAxis 0).re

theorem sourceAxis_zero :
    sourceAxis 0 = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) :=
  response_center_readout

theorem sourceScale_eq : sourceScale = canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [sourceScale, sourceAxis_zero, Complex.ofReal_re]

theorem sourceScale_pos : 0 < sourceScale := by
  rw [sourceScale_eq]
  exact canonicalCompletedNativeLogDerivativeMoment_zero_pos

theorem sourceAxis_zero_eq_scale : sourceAxis 0 = (sourceScale : ℂ) := by
  rw [sourceAxis_zero, sourceScale_eq]

theorem sourceResponse_eq_mul_axis (z : ℂ) :
    sourceResponse z = z * sourceAxis z := by
  have h := sub_smul_dslope sourceResponse 0 z
  simpa only [sub_zero, sourceResponse_zero, smul_eq_mul, ← sourceAxis_eq_dslope] using h.symm

/-- One scalar Hilbert feature, fixed by the source Schur reduction. -/
def positiveFeature (z : ℂ) : ℂ := sourceAxis z / (Real.sqrt sourceScale : ℂ)

theorem positiveFeature_zero : positiveFeature 0 = (Real.sqrt sourceScale : ℂ) := by
  rw [positiveFeature, sourceAxis_zero_eq_scale]
  have hs : (Real.sqrt sourceScale : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr sourceScale_pos).ne'
  have hsq : (Real.sqrt sourceScale : ℂ)^2 = (sourceScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt sourceScale_pos.le
  rw [← hsq]
  field_simp

theorem positiveFeature_inner (z w : ℂ) :
    inner ℂ (positiveFeature z) (positiveFeature w) =
      conj (sourceAxis z) * sourceAxis w / (sourceScale : ℂ) := by
  have hsq : (Real.sqrt sourceScale : ℂ)^2 = (sourceScale : ℂ) := by
    exact_mod_cast Real.sq_sqrt sourceScale_pos.le
  simp only [positiveFeature, RCLike.inner_apply, map_div₀, Complex.conj_ofReal]
  rw [div_mul_div_comm]
  rw [mul_comm (sourceAxis w), ← pow_two, hsq]

theorem positiveFeature_center_energy : ‖positiveFeature 0‖^2 = sourceScale := by
  rw [positiveFeature_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt sourceScale_pos.le]

/-- A second removable quotient; it is built from the SAME completed source.
Away from zero it is 1/(scale*z) - 1/sourceResponse(z). -/
def reducedResponse (z : ℂ) : ℂ :=
  dslope sourceAxis 0 z / ((sourceScale : ℂ) * sourceAxis z)

theorem reducedResponse_source_equation (z : ℂ) (hz : sourceAxis z ≠ 0) :
    sourceResponse z * reducedResponse z =
      sourceAxis z / (sourceScale : ℂ) - 1 := by
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  have h := sub_smul_dslope sourceAxis 0 z
  simp only [sub_zero, smul_eq_mul, sourceAxis_zero_eq_scale] at h
  rw [sourceResponse_eq_mul_axis, reducedResponse]
  field_simp
  linear_combination h

theorem reducedResponse_analyticAt_zero : AnalyticAt ℂ reducedResponse 0 := by
  rcases sourceAxis_analyticAt_zero with ⟨p, hp⟩
  apply hp.has_fpower_series_dslope_fslope.analyticAt.div
    (analyticAt_const.mul sourceAxis_analyticAt_zero)
  change (sourceScale : ℂ) * sourceAxis 0 ≠ 0
  rw [sourceAxis_zero_eq_scale]
  exact mul_ne_zero (by exact_mod_cast sourceScale_pos.ne')
    (by exact_mod_cast sourceScale_pos.ne')

/-- Actual local regularity comes from the completed source and its positive
central curvature, not from positivity of a desired kernel. -/
theorem sourceAxis_eventually_ne_zero : ∀ᶠ z : ℂ in nhds 0, sourceAxis z ≠ 0 := by
  apply sourceAxis_analyticAt_zero.continuousAt.eventually_ne
  rw [sourceAxis_zero_eq_scale]
  exact_mod_cast sourceScale_pos.ne'

/-- On separated inputs these are the original polarized divided responses. -/
def sourceKernel (z w : ℂ) : ℂ :=
  (sourceResponse w - conj (sourceResponse z)) / (w-conj z)

def reducedKernel (z w : ℂ) : ℂ :=
  (reducedResponse w - conj (reducedResponse z)) / (w-conj z)

/-- Exact numerator identity, including coincident or central inputs.
It retains the complete source correction and every orientation. -/
theorem sourceKernel_numerator_split (z w : ℂ)
    (hz : sourceAxis z ≠ 0) (hw : sourceAxis w ≠ 0) :
    sourceResponse w-conj (sourceResponse z) =
      (w-conj z) * inner ℂ (positiveFeature z) (positiveFeature w) +
        conj (sourceResponse z)*sourceResponse w *
          (reducedResponse w-conj (reducedResponse z)) := by
  have hzw := reducedResponse_source_equation w hw
  have hzz := congrArg conj (reducedResponse_source_equation z hz)
  simp only [map_mul, map_sub, map_div₀, map_one, Complex.conj_ofReal] at hzz
  rw [positiveFeature_inner, sourceResponse_eq_mul_axis w,
    sourceResponse_eq_mul_axis z, map_mul] at *
  linear_combination
    -(conj z * conj (sourceAxis z)) * hzw + (w * sourceAxis w) * hzz

/-- Positive first channel PLUS the unchanged reduced kernel.
The separation hypothesis is essential: division is not a removable diagonal. -/
theorem sourceKernel_split (z w : ℂ)
    (hz : sourceAxis z ≠ 0) (hw : sourceAxis w ≠ 0) (hsep : w ≠ conj z) :
    sourceKernel z w = inner ℂ (positiveFeature z) (positiveFeature w) +
      conj (sourceResponse z)*sourceResponse w*reducedKernel z w := by
  unfold sourceKernel reducedKernel
  rw [sourceKernel_numerator_split z w hz hw]
  field_simp [sub_ne_zero.mpr hsep]

/-- The central row is represented exactly, with the actual removable value
on its central diagonal. No residual is silently set to zero elsewhere. -/
theorem positiveFeature_center_row (w : ℂ) :
    inner ℂ (positiveFeature 0) (positiveFeature w) = sourceAxis w := by
  rw [positiveFeature_inner, sourceAxis_zero_eq_scale, Complex.conj_ofReal]
  have ha : (sourceScale : ℂ) ≠ 0 := by exact_mod_cast sourceScale_pos.ne'
  field_simp

/-- Every ordered crossing of any finite source family is retained. -/
theorem sourceKernel_finite_energy_split {N : ℕ} (c : Fin N → ℂ) (z : Fin N → ℂ)
    (haxis : ∀ i, sourceAxis (z i) ≠ 0)
    (hsep : ∀ i j, z j ≠ conj (z i)) :
    ∑ i, ∑ j, conj (c i)*c j*sourceKernel (z i) (z j) =
      (‖∑ i, c i*positiveFeature (z i)‖^2 : ℂ) +
        ∑ i, ∑ j, conj (c i*sourceResponse (z i))*(c j*sourceResponse (z j))*
          reducedKernel (z i) (z j) := by
  have hGram : (‖∑ i, c i*positiveFeature (z i)‖^2 : ℂ) =
      ∑ i, ∑ j, conj (c i)*c j*inner ℂ (positiveFeature (z i)) (positiveFeature (z j)) := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.inner_apply, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hGram, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceKernel_split _ _ (haxis i) (haxis j) (hsep i j), map_mul]
  ring

end
end CarrySelfAdjointOperator.SourcePositiveReduction

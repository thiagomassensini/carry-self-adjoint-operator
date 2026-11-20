import CarrySelfAdjointOperator.NativeCompletedSourceFourthPositiveChannel
import CarrySelfAdjointOperator.C3GammaCameraTraceObstruction
import Mathlib.Tactic

/-!
# Local parity survives source-based Schur reduction
The source itself, not a fitted measure, is locally odd.
This proves that `chainResponse 4` has a genuine removable center.
-/

namespace CarrySelfAdjointOperator.SourcePositiveReduction
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem dslope_even_of_odd_germ
    (f : ℂ → ℂ) (hfzero : f 0 = 0)
    (hodd : (fun z => f (-z)) =ᶠ[nhds 0] fun z => -f z) :
    (fun z => dslope f 0 (-z)) =ᶠ[nhds 0] (dslope f 0) := by
  filter_upwards [hodd] with z hzodd
  by_cases hz : z = 0
  · simp [hz]
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [dslope_of_ne _ hz, dslope_of_ne _ hnz]
    simp only [slope, sub_zero, vsub_eq_sub, hfzero, hzodd]
    simp [smul_eq_mul]

private theorem deriv_zero_of_even_germ
    (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0)
    (heven : (fun z => f (-z)) =ᶠ[nhds 0] f) :
    deriv f 0 = 0 := by
  have he : deriv (fun z => f (-z)) 0 = deriv f 0 :=
    heven.deriv_eq
  rw [deriv_comp_neg] at he
  simp only [neg_zero] at he
  linear_combination -he / 2

private theorem dslope_odd_of_even_germ
    (f : ℂ → ℂ) (hzero : deriv f 0 = 0)
    (heven : (fun z => f (-z)) =ᶠ[nhds 0] f) :
    (fun z => dslope f 0 (-z)) =ᶠ[nhds 0]
      (fun z => -(dslope f 0 z)) := by
  filter_upwards [heven] with z hzeven
  by_cases hz : z = 0
  · simp [hz, dslope_same, hzero]
  · have hnz : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [dslope_of_ne _ hz, dslope_of_ne _ hnz]
    simp only [slope, sub_zero, vsub_eq_sub, hzeven]
    field_simp [hz]
    ring

/-- A real/complex source reduction sends an analytic odd germ to an odd
germ. It also forces the removable center to be exactly zero. No
positive moment or Schur input is assumed. -/
theorem sourceReduction_preserves_odd_germ
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (hfzero : f 0 = 0)
    (hodd : (fun z => f (-z)) =ᶠ[nhds 0] fun z => -f z) :
    sourceReduction f 0 = 0 ∧
      (fun z => sourceReduction f (-z)) =ᶠ[nhds 0]
        fun z => -sourceReduction f z := by
  let a : ℂ → ℂ := dslope f 0
  have ha : AnalyticAt ℂ a 0 := by
    rcases hf with ⟨p, hp⟩
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  have heven : (fun z => a (-z)) =ᶠ[nhds 0] a :=
    dslope_even_of_odd_germ f hfzero hodd
  have hz : deriv a 0 = 0 := deriv_zero_of_even_germ a ha heven
  have hnum : (fun z => dslope a 0 (-z)) =ᶠ[nhds 0]
      (fun z => -(dslope a 0 z)) :=
    dslope_odd_of_even_germ a hz heven
  constructor
  · change dslope a 0 0 / (↑(responseScale f) * a 0) = 0
    rw [dslope_same, hz, zero_div]
  · filter_upwards [heven, hnum] with z he hn
    change dslope a 0 (-z) / (↑(responseScale f) * a (-z)) =
      -(dslope a 0 z / (↑(responseScale f) * a z))
    rw [he, hn]
    ring


/-- The original completed C3 vector readout is locally odd:
this is inherited from F=A*N, not imposed on the reduction. -/
theorem completedSourceResponse_eventually_odd :
    (fun z => sourceResponse (-z)) =ᶠ[nhds 0]
      (fun z => -sourceResponse z) := by
  let native : ℂ → ℂ :=
    completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion
  have hn : sourceResponse =ᶠ[nhds 0] native :=
    sourceResponse_eventuallyEq_native
  have hc : ContinuousAt (fun z : ℂ => -z) 0 := by fun_prop
  have hneg : Filter.Tendsto (fun z : ℂ => -z) (nhds 0) (nhds 0) := by
    simpa using hc.tendsto
  have hnneg := hneg.eventually hn
  have ho : (fun z => native (-z)) =ᶠ[nhds 0]
      (fun z => -native z) :=
    completedNativeGreenResponse_eventually_odd
  filter_upwards [hn, hnneg, ho] with z hnow hminus hodd
  calc
    sourceResponse (-z) = native (-z) := hminus
    _ = -native z := hodd
    _ = -sourceResponse z := by rw [hnow]

theorem chainResponse_one_odd :
    (fun z => chainResponse 1 (-z)) =ᶠ[nhds 0]
      (fun z => -chainResponse 1 z) := by
  simpa only [chainResponse] using
    (sourceReduction_preserves_odd_germ
      sourceResponse sourceResponse_analyticAt_zero
      sourceResponse_zero completedSourceResponse_eventually_odd).2

theorem chainResponse_two_odd :
    (fun z => chainResponse 2 (-z)) =ᶠ[nhds 0]
      (fun z => -chainResponse 2 z) := by
  have hzero : chainResponse 1 0 = 0 := by
    rw [chainResponse_one_eq]
    exact reducedResponse_zero
  have ha : AnalyticAt ℂ (chainResponse 1) 0 := by
    rw [chainResponse_one_eq]
    exact reducedResponse_analyticAt_zero
  exact (sourceReduction_preserves_odd_germ
    (chainResponse 1) ha hzero chainResponse_one_odd).2

theorem chainResponse_three_odd :
    (fun z => chainResponse 3 (-z)) =ᶠ[nhds 0]
      (fun z => -chainResponse 3 z) := by
  have hzero : chainResponse 2 0 = 0 := by
    rw [chainResponse_two_eq]
    exact secondReducedResponse_zero
  have ha : AnalyticAt ℂ (chainResponse 2) 0 := by
    rw [chainResponse_two_eq]
    exact secondReducedResponse_analyticAt_zero
  exact (sourceReduction_preserves_odd_germ
    (chainResponse 2) ha hzero chainResponse_two_odd).2

/-- Source-level new result: stage four has zero constant term
independently of the positivity of its future Schur coefficient. -/
theorem chainResponse_four_zero :
    chainResponse 4 0 = 0 :=
  (sourceReduction_preserves_odd_germ
    (chainResponse 3) chainResponse_three_analyticAt_zero
    chainResponse_three_zero chainResponse_three_odd).1

theorem chainResponse_four_odd :
    (fun z => chainResponse 4 (-z)) =ᶠ[nhds 0]
      (fun z => -chainResponse 4 z) :=
  (sourceReduction_preserves_odd_germ
    (chainResponse 3) chainResponse_three_analyticAt_zero
    chainResponse_three_zero chainResponse_three_odd).2

/-- Every four-stage frequency factor is source-derived, and the
fifth candidate's analytic axis has an actual removable center. -/
theorem chainAxis_four_analyticAt_zero :
    AnalyticAt ℂ (chainAxis 4) 0 := by
  rcases chainResponse_four_analyticAt_zero with ⟨p, hp⟩
  exact hp.has_fpower_series_dslope_fslope.analyticAt


/-- All first five stages of the native source chain vanish at the center. -/
theorem chain_first_five_centers (j : ℕ) (hj : j < 5) :
    chainResponse j 0 = 0 := by
  by_cases h : j < 4
  · exact chain_first_four_centers j h
  · have he : j = 4 := by omega
    subst j
    exact chainResponse_four_zero

/-- The fifth remainder is forced to order five in each spectral leg,
without requiring any sign for the fifth source scale. -/
theorem chainWeight_five_exact_factor (z : ℂ) :
    chainWeight 5 z =
      z ^ 5 * ∏ j ∈ Finset.range 5, chainAxis j z :=
  chainWeight_factor 5 chain_first_five_centers z

/-- The real part of the fifth source axis is its actual source scale. -/
theorem chainAxis_four_realPart_eq_scale :
    (chainAxis 4 0).re = chainScale 4 := rfl

/-- A positive *source-derived* fifth scale makes its actual analytic
axis nonzero at the center, even before proving that the axis is real. -/
theorem chainAxis_four_center_ne_zero_of_scale_pos
    (hscale : 0 < chainScale 4) :
    chainAxis 4 0 ≠ 0 := by
  intro he
  have hh := chainAxis_four_realPart_eq_scale
  rw [he] at hh
  simp only [Complex.zero_re] at hh
  linarith

/-- Under the explicit fifth-scale sign, the NEXT source response is
analytic; no artificial extension or synthetic moment vector is used. -/
theorem chainResponse_five_analyticAt_zero_of_scale_pos
    (hscale : 0 < chainScale 4) :
    AnalyticAt ℂ (chainResponse 5) 0 := by
  rcases chainAxis_four_analyticAt_zero with ⟨p, hp⟩
  apply hp.has_fpower_series_dslope_fslope.analyticAt.div
    (analyticAt_const.mul chainAxis_four_analyticAt_zero)
  change (chainScale 4 : ℂ) * chainAxis 4 0 ≠ 0
  exact mul_ne_zero (by exact_mod_cast hscale.ne')
    (chainAxis_four_center_ne_zero_of_scale_pos hscale)

theorem chainResponse_five_zero :
    chainResponse 5 0 = 0 :=
  (sourceReduction_preserves_odd_germ
    (chainResponse 4) chainResponse_four_analyticAt_zero
    chainResponse_four_zero chainResponse_four_odd).1

end
end CarrySelfAdjointOperator.SourcePositiveReduction

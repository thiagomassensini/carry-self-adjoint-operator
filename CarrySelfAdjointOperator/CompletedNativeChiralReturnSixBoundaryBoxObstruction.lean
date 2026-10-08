import CarrySelfAdjointOperator.CompletedNativeChiralReturnSixBoundaryFace

/-!
# Exact obstruction to reusing the previous independent theta enclosure

This rational tuple belongs to the old six integral intervals and has
positive raw Xi entries and positive previous mixed numerator, but negative
new mixed numerator. It is NOT the actual theta source, a source state,
a fitted carrier or a counterexample to canonical storage positivity.
-/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The previous interval information and positivity of the new theta
entry do not determine the next odd boundary sign. -/
theorem nativeSourcePreviousThetaBox_does_not_force_sixOddSign :
    ∃ t0 t2 t4 t6 t8 t10 t12 : ℝ,
      ((11516610847649/1000000000000000:ℝ) ≤ t0 ∧ t0 ≤ (5758542847001/500000000000000:ℝ)) ∧
      ((61829866593/250000000000000:ℝ) ≤ t2 ∧ t2 ≤ (61830753323/250000000000000:ℝ)) ∧
      ((25000511/1250000000000:ℝ) ≤ t4 ∧ t4 ≤ (10000374553/500000000000000:ℝ)) ∧
      ((1438505521/500000000000000:ℝ) ≤ t6 ∧ t6 ≤ (575423539/200000000000000:ℝ)) ∧
      ((18429291/31250000000000:ℝ) ≤ t8 ∧ t8 ≤ (589803117/1000000000000000:ℝ)) ∧
      ((0/1:ℝ) ≤ t10 ∧ t10 ≤ (31050931/200000000000000:ℝ)) ∧
      0 < t12 ∧
      0 < (1/2-t0/4) ∧
      0 < (2*t0-t2/4) ∧
      0 < (12*t2-t4/4) ∧
      0 < (30*t4-t6/4) ∧
      0 < (56*t6-t8/4) ∧
      0 < (90*t8-t10/4) ∧
      0 < (132*t10-t12/4) ∧
      0 < nativeSourceTenthMixedNumerator (1/2-t0/4) (2*t0-t2/4) (12*t2-t4/4) (30*t4-t6/4) (56*t6-t8/4) (90*t8-t10/4) ∧
      nativeSourceTwelfthMixedNumerator (1/2-t0/4) (2*t0-t2/4) (12*t2-t4/4) (30*t4-t6/4) (56*t6-t8/4) (90*t8-t10/4) (132*t10-t12/4) < 0 := by
  refine ⟨(23033696541651/2000000000000000:ℝ), (30915154979/125000000000000:ℝ), (20000578953/1000000000000000:ℝ), (5754128737/2000000000000000:ℝ), (1179540429/2000000000000000:ℝ), (31050931/200000000000000:ℝ), (1/100000000000000:ℝ), ?_⟩
  norm_num [nativeSourceTenthMixedNumerator, nativeSourceTwelfthMixedNumerator]

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaTenth_node_3584 :
    (34169/125000000000000:ℝ) ≤ thetaFirstMode (1/1:ℝ) ∧
      thetaFirstMode (1/1:ℝ) ≤ (273353/1000000000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (1/1:ℝ) ∧
      thetaSecondMode (1/1:ℝ) ≤ (1/1000000000000000:ℝ) := by
  have hfirst : (34169/125000000000000:ℝ) ≤ thetaFirstMode (1/1:ℝ) ∧
      thetaFirstMode (1/1:ℝ) ≤ (273353/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/1:ℝ) (147781121978613/20000000000000:ℝ) (7389056098930651/1000000000000000:ℝ)
      (34169/125000000000000:ℝ) (273353/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (1/1:ℝ) ∧
      thetaSecondMode (1/1:ℝ) ≤ (1/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/1:ℝ) (147781121978613/20000000000000:ℝ) (7389056098930651/1000000000000000:ℝ)
      (0/1:ℝ) (1/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

end
end CarrySelfAdjointOperator

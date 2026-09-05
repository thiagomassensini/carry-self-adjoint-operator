import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds

namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000

theorem thetaFirstMode_node_512 :
    (273/1000000000000:ℝ) ≤ thetaFirstMode (1/1:ℝ) ∧ thetaFirstMode (1/1:ℝ) ≤ (137/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/1:ℝ) (73890560989/10000000000:ℝ) (7389056099/1000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

end CarrySelfAdjointOperator

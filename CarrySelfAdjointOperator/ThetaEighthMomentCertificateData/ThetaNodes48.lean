import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds

namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000

theorem thetaFirstMode_refined_node_1536 :
    (5467/20000000000000:ℝ) ≤ thetaFirstMode (1/1:ℝ) ∧ thetaFirstMode (1/1:ℝ) ≤ (3417/12500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/1:ℝ) (738905609893/100000000000:ℝ) (7389056098931/1000000000000:ℝ) (5467/20000000000000:ℝ) (3417/12500000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

end CarrySelfAdjointOperator

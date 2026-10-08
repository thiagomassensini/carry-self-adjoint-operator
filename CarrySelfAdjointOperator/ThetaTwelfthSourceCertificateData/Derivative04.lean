import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0128 :
    (-5761776608913551036264339930467/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (83/512:ℝ) ∧ thetaFirstModeFirst (83/512:ℝ) ≤ (-360110418415211111719267/1562500000000000000000000:ℝ) := by
  have hlo : (2172332005089/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(83/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(83/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(83/512:ℝ)) ≤ (691474897151/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(83/512:ℝ)) (by norm_num : 2*(83/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(83/512:ℝ)) ≤ (2172332696565301543/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (83/512:ℝ) (2172332005089/500000000000:ℝ) (2172332696565301543/500000000000000000:ℝ) (175892536003/6250000000000:ℝ) (2814284468069/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0247).1 (thetaFirstMode_refined_node_0247).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0129 :
    (-5759584812271629765978533442441/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (32917849303728807/202980990606108160:ℝ) ∧ thetaFirstModeFirst (32917849303728807/202980990606108160:ℝ) ≤ (-719946862598563970324289/3125000000000000000000000:ℝ) := by
  have hlo : (2172604451261/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(32917849303728807/202980990606108160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(32917849303728807/202980990606108160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(32917849303728807/202980990606108160:ℝ)) ≤ (691561619479/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(32917849303728807/202980990606108160:ℝ)) (by norm_num : 2*(32917849303728807/202980990606108160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(32917849303728807/202980990606108160:ℝ)) ≤ (2172605142823890047/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (32917849303728807/202980990606108160:ℝ) (2172604451261/500000000000:ℝ) (2172605142823890047/500000000000000000:ℝ) (351604462549/12500000000000:ℝ) (2812839590903/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0251).1 (thetaFirstMode_refined_node_0251).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0130 :
    (-5693710515581249436465745500623/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21/128:ℝ) ∧ thetaFirstModeFirst (21/128:ℝ) ≤ (-2846850344036210012360517/12500000000000000000000000:ℝ) := by
  have hlo : (2180834272163/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21/128:ℝ)) ≤ (1388362506757/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21/128:ℝ)) (by norm_num : 2*(21/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21/128:ℝ)) ≤ (4361669932690243901/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21/128:ℝ) (2180834272163/500000000000:ℝ) (4361669932690243901/1000000000000000000:ℝ) (1384766458359/50000000000000:ℝ) (1384768380923/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0252).1 (thetaFirstMode_refined_node_0252).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0131 :
    (-562606852677076569099959116451/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (85/512:ℝ) ∧ thetaFirstModeFirst (85/512:ℝ) ≤ (-2250423514356939893987757/10000000000000000000000000:ℝ) := by
  have hlo : (4378739632339/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(85/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(85/512:ℝ)) ≤ (139379640397/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(85/512:ℝ)) (by norm_num : 2*(85/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(85/512:ℝ)) ≤ (437874102613732421/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (85/512:ℝ) (4378739632339/1000000000000:ℝ) (437874102613732421/100000000000000000:ℝ) (545063073663/20000000000000:ℝ) (1362659583431/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0253).1 (thetaFirstMode_refined_node_0253).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0132 :
    (-11247909633159162109304544626363/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8156311544891565/49111668780733952:ℝ) ∧ thetaFirstModeFirst (8156311544891565/49111668780733952:ℝ) ≤ (-11247890156825530945542183/50000000000000000000000000:ℝ) := by
  have hlo : (4379275894543/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(8156311544891565/49111668780733952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8156311544891565/49111668780733952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8156311544891565/49111668780733952:ℝ)) ≤ (1393967101567/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8156311544891565/49111668780733952:ℝ)) (by norm_num : 2*(8156311544891565/49111668780733952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8156311544891565/49111668780733952:ℝ)) ≤ (4379277288513176231/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8156311544891565/49111668780733952:ℝ) (4379275894543/1000000000000:ℝ) (4379277288513176231/1000000000000000000:ℝ) (2723937669481/100000000000000:ℝ) (2723941466573/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0257).1 (thetaFirstMode_refined_node_0257).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0133 :
    (-2223541304891261386854239462981/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (43/256:ℝ) ∧ thetaFirstModeFirst (43/256:ℝ) ≤ (-347427725490423663772503/1562500000000000000000000:ℝ) := by
  have hlo : (2197938767351/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(43/256:ℝ)) ≤ (279850313771/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(43/256:ℝ)) (by norm_num : 2*(43/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(43/256:ℝ)) ≤ (879175786790777203/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (43/256:ℝ) (2197938767351/500000000000:ℝ) (879175786790777203/200000000000000000:ℝ) (167601537953/6250000000000:ℝ) (2681628359527/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0258).1 (thetaFirstMode_refined_node_0258).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0134 :
    (-1373016817501124793119945563793/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (87/512:ℝ) ∧ thetaFirstModeFirst (87/512:ℝ) ≤ (-10726675199165057979899/48828125000000000000000:ℝ) := by
  have hlo : (4413082512917/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(87/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(87/512:ℝ)) ≤ (351182021163/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(87/512:ℝ)) (by norm_num : 2*(87/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(87/512:ℝ)) ≤ (1103270979411532659/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (87/512:ℝ) (4413082512917/1000000000000:ℝ) (1103270979411532659/250000000000000000:ℝ) (2576618447/97656250000:ℝ) (1319230498027/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0259).1 (thetaFirstMode_refined_node_0259).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0135 :
    (-1372507094811860412583584941229/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (50272907626205343/295754822586012160:ℝ) ∧ thetaFirstModeFirst (50272907626205343/295754822586012160:ℝ) ≤ (-1098003762770462553442177/5000000000000000000000000:ℝ) := by
  have hlo : (441361057281/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(50272907626205343/295754822586012160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(50272907626205343/295754822586012160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(50272907626205343/295754822586012160:ℝ)) ≤ (351224042843/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(50272907626205343/295754822586012160:ℝ)) (by norm_num : 2*(50272907626205343/295754822586012160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(50272907626205343/295754822586012160:ℝ)) ≤ (1103402994427268899/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (50272907626205343/295754822586012160:ℝ) (441361057281/100000000000:ℝ) (1103402994427268899/250000000000000000:ℝ) (2637143276417/100000000000000:ℝ) (1318573490671/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0263).1 (thetaFirstMode_refined_node_0263).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0136 :
    (-5425713026250097947953973193683/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11/64:ℝ) ∧ thetaFirstModeFirst (11/64:ℝ) ≤ (-2712851772206397561434961/12500000000000000000000000:ℝ) := by
  have hlo : (2215177414757/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11/64:ℝ)) ≤ (705113017463/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11/64:ℝ)) (by norm_num : 2*(11/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11/64:ℝ)) ≤ (2215178119870638559/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11/64:ℝ) (2215177414757/500000000000:ℝ) (2215178119870638559/500000000000000000:ℝ) (1297905026173/50000000000000:ℝ) (2595813713037/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0264).1 (thetaFirstMode_refined_node_0264).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0137 :
    (-2679896467491864574072049939417/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (89/512:ℝ) ∧ thetaFirstModeFirst (89/512:ℝ) ≤ (-669972942398000957144817/3125000000000000000000000:ℝ) := by
  have hlo : (2223847374023/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(89/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(89/512:ℝ)) ≤ (1415745503569/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(89/512:ℝ)) (by norm_num : 2*(89/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(89/512:ℝ)) ≤ (4447696163793845417/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (89/512:ℝ) (2223847374023/500000000000:ℝ) (4447696163793845417/1000000000000000000:ℝ) (319209939079/12500000000000:ℝ) (638420782001/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0265).1 (thetaFirstMode_refined_node_0265).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0138 :
    (-10715651598204005518805144426309/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (61679411798377041/354710535855669760:ℝ) ∧ thetaFirstModeFirst (61679411798377041/354710535855669760:ℝ) ≤ (-5357816405875069874886099/25000000000000000000000000:ℝ) := by
  have hlo : (2224107502471/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(61679411798377041/354710535855669760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61679411798377041/354710535855669760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(61679411798377041/354710535855669760:ℝ)) ≤ (1415911106517/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(61679411798377041/354710535855669760:ℝ)) (by norm_num : 2*(61679411798377041/354710535855669760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(61679411798377041/354710535855669760:ℝ)) ≤ (4448216420856061581/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (61679411798377041/354710535855669760:ℝ) (2224107502471/500000000000:ℝ) (4448216420856061581/1000000000000000000:ℝ) (2552425923669/100000000000000:ℝ) (2552429537689/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0269).1 (thetaFirstMode_refined_node_0269).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0139 :
    (-10588618655822651373377582342077/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (45/256:ℝ) ∧ thetaFirstModeFirst (45/256:ℝ) ≤ (-10588600035970063929092317/50000000000000000000000000:ℝ) := by
  have hlo : (4465102533101/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(45/256:ℝ)) ≤ (1421286574801/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(45/256:ℝ)) (by norm_num : 2*(45/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(45/256:ℝ)) ≤ (4465103954388797993/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (45/256:ℝ) (4465102533101/1000000000000:ℝ) (4465103954388797993/1000000000000000000:ℝ) (2512062269617/100000000000000:ℝ) (2512065839989/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0270).1 (thetaFirstMode_refined_node_0270).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0140 :
    (-5229264464220805941873707183149/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (91/512:ℝ) ∧ thetaFirstModeFirst (91/512:ℝ) ≤ (-104585104799884434452673/500000000000000000000000:ℝ) := by
  have hlo : (44825784503/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(91/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(91/512:ℝ)) ≤ (1426849333173/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(91/512:ℝ)) (by norm_num : 2*(91/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(91/512:ℝ)) ≤ (4482579877150964589/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (91/512:ℝ) (44825784503/10000000000:ℝ) (4482579877150964589/1000000000000000000:ℝ) (2470954904391/100000000000000:ℝ) (1235479215041/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0271).1 (thetaFirstMode_refined_node_0271).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0141 :
    (-2613683101637881345539804340327/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (75331067100848559/423704371432783360:ℝ) ∧ thetaFirstModeFirst (75331067100848559/423704371432783360:ℝ) ≤ (-5227356981553553106799291/25000000000000000000000000:ℝ) := by
  have hlo : (4483091277497/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(75331067100848559/423704371432783360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75331067100848559/423704371432783360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(75331067100848559/423704371432783360:ℝ)) ≤ (713506285587/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(75331067100848559/423704371432783360:ℝ)) (by norm_num : 2*(75331067100848559/423704371432783360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(75331067100848559/423704371432783360:ℝ)) ≤ (2241546352256120091/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (75331067100848559/423704371432783360:ℝ) (4483091277497/1000000000000:ℝ) (2241546352256120091/500000000000000000:ℝ) (1234879344403/50000000000000:ℝ) (1234881106597/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0275).1 (thetaFirstMode_refined_node_0275).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0142 :
    (-2582330265224662741602061841233/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23/128:ℝ) ∧ thetaFirstModeFirst (23/128:ℝ) ≤ (-1032930278347655037052001/5000000000000000000000000:ℝ) := by
  have hlo : (900024553261/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23/128:ℝ)) ≤ (716216931783/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23/128:ℝ)) (by norm_num : 2*(23/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23/128:ℝ)) ≤ (2250062099370950319/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23/128:ℝ) (900024553261/200000000000:ℝ) (2250062099370950319/500000000000000000:ℝ) (1215176990341/50000000000000:ℝ) (1215178731007/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0276).1 (thetaFirstMode_refined_node_0276).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0143 :
    (-1275124910085750686642879321289/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (93/512:ℝ) ∧ thetaFirstModeFirst (93/512:ℝ) ≤ (-10200981173921390980686851/50000000000000000000000000:ℝ) := by
  have hlo : (4517735748821/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(93/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(93/512:ℝ)) ≤ (179755031399/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(93/512:ℝ)) (by norm_num : 2*(93/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(93/512:ℝ)) ≤ (564717148357878607/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (93/512:ℝ) (4517735748821/1000000000000:ℝ) (564717148357878607/125000000000000000:ℝ) (2390256045431/100000000000000:ℝ) (2390259482727/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0277).1 (thetaFirstMode_refined_node_0277).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0144 :
    (-1019733508622841471817190211/5000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (91605462777481257/504167194710300160:ℝ) ∧ thetaFirstModeFirst (91605462777481257/504167194710300160:ℝ) ≤ (-1019731698435172028731617/5000000000000000000000000:ℝ) := by
  have hlo : (903648299167/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(91605462777481257/504167194710300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91605462777481257/504167194710300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(91605462777481257/504167194710300160:ℝ)) ≤ (2876402471/2000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(91605462777481257/504167194710300160:ℝ)) (by norm_num : 2*(91605462777481257/504167194710300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(91605462777481257/504167194710300160:ℝ)) ≤ (9036485868076303/2000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (91605462777481257/504167194710300160:ℝ) (903648299167/200000000000:ℝ) (9036485868076303/2000000000000000:ℝ) (1194557172351/50000000000000:ℝ) (119455889037/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0281).1 (thetaFirstMode_refined_node_0281).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0145 :
    (-10073567669361363370601205553991/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (47/256:ℝ) ∧ thetaFirstModeFirst (47/256:ℝ) ≤ (-1259193716609016058996233/6250000000000000000000000:ℝ) := by
  have hlo : (2267708833301/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(47/256:ℝ)) ≤ (1443668581599/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(47/256:ℝ)) (by norm_num : 2*(47/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(47/256:ℝ)) ≤ (4535419110271347207/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (47/256:ℝ) (2267708833301/500000000000:ℝ) (4535419110271347207/1000000000000000000:ℝ) (587664407333/25000000000000:ℝ) (2350661022913/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0282).1 (thetaFirstMode_refined_node_0282).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0146 :
    (-9947030162445663752188109956389/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (95/512:ℝ) ∧ thetaFirstModeFirst (95/512:ℝ) ≤ (-99470123958132555901611/500000000000000000000000:ℝ) := by
  have hlo : (1138292197363/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(95/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(95/512:ℝ)) ≤ (1449318940669/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(95/512:ℝ)) (by norm_num : 2*(95/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(95/512:ℝ)) ≤ (4553170238773145717/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (95/512:ℝ) (1138292197363/250000000000:ℝ) (4553170238773145717/1000000000000000000:ℝ) (92462209897/4000000000000:ℝ) (2311558597617/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0283).1 (thetaFirstMode_refined_node_0283).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0147 :
    (-2485873295490302234156004147927/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (22186673770886955/119539193595863552:ℝ) ∧ thetaFirstModeFirst (22186673770886955/119539193595863552:ℝ) ≤ (-4971737710048177139068927/25000000000000000000000000:ℝ) := by
  have hlo : (2276833892007/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(22186673770886955/119539193595863552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(22186673770886955/119539193595863552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(22186673770886955/119539193595863552:ℝ)) ≤ (362369443901/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(22186673770886955/119539193595863552:ℝ)) (by norm_num : 2*(22186673770886955/119539193595863552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(22186673770886955/119539193595863552:ℝ)) ≤ (1138417308373274293/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (22186673770886955/119539193595863552:ℝ) (2276833892007/500000000000:ℝ) (1138417308373274293/250000000000000000:ℝ) (2310465379561/100000000000000:ℝ) (2310468728539/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0287).1 (thetaFirstMode_refined_node_0287).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0148 :
    (-24553476373019469343849424389/125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/16:ℝ) ∧ thetaFirstModeFirst (3/16:ℝ) ≤ (-9821372952020047948247809/50000000000000000000000000:ℝ) := by
  have hlo : (4570989388233/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/16:ℝ)) ≤ (1454991414619/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/16:ℝ)) (by norm_num : 2*(3/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/16:ℝ)) ≤ (4570990843227148067/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/16:ℝ) (4570989388233/1000000000000:ℝ) (4570990843227148067/1000000000000000000:ℝ) (2272945399673/100000000000000:ℝ) (5682371767/250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0288).1 (thetaFirstMode_refined_node_0288).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0149 :
    (-484832623625435136497041351833/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (97/512:ℝ) ∧ thetaFirstModeFirst (97/512:ℝ) ≤ (-969663504433780707057507/5000000000000000000000000:ℝ) := by
  have hlo : (917775946973/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(97/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(97/512:ℝ)) ≤ (365171522501/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(97/512:ℝ)) (by norm_num : 2*(97/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(97/512:ℝ)) ≤ (1147220298888484093/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (97/512:ℝ) (917775946973/200000000000:ℝ) (1147220298888484093/250000000000000000:ℝ) (1117412285759/50000000000000:ℝ) (446965567181/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0289).1 (thetaFirstMode_refined_node_0289).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0150 :
    (-2423309469003666491290107722139/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (133804837701602793/706068831528348160:ℝ) ∧ thetaFirstModeFirst (133804837701602793/706068831528348160:ℝ) ≤ (-2423305113119570236802301/12500000000000000000000000:ℝ) := by
  have hlo : (2294686142357/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(133804837701602793/706068831528348160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(133804837701602793/706068831528348160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(133804837701602793/706068831528348160:ℝ)) ≤ (1460842873523/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(133804837701602793/706068831528348160:ℝ)) (by norm_num : 2*(133804837701602793/706068831528348160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(133804837701602793/706068831528348160:ℝ)) ≤ (4589373745559742139/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (133804837701602793/706068831528348160:ℝ) (2294686142357/500000000000:ℝ) (4589373745559742139/1000000000000000000:ℝ) (1116892008393/50000000000000:ℝ) (558446820001/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0293).1 (thetaFirstMode_refined_node_0293).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0151 :
    (-478640971434709097493736141841/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (49/256:ℝ) ∧ thetaFirstModeFirst (49/256:ℝ) ≤ (-957280216909008531871797/5000000000000000000000000:ℝ) := by
  have hlo : (2303420051167/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(49/256:ℝ)) ≤ (733201526859/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(49/256:ℝ)) (by norm_num : 2*(49/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(49/256:ℝ)) ≤ (2303420784369546387/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (49/256:ℝ) (2303420051167/500000000000:ℝ) (2303420784369546387/500000000000000000:ℝ) (439437846891/20000000000000:ℝ) (219719245643/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0294).1 (thetaFirstMode_refined_node_0294).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0152 :
    (-1181236845937298032390968093279/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (99/512:ℝ) ∧ thetaFirstModeFirst (99/512:ℝ) ≤ (-1181234709499861645374897/6250000000000000000000000:ℝ) := by
  have hlo : (2312435382347/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(99/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(99/512:ℝ)) ≤ (368035598249/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(99/512:ℝ)) (by norm_num : 2*(99/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(99/512:ℝ)) ≤ (1156218059209870657/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (99/512:ℝ) (2312435382347/500000000000:ℝ) (1156218059209870657/250000000000000000:ℝ) (540008961651/25000000000000:ℝ) (1080019513247/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0295).1 (thetaFirstMode_refined_node_0295).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0153 :
    (-1889319597122152687153954521623/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (160775853321491991/831261189349250560:ℝ) ∧ thetaFirstModeFirst (160775853321491991/831261189349250560:ℝ) ≤ (-1180822612328989692599391/6250000000000000000000000:ℝ) := by
  have hlo : (578169644899/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(160775853321491991/831261189349250560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(160775853321491991/831261189349250560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(160775853321491991/831261189349250560:ℝ)) ≤ (294459443441/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(160775853321491991/831261189349250560:ℝ)) (by norm_num : 2*(160775853321491991/831261189349250560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(160775853321491991/831261189349250560:ℝ)) ≤ (925071726298141513/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (160775853321491991/831261189349250560:ℝ) (578169644899/125000000000:ℝ) (925071726298141513/200000000000000000:ℝ) (2159042234709/100000000000000:ℝ) (2159045413471/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0299).1 (thetaFirstMode_refined_node_0299).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0154 :
    (-582992605756223555107765103111/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (25/128:ℝ) ∧ thetaFirstModeFirst (25/128:ℝ) ≤ (-4663932384116234802339221/25000000000000000000000000:ℝ) := by
  have hlo : (4642971997071/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(25/128:ℝ)) ≤ (369476048853/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(25/128:ℝ)) (by norm_num : 2*(25/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(25/128:ℝ)) ≤ (1160743368744242829/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (25/128:ℝ) (4642971997071/1000000000000:ℝ) (1160743368744242829/250000000000000000:ℝ) (1061680426651/50000000000000:ℝ) (530840997859/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0300).1 (thetaFirstMode_refined_node_0300).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0155 :
    (-920678325897132643988088934431/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (101/512:ℝ) ∧ thetaFirstModeFirst (101/512:ℝ) ≤ (-9206766502248011088955491/50000000000000000000000000:ℝ) := by
  have hlo : (4661144075669/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(101/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(101/512:ℝ)) ≤ (741844274443/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(101/512:ℝ)) (by norm_num : 2*(101/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(101/512:ℝ)) ≤ (2330572779680207699/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (101/512:ℝ) (4661144075669/1000000000000:ℝ) (2330572779680207699/500000000000000000:ℝ) (2087160687639/100000000000000:ℝ) (417432756869/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0301).1 (thetaFirstMode_refined_node_0301).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0156 :
    (-575224997641594188646699268061/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (192475564448517009/975462843111554560:ℝ) ∧ thetaFirstModeFirst (192475564448517009/975462843111554560:ℝ) ≤ (-9203583209948288183516109/50000000000000000000000000:ℝ) := by
  have hlo : (4661624587249/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(192475564448517009/975462843111554560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(192475564448517009/975462843111554560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(192475564448517009/975462843111554560:ℝ)) ≤ (185480187563/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(192475564448517009/975462843111554560:ℝ)) (by norm_num : 2*(192475564448517009/975462843111554560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(192475564448517009/975462843111554560:ℝ)) ≤ (582703258886607859/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (192475564448517009/975462843111554560:ℝ) (4661624587249/1000000000000:ℝ) (582703258886607859/125000000000000000:ℝ) (2086211786141/100000000000000:ℝ) (1043107440879/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0305).1 (thetaFirstMode_refined_node_0305).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0157 :
    (-9086602378078348879272635627313/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (51/256:ℝ) ∧ thetaFirstModeFirst (51/256:ℝ) ≤ (-9086585787997117959162741/50000000000000000000000000:ℝ) := by
  have hlo : (4679387277771/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(51/256:ℝ)) ≤ (1489495541679/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(51/256:ℝ)) (by norm_num : 2*(51/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(51/256:ℝ)) ≤ (4679388767269954647/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (51/256:ℝ) (4679387277771/1000000000000:ℝ) (4679388767269954647/1000000000000000000:ℝ) (2051431771071/100000000000000:ℝ) (2051434826679/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0306).1 (thetaFirstMode_refined_node_0306).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0158 :
    (-1793468362567391087674201617927/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (103/512:ℝ) ∧ thetaFirstModeFirst (103/512:ℝ) ≤ (-560457836805157194420567/3125000000000000000000000:ℝ) := by
  have hlo : (1174425470437/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(103/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(103/512:ℝ)) ≤ (1495325262399/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(103/512:ℝ)) (by norm_num : 2*(103/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(103/512:ℝ)) ≤ (4697703377075861607/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (103/512:ℝ) (1174425470437/250000000000:ℝ) (4697703377075861607/1000000000000000000:ℝ) (504042628491/25000000000000:ℝ) (403234705761/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0307).1 (thetaFirstMode_refined_node_0307).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0159 :
    (-22410669733251202917470933647/125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (229614139092996207/1141096218995868160:ℝ) ∧ thetaFirstModeFirst (229614139092996207/1141096218995868160:ℝ) ≤ (-2241062868410695775947257/12500000000000000000000000:ℝ) := by
  have hlo : (2349088383617/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(229614139092996207/1141096218995868160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(229614139092996207/1141096218995868160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(229614139092996207/1141096218995868160:ℝ)) ≤ (59819056927/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(229614139092996207/1141096218995868160:ℝ)) (by norm_num : 2*(229614139092996207/1141096218995868160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(229614139092996207/1141096218995868160:ℝ)) ≤ (187927130508464711/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (229614139092996207/1141096218995868160:ℝ) (2349088383617/500000000000:ℝ) (187927130508464711/40000000000000000:ℝ) (1007632108921/50000000000000:ℝ) (125954201977/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0311).1 (thetaFirstMode_refined_node_0311).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0640 :
    (-174104208624903533746519401/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (53/64:ℝ) ∧ thetaFirstModeFirst (53/64:ℝ) ≤ (-21762903542189345523/3125000000000000000000000:ℝ) := by
  have hlo : (16460765120659/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(53/64:ℝ)) ≤ (5239625362129/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(53/64:ℝ)) (by norm_num : 2*(53/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(53/64:ℝ)) ≤ (16460770360286931497/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (53/64:ℝ) (16460765120659/1000000000000:ℝ) (16460770360286931497/1000000000000000000:ℝ) (1342497/6250000000000:ℝ) (10740033/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1272).1 (thetaFirstMode_refined_node_1272).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0641 :
    (-328100025216610487790481939/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (425/512:ℝ) ∧ thetaFirstModeFirst (425/512:ℝ) ≤ (-82024544432356675749/12500000000000000000000000:ℝ) := by
  have hlo : (8262595366883/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(425/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(425/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(425/512:ℝ)) ≤ (5260132675971/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(425/512:ℝ)) (by norm_num : 2*(425/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(425/512:ℝ)) ≤ (16525195993901761803/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (425/512:ℝ) (8262595366883/500000000000:ℝ) (16525195993901761803/1000000000000000000:ℝ) (10079703/50000000000000:ℝ) (20159513/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1273).1 (thetaFirstMode_refined_node_1273).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0642 :
    (-327977334446131963136579723/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15904930171669675505325/19160480067509209098752:ℝ) ∧ thetaFirstModeFirst (15904930171669675505325/19160480067509209098752:ℝ) ≤ (-40996935869417980983/6250000000000000000000000:ℝ) := by
  have hlo : (4131398939101/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(15904930171669675505325/19160480067509209098752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15904930171669675505325/19160480067509209098752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15904930171669675505325/19160480067509209098752:ℝ)) ≤ (5260261598707/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15904930171669675505325/19160480067509209098752:ℝ)) (by norm_num : 2*(15904930171669675505325/19160480067509209098752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15904930171669675505325/19160480067509209098752:ℝ)) ≤ (16525601016666720251/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15904930171669675505325/19160480067509209098752:ℝ) (4131398939101/250000000000:ℝ) (16525601016666720251/1000000000000000000:ℝ) (10075683/50000000000000:ℝ) (20151473/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1277).1 (thetaFirstMode_refined_node_1277).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0643 :
    (-247259872036157049454863/40000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (213/256:ℝ) ∧ thetaFirstModeFirst (213/256:ℝ) ≤ (-154536544915800515741/25000000000000000000000000:ℝ) := by
  have hlo : (16589868501593/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(213/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(213/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(213/256:ℝ)) ≤ (528072025317/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(213/256:ℝ)) (by norm_num : 2*(213/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(213/256:ℝ)) ≤ (1658987378231709981/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (213/256:ℝ) (16589868501593/1000000000000:ℝ) (1658987378231709981/100000000000000000:ℝ) (9457637/50000000000000:ℝ) (151323/800000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1278).1 (thetaFirstMode_refined_node_1278).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0644 :
    (-145539539470016339467656953/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (427/512:ℝ) ∧ thetaFirstModeFirst (427/512:ℝ) ≤ (-145538713209367669413/25000000000000000000000000:ℝ) := by
  have hlo : (8327399705523/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(427/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(427/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(427/512:ℝ)) ≤ (5301388407867/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(427/512:ℝ)) (by norm_num : 2*(427/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(427/512:ℝ)) ≤ (16654804712436112131/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (427/512:ℝ) (8327399705523/500000000000:ℝ) (16654804712436112131/1000000000000000000:ℝ) (17743431/100000000000000:ℝ) (8871763/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1279).1 (thetaFirstMode_refined_node_1279).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0645 :
    (-58193965464152993522552829/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (82956802885821125866143/99468997421790285852160:ℝ) ∧ thetaFirstModeFirst (82956802885821125866143/99468997421790285852160:ℝ) ≤ (-3637102184952230609/625000000000000000000000:ℝ) := by
  have hlo : (832760284923/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(82956802885821125866143/99468997421790285852160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(82956802885821125866143/99468997421790285852160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(82956802885821125866143/99468997421790285852160:ℝ)) ≤ (1060303546639/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(82956802885821125866143/99468997421790285852160:ℝ)) (by norm_num : 2*(82956802885821125866143/99468997421790285852160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(82956802885821125866143/99468997421790285852160:ℝ)) ≤ (3331042199996255927/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (82956802885821125866143/99468997421790285852160:ℝ) (832760284923/50000000000:ℝ) (3331042199996255927/200000000000000000:ℝ) (4434083/25000000000000:ℝ) (17736427/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1283).1 (thetaFirstMode_refined_node_1283).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0646 :
    (-54812280789211738978874777/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (107/128:ℝ) ∧ thetaFirstModeFirst (107/128:ℝ) ≤ (-274059833086808045601/50000000000000000000000000:ℝ) := by
  have hlo : (16719984452893/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(107/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(107/128:ℝ)) ≤ (1064427491087/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(107/128:ℝ)) (by norm_num : 2*(107/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(107/128:ℝ)) ≤ (3343997955006481591/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (107/128:ℝ) (16719984452893/1000000000000:ℝ) (3343997955006481591/200000000000000000:ℝ) (16639957/100000000000000:ℝ) (16640047/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1284).1 (thetaFirstMode_refined_node_1284).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0647 :
    (-257972764926647850930564011/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (429/512:ℝ) ∧ thetaFirstModeFirst (429/512:ℝ) ≤ (-32246409507344621121/6250000000000000000000000:ℝ) := by
  have hlo : (16785424621781/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(429/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(429/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(429/512:ℝ)) ≤ (5342967712479/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(429/512:ℝ)) (by norm_num : 2*(429/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(429/512:ℝ)) ≤ (16785429964750039047/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (429/512:ℝ) (16785424621781/1000000000000:ℝ) (16785429964750039047/1000000000000000000:ℝ) (1950141/12500000000000:ℝ) (15601213/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1285).1 (thetaFirstMode_refined_node_1285).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0648 :
    (-10315022379513419488123/2000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (86519996812935046058841/103257800780870084584960:ℝ) ∧ thetaFirstModeFirst (86519996812935046058841/103257800780870084584960:ℝ) ≤ (-6446852178814216519/1250000000000000000000000:ℝ) := by
  have hlo : (839291609343/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(86519996812935046058841/103257800780870084584960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(86519996812935046058841/103257800780870084584960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(86519996812935046058841/103257800780870084584960:ℝ)) ≤ (10686194889/2000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(86519996812935046058841/103257800780870084584960:ℝ)) (by norm_num : 2*(86519996812935046058841/103257800780870084584960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(86519996812935046058841/103257800780870084584960:ℝ)) ≤ (33571675059918177/2000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (86519996812935046058841/103257800780870084584960:ℝ) (839291609343/50000000000:ℝ) (33571675059918177/2000000000000000:ℝ) (7797433/50000000000000:ℝ) (311899/2000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1289).1 (thetaFirstMode_refined_node_1289).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0649 :
    (-60691588585704853893634901/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (215/256:ℝ) ∧ thetaFirstModeFirst (215/256:ℝ) ≤ (-30345618476813427117/6250000000000000000000000:ℝ) := by
  have hlo : (2106390114531/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(215/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(215/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(215/256:ℝ)) ≤ (1340969874211/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(215/256:ℝ)) (by norm_num : 2*(215/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(215/256:ℝ)) ≤ (4212781570032158123/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (215/256:ℝ) (2106390114531/125000000000:ℝ) (4212781570032158123/250000000000000000:ℝ) (14623407/100000000000000:ℝ) (14623487/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1290).1 (thetaFirstMode_refined_node_1290).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0650 :
    (-228397510330448227443162237/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (431/512:ℝ) ∧ thetaFirstModeFirst (431/512:ℝ) ≤ (-57099046627044903519/12500000000000000000000000:ℝ) := by
  have hlo : (16917074338741/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(431/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(431/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(431/512:ℝ)) ≤ (5384873127619/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(431/512:ℝ)) (by norm_num : 2*(431/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(431/512:ℝ)) ≤ (16917079723615957067/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (431/512:ℝ) (16917074338741/1000000000000:ℝ) (16917079723615957067/1000000000000000000:ℝ) (3425859/25000000000000:ℝ) (13703511/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1291).1 (thetaFirstMode_refined_node_1291).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0651 :
    (-28538890652579743145831737/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (90218589795601773832359/107172285154106278812160:ℝ) ∧ thetaFirstModeFirst (90218589795601773832359/107172285154106278812160:ℝ) ≤ (-228309801395635387713/50000000000000000000000000:ℝ) := by
  have hlo : (16917483194389/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(90218589795601773832359/107172285154106278812160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(90218589795601773832359/107172285154106278812160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(90218589795601773832359/107172285154106278812160:ℝ)) ≤ (5385003270441/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(90218589795601773832359/107172285154106278812160:ℝ)) (by norm_num : 2*(90218589795601773832359/107172285154106278812160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(90218589795601773832359/107172285154106278812160:ℝ)) ≤ (16917488579394552513/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (90218589795601773832359/107172285154106278812160:ℝ) (16917483194389/1000000000000:ℝ) (16917488579394552513/1000000000000000000:ℝ) (13697917/100000000000000:ℝ) (1712249/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1295).1 (thetaFirstMode_refined_node_1295).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0652 :
    (-107411808429493455517427491/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (27/32:ℝ) ∧ thetaFirstModeFirst (27/32:ℝ) ≤ (-6713198731048653201/1562500000000000000000000:ℝ) := by
  have hlo : (1061455368477/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(27/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(27/32:ℝ)) ≤ (2702974462571/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(27/32:ℝ)) (by norm_num : 2*(27/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(27/32:ℝ)) ≤ (8491645650791815603/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (27/32:ℝ) (1061455368477/62500000000:ℝ) (8491645650791815603/500000000000000000:ℝ) (6419013/50000000000000:ℝ) (12838097/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1296).1 (thetaFirstMode_refined_node_1296).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0653 :
    (-10100201726413400226760369/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (433/512:ℝ) ∧ thetaFirstModeFirst (433/512:ℝ) ≤ (-101001430243798734633/25000000000000000000000000:ℝ) := by
  have hlo : (17049756597229/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(433/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(433/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(433/512:ℝ)) ≤ (5427107211003/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(433/512:ℝ)) (by norm_num : 2*(433/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(433/512:ℝ)) ≤ (17049762024336547779/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (433/512:ℝ) (17049756597229/1000000000000:ℝ) (17049762024336547779/1000000000000000000:ℝ) (6012077/50000000000000:ℝ) (601211/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1297).1 (thetaFirstMode_refined_node_1297).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0654 :
    (-100963667168440885867516937/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (94057062584506765152057/111216007226212200348160:ℝ) ∧ thetaFirstModeFirst (94057062584506765152057/111216007226212200348160:ℝ) ≤ (-20192616029390800479/5000000000000000000000000:ℝ) := by
  have hlo : (8525083378181/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(94057062584506765152057/111216007226212200348160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(94057062584506765152057/111216007226212200348160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(94057062584506765152057/111216007226212200348160:ℝ)) ≤ (2713618884369/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(94057062584506765152057/111216007226212200348160:ℝ)) (by norm_num : 2*(94057062584506765152057/111216007226212200348160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(94057062584506765152057/111216007226212200348160:ℝ)) ≤ (8525086091801459817/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (94057062584506765152057/111216007226212200348160:ℝ) (8525083378181/500000000000:ℝ) (8525086091801459817/500000000000000000:ℝ) (2403859/20000000000000:ℝ) (12019361/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1301).1 (thetaFirstMode_refined_node_1301).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0655 :
    (-37979999085750017576033907/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (217/256:ℝ) ∧ thetaFirstModeFirst (217/256:ℝ) ≤ (-47474722090872475203/12500000000000000000000000:ℝ) := by
  have hlo : (4279121864449/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(217/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(217/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(217/256:ℝ)) ≤ (1089669661611/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(217/256:ℝ)) (by norm_num : 2*(217/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(217/256:ℝ)) ≤ (3423298581229486323/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (217/256:ℝ) (4279121864449/250000000000:ℝ) (3423298581229486323/200000000000000000:ℝ) (11258947/100000000000000:ℝ) (11259009/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1302).1 (thetaFirstMode_refined_node_1302).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0656 :
    (-178474579628005459429174991/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (435/512:ℝ) ∧ thetaFirstModeFirst (435/512:ℝ) ≤ (-44618380725938895207/12500000000000000000000000:ℝ) := by
  have hlo : (17183479495567/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(435/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(435/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(435/512:ℝ)) ≤ (5469672540409/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(435/512:ℝ)) (by norm_num : 2*(435/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(435/512:ℝ)) ≤ (17183484965241131537/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (435/512:ℝ) (17183479495567/1000000000000:ℝ) (17183484965241131537/1000000000000000000:ℝ) (2634921/25000000000000:ℝ) (10539743/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1303).1 (thetaFirstMode_refined_node_1303).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0657 :
    (-17840655793648345212111183/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19608004486597651322715/23078521433218056637952:ℝ) ∧ thetaFirstModeFirst (19608004486597651322715/23078521433218056637952:ℝ) ≤ (-557517244199466567/156250000000000000000000:ℝ) := by
  have hlo : (214798637139/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(19608004486597651322715/23078521433218056637952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19608004486597651322715/23078521433218056637952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19608004486597651322715/23078521433218056637952:ℝ)) ≤ (5469803517173/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19608004486597651322715/23078521433218056637952:ℝ)) (by norm_num : 2*(19608004486597651322715/23078521433218056637952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19608004486597651322715/23078521433218056637952:ℝ)) ≤ (17183896440926076589/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19608004486597651322715/23078521433218056637952:ℝ) (214798637139/12500000000:ℝ) (17183896440926076589/1000000000000000000:ℝ) (2633853/25000000000000:ℝ) (1053547/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1307).1 (thetaFirstMode_refined_node_1307).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0658 :
    (-167692554584959926830222623/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (109/128:ℝ) ∧ thetaFirstModeFirst (109/128:ℝ) ≤ (-524036141817057387/156250000000000000000000:ℝ) := by
  have hlo : (431268343319/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(109/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(109/128:ℝ)) ≤ (5491080233449/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(109/128:ℝ)) (by norm_num : 2*(109/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(109/128:ℝ)) ≤ (17250739223841744257/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (109/128:ℝ) (431268343319/25000000000:ℝ) (17250739223841744257/1000000000000000000:ℝ) (1232973/12500000000000:ℝ) (9863839/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1308).1 (thetaFirstMode_refined_node_1308).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0659 :
    (-157520397989446547062862333/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (437/512:ℝ) ∧ thetaFirstModeFirst (437/512:ℝ) ≤ (-39379864891416292301/12500000000000000000000000:ℝ) := by
  have hlo : (4329562798899/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(437/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(437/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(437/512:ℝ)) ≤ (5512571713831/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(437/512:ℝ)) (by norm_num : 2*(437/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(437/512:ℝ)) ≤ (17318256708169472783/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (437/512:ℝ) (4329562798899/250000000000:ℝ) (17318256708169472783/1000000000000000000:ℝ) (9228799/100000000000000:ℝ) (9228851/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1309).1 (thetaFirstMode_refined_node_1309).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0660 :
    (-78730065960210806203937833/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (102172206059393137678593/119705810187199806492160:ℝ) ∧ thetaFirstModeFirst (102172206059393137678593/119705810187199806492160:ℝ) ≤ (-39364802640830643457/12500000000000000000000000:ℝ) := by
  have hlo : (8659332000259/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(102172206059393137678593/119705810187199806492160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(102172206059393137678593/119705810187199806492160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(102172206059393137678593/119705810187199806492160:ℝ)) ≤ (2756351556873/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(102172206059393137678593/119705810187199806492160:ℝ)) (by norm_num : 2*(102172206059393137678593/119705810187199806492160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(102172206059393137678593/119705810187199806492160:ℝ)) ≤ (8659334756611318689/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (102172206059393137678593/119705810187199806492160:ℝ) (8659332000259/500000000000:ℝ) (8659334756611318689/500000000000000000:ℝ) (4612523/50000000000000:ℝ) (9225097/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1313).1 (thetaFirstMode_refined_node_1313).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0661 :
    (-147926149328750039532937443/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (219/256:ℝ) ∧ thetaFirstModeFirst (219/256:ℝ) ≤ (-147925279025843068999/50000000000000000000000000:ℝ) := by
  have hlo : (17386032914309/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(219/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(219/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(219/256:ℝ)) ≤ (5534147309489/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(219/256:ℝ)) (by norm_num : 2*(219/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(219/256:ℝ)) ≤ (17386038448459475977/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (219/256:ℝ) (17386032914309/1000000000000:ℝ) (17386038448459475977/1000000000000000000:ℝ) (8632411/100000000000000:ℝ) (8632459/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1314).1 (thetaFirstMode_refined_node_1314).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0662 :
    (-1735992438626752515251229/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (439/512:ℝ) ∧ thetaFirstModeFirst (439/512:ℝ) ≤ (-216997748208405979/78125000000000000000000:ℝ) := by
  have hlo : (545439997599/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(439/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(439/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(439/512:ℝ)) ≤ (138895183741/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(439/512:ℝ)) (by norm_num : 2*(439/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(439/512:ℝ)) ≤ (436352136974439413/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (439/512:ℝ) (545439997599/31250000000:ℝ) (436352136974439413/25000000000000000:ℝ) (403621/5000000000000:ℝ) (4036233/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1315).1 (thetaFirstMode_refined_node_1315).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0663 :
    (-27765209890924093176995901/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (106458482664671619457791/124159428129696431157760:ℝ) ∧ thetaFirstModeFirst (106458482664671619457791/124159428129696431157760:ℝ) ≤ (-277650426432084671/100000000000000000000000:ℝ) := by
  have hlo : (4363623517607/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(106458482664671619457791/124159428129696431157760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(106458482664671619457791/124159428129696431157760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(106458482664671619457791/124159428129696431157760:ℝ)) ≤ (1111187835367/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(106458482664671619457791/124159428129696431157760:ℝ)) (by norm_num : 2*(106458482664671619457791/124159428129696431157760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(106458482664671619457791/124159428129696431157760:ℝ)) ≤ (3490899925274119631/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (106458482664671619457791/124159428129696431157760:ℝ) (4363623517607/250000000000:ℝ) (3490899925274119631/200000000000000000:ℝ) (64553/800000000000:ℝ) (8069171/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1319).1 (thetaFirstMode_refined_node_1319).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0664 :
    (-16293893694321719792971323/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (55/64:ℝ) ∧ thetaFirstModeFirst (55/64:ℝ) ≤ (-6517518237451493277/2500000000000000000000000:ℝ) := by
  have hlo : (1752239326049/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(55/64:ℝ)) ≤ (697194020599/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(55/64:ℝ)) (by norm_num : 2*(55/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(55/64:ℝ)) ≤ (2190299854755674207/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (55/64:ℝ) (1752239326049/100000000000:ℝ) (2190299854755674207/125000000000000000:ℝ) (3773373/50000000000000:ℝ) (7546789/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1320).1 (thetaFirstMode_refined_node_1320).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0665 :
    (-15289236050376283881337641/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (441/512:ℝ) ∧ thetaFirstModeFirst (441/512:ℝ) ≤ (-12231313792804261279/5000000000000000000000000:ℝ) := by
  have hlo : (3518194793731/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(441/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(441/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(441/512:ℝ)) ≤ (699922760843/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(441/512:ℝ)) (by norm_num : 2*(441/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(441/512:ℝ)) ≤ (2198872446005042899/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (441/512:ℝ) (3518194793731/200000000000:ℝ) (2198872446005042899/125000000000000000:ℝ) (3526709/50000000000000:ℝ) (7053459/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1321).1 (thetaFirstMode_refined_node_1321).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0666 :
    (-1528333998050377289643369/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (110903857005979655461809/128757361064545117135360:ℝ) ∧ thetaFirstModeFirst (110903857005979655461809/128757361064545117135360:ℝ) ≤ (-12226598670865470667/5000000000000000000000000:ℝ) := by
  have hlo : (17591389471239/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(110903857005979655461809/128757361064545117135360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(110903857005979655461809/128757361064545117135360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(110903857005979655461809/128757361064545117135360:ℝ)) ≤ (699939293169/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(110903857005979655461809/128757361064545117135360:ℝ)) (by norm_num : 2*(110903857005979655461809/128757361064545117135360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(110903857005979655461809/128757361064545117135360:ℝ)) ≤ (2198924383844678217/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (110903857005979655461809/128757361064545117135360:ℝ) (17591389471239/1000000000000:ℝ) (2198924383844678217/125000000000000000:ℝ) (705053/10000000000000:ℝ) (705057/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1325).1 (thetaFirstMode_refined_node_1325).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0667 :
    (-3585667387827557866346473/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (221/256:ℝ) ∧ thetaFirstModeFirst (221/256:ℝ) ≤ (-57370320189802267709/25000000000000000000000000:ℝ) := by
  have hlo : (8829911547061/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(221/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(221/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(221/256:ℝ)) ≤ (2810648724297/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(221/256:ℝ)) (by norm_num : 2*(221/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(221/256:ℝ)) ≤ (8829914357710385121/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (221/256:ℝ) (8829911547061/500000000000:ℝ) (8829914357710385121/500000000000000000:ℝ) (6590569/100000000000000:ℝ) (411913/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1326).1 (thetaFirstMode_refined_node_1326).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0668 :
    (-5380430743666488624947283/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (443/512:ℝ) ∧ thetaFirstModeFirst (443/512:ℝ) ≤ (-53803975444308041999/25000000000000000000000000:ℝ) := by
  have hlo : (17728941687447/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(443/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(443/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(443/512:ℝ)) ≤ (2821649292373/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(443/512:ℝ)) (by norm_num : 2*(443/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(443/512:ℝ)) ≤ (8864473665373970189/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (443/512:ℝ) (17728941687447/1000000000000:ℝ) (8864473665373970189/500000000000000000:ℝ) (3078217/50000000000000:ℝ) (615647/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1327).1 (thetaFirstMode_refined_node_1327).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0669 :
    (-1344586981700192143839367/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (115513472527065173117007/133503598919808937500160:ℝ) ∧ thetaFirstModeFirst (115513472527065173117007/133503598919808937500160:ℝ) ≤ (-1344578681871957587/625000000000000000000000:ℝ) := by
  have hlo : (3545871711673/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(115513472527065173117007/133503598919808937500160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115513472527065173117007/133503598919808937500160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(115513472527065173117007/133503598919808937500160:ℝ)) ≤ (1410857819727/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(115513472527065173117007/133503598919808937500160:ℝ)) (by norm_num : 2*(115513472527065173117007/133503598919808937500160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(115513472527065173117007/133503598919808937500160:ℝ)) ≤ (4432341050449605111/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (115513472527065173117007/133503598919808937500160:ℝ) (3545871711673/200000000000:ℝ) (4432341050449605111/250000000000000000:ℝ) (384619/6250000000000:ℝ) (307697/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1331).1 (thetaFirstMode_refined_node_1331).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0670 :
    (-5044597471815766520584581/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (111/128:ℝ) ∧ thetaFirstModeFirst (111/128:ℝ) ≤ (-2522283005515833083/1250000000000000000000000:ℝ) := by
  have hlo : (8899165401649/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(111/128:ℝ)) ≤ (566538583091/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(111/128:ℝ)) (by norm_num : 2*(111/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(111/128:ℝ)) ≤ (1779833646868603963/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (111/128:ℝ) (8899165401649/500000000000:ℝ) (1779833646868603963/100000000000000000:ℝ) (287467/5000000000000:ℝ) (2874687/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1332).1 (thetaFirstMode_refined_node_1332).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0671 :
    (-94568810608081373334721197/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (445/512:ℝ) ∧ thetaFirstModeFirst (445/512:ℝ) ≤ (-23642058480249863763/12500000000000000000000000:ℝ) := by
  have hlo : (17867991500469/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(445/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(445/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(445/512:ℝ)) ≤ (5687559524111/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(445/512:ℝ)) (by norm_num : 2*(445/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(445/512:ℝ)) ≤ (17867997188030448823/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (445/512:ℝ) (17867991500469/1000000000000:ℝ) (17867997188030448823/1000000000000000000:ℝ) (1341927/25000000000000:ℝ) (5367739/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1333).1 (thetaFirstMode_refined_node_1333).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

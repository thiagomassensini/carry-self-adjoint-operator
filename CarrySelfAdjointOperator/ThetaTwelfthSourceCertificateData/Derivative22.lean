import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0704 :
    (-21210070306235236482166089/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (467/512:ℝ) ∧ thetaFirstModeFirst (467/512:ℝ) ≤ (-21209909695580947857/50000000000000000000000000:ℝ) := by
  have hlo : (19471433208707/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(467/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(467/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(467/512:ℝ)) ≤ (6197950977947/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(467/512:ℝ)) (by norm_num : 2*(467/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(467/512:ℝ)) ≤ (19471439406661449571/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (467/512:ℝ) (19471433208707/1000000000000:ℝ) (19471439406661449571/1000000000000000000:ℝ) (1103451/100000000000000:ℝ) (1103459/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1399).1 (thetaFirstMode_refined_node_1399).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0705 :
    (-5300364402117373609737747/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (185715593048194171355943/203608610322761788188160:ℝ) ∧ thetaFirstModeFirst (185715593048194171355943/203608610322761788188160:ℝ) ≤ (-2120129699711990229/5000000000000000000000000:ℝ) := by
  have hlo : (3894373504661/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(185715593048194171355943/203608610322761788188160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(185715593048194171355943/203608610322761788188160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(185715593048194171355943/203608610322761788188160:ℝ)) ≤ (3099044612303/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(185715593048194171355943/203608610322761788188160:ℝ)) (by norm_num : 2*(185715593048194171355943/203608610322761788188160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(185715593048194171355943/203608610322761788188160:ℝ)) ≤ (9735936860698818679/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (185715593048194171355943/203608610322761788188160:ℝ) (3894373504661/200000000000:ℝ) (9735936860698818679/500000000000000000:ℝ) (551489/50000000000000:ℝ) (551493/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1403).1 (thetaFirstMode_refined_node_1403).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0706 :
    (-19750930930569036197061423/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (117/128:ℝ) ∧ thetaFirstModeFirst (117/128:ℝ) ≤ (-1975078947870792369/5000000000000000000000000:ℝ) := by
  have hlo : (3909528448709/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(117/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(117/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(117/128:ℝ)) ≤ (6222209072199/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(117/128:ℝ)) (by norm_num : 2*(117/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(117/128:ℝ)) ≤ (19547648465756873007/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (117/128:ℝ) (3909528448709/200000000000:ℝ) (19547648465756873007/1000000000000000000:ℝ) (511741/50000000000000:ℝ) (1023489/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1404).1 (thetaFirstMode_refined_node_1404).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0707 :
    (-18386674451772073483371701/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (469/512:ℝ) ∧ thetaFirstModeFirst (469/512:ℝ) ≤ (-45966380696732727/125000000000000000000000:ℝ) := by
  have hlo : (1226509347007/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(469/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(469/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(469/512:ℝ)) ≤ (6246562109947/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(469/512:ℝ)) (by norm_num : 2*(469/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(469/512:ℝ)) ≤ (19624155798674725571/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (469/512:ℝ) (1226509347007/62500000000:ℝ) (19624155798674725571/1000000000000000000:ℝ) (37961/4000000000000:ℝ) (949031/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1405).1 (thetaFirstMode_refined_node_1405).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0708 :
    (-4594795814467300481242593/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (192997563136753342300641/210689881453211795484160:ℝ) ∧ thetaFirstModeFirst (192997563136753342300641/210689881453211795484160:ℝ) ≤ (-1148690106875291059/3125000000000000000000000:ℝ) := by
  have hlo : (9812292703267/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(192997563136753342300641/210689881453211795484160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(192997563136753342300641/210689881453211795484160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(192997563136753342300641/210689881453211795484160:ℝ)) ≤ (1561675211687/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(192997563136753342300641/210689881453211795484160:ℝ)) (by norm_num : 2*(192997563136753342300641/210689881453211795484160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(192997563136753342300641/210689881453211795484160:ℝ)) ≤ (4906147913309397391/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (192997563136753342300641/210689881453211795484160:ℝ) (9812292703267/500000000000:ℝ) (4906147913309397391/250000000000000000:ℝ) (118577/12500000000000:ℝ) (948623/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1409).1 (thetaFirstMode_refined_node_1409).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0709 :
    (-17111536951308867281704801/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (235/256:ℝ) ∧ thetaFirstModeFirst (235/256:ℝ) ≤ (-8555707364395816389/25000000000000000000000000:ℝ) := by
  have hlo : (9850478150909/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(235/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(235/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(235/256:ℝ)) ≤ (6271010462791/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(235/256:ℝ)) (by norm_num : 2*(235/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(235/256:ℝ)) ≤ (19700962572830966063/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (235/256:ℝ) (9850478150909/500000000000:ℝ) (19700962572830966063/1000000000000000000:ℝ) (879721/100000000000000:ℝ) (879727/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1410).1 (thetaFirstMode_refined_node_1410).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0710 :
    (-7960022113141745826409757/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (471/512:ℝ) ∧ thetaFirstModeFirst (471/512:ℝ) ≤ (-15919921925517906819/50000000000000000000000000:ℝ) := by
  have hlo : (19778063664643/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(471/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(471/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(471/512:ℝ)) ≤ (3147777251891/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(471/512:ℝ)) (by norm_num : 2*(471/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(471/512:ℝ)) ≤ (9889034980100002363/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (471/512:ℝ) (19778063664643/1000000000000:ℝ) (9889034980100002363/500000000000000000:ℝ) (815233/100000000000000:ℝ) (815239/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1411).1 (thetaFirstMode_refined_node_1411).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0711 :
    (-15913526783585675278320063/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (200532239716009818864159/217985716752994642792960:ℝ) ∧ thetaFirstModeFirst (200532239716009818864159/217985716752994642792960:ℝ) ≤ (-7956702241149263031/25000000000000000000000000:ℝ) := by
  have hlo : (9889250536151/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(200532239716009818864159/217985716752994642792960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(200532239716009818864159/217985716752994642792960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(200532239716009818864159/217985716752994642792960:ℝ)) ≤ (6295693734993/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(200532239716009818864159/217985716752994642792960:ℝ)) (by norm_num : 2*(200532239716009818864159/217985716752994642792960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(200532239716009818864159/217985716752994642792960:ℝ)) ≤ (19778507367997863849/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (200532239716009818864159/217985716752994642792960:ℝ) (9889250536151/500000000000:ℝ) (19778507367997863849/1000000000000000000:ℝ) (814881/100000000000000:ℝ) (814887/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1415).1 (thetaFirstMode_refined_node_1415).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0712 :
    (-59228152473932116783149/200000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (59/64:ℝ) ∧ thetaFirstModeFirst (59/64:ℝ) ≤ (-3701728928079475083/12500000000000000000000000:ℝ) := by
  have hlo : (19855472817153/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(59/64:ℝ)) ≤ (6320194607433/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(59/64:ℝ)) (by norm_num : 2*(59/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(59/64:ℝ)) ≤ (19855479137349260769/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (59/64:ℝ) (19855472817153/1000000000000:ℝ) (19855479137349260769/1000000000000000000:ℝ) (188811/25000000000000:ℝ) (3021/400000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1416).1 (thetaFirstMode_refined_node_1416).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0713 :
    (-3441916006524529991757929/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (473/512:ℝ) ∧ thetaFirstModeFirst (473/512:ℝ) ≤ (-172094514651577977/625000000000000000000000:ℝ) := by
  have hlo : (498329623513/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(473/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(473/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(473/512:ℝ)) ≤ (1586232787431/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(473/512:ℝ)) (by norm_num : 2*(473/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(473/512:ℝ)) ≤ (4983297821363717583/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (473/512:ℝ) (498329623513/25000000000:ℝ) (4983297821363717583/250000000000000000:ℝ) (349729/50000000000000:ℝ) (699463/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1417).1 (thetaFirstMode_refined_node_1417).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0714 :
    (-344050173313491711150469/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (208327263246534084091857/225501664871413871772160:ℝ) ∧ thetaFirstModeFirst (208327263246534084091857/225501664871413871772160:ℝ) ≤ (-550476163127897563/2000000000000000000000000:ℝ) := by
  have hlo : (3986724782973/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(208327263246534084091857/225501664871413871772160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(208327263246534084091857/225501664871413871772160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(208327263246534084091857/225501664871413871772160:ℝ)) ≤ (6345070879627/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(208327263246534084091857/225501664871413871772160:ℝ)) (by norm_num : 2*(208327263246534084091857/225501664871413871772160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(208327263246534084091857/225501664871413871772160:ℝ)) ≤ (19933630259940025811/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (208327263246534084091857/225501664871413871772160:ℝ) (3986724782973/200000000000:ℝ) (19933630259940025811/1000000000000000000:ℝ) (139831/20000000000000:ℝ) (17479/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1421).1 (thetaFirstMode_refined_node_1421).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0715 :
    (-31993395088703516659901/125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (237/256:ℝ) ∧ thetaFirstModeFirst (237/256:ℝ) ≤ (-1279725510441430611/5000000000000000000000000:ℝ) := by
  have hlo : (10005600610269/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(237/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(237/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(237/256:ℝ)) ≤ (6369764508103/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(237/256:ℝ)) (by norm_num : 2*(237/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(237/256:ℝ)) ≤ (20011207590304828079/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (237/256:ℝ) (10005600610269/500000000000:ℝ) (20011207590304828079/1000000000000000000:ℝ) (129519/20000000000000:ℝ) (1619/250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1422).1 (thetaFirstMode_refined_node_1422).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0716 :
    (-59459069139292464237279/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (475/512:ℝ) ∧ thetaFirstModeFirst (475/512:ℝ) ≤ (-2378342159452595197/10000000000000000000000000:ℝ) := by
  have hlo : (20089522847643/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(475/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(475/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(475/512:ℝ)) ≤ (6394695061499/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(475/512:ℝ)) (by norm_num : 2*(475/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(475/512:ℝ)) ≤ (20089529242339827907/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (475/512:ℝ) (20089522847643/1000000000000:ℝ) (20089529242339827907/1000000000000000000:ℝ) (119879/20000000000000:ℝ) (2997/500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1423).1 (thetaFirstMode_refined_node_1423).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0717 :
    (-11886899664204266836359249/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (43278094269113915002275/46648678704053587338752:ℝ) ∧ thetaFirstModeFirst (43278094269113915002275/46648678704053587338752:ℝ) ≤ (-5943398316495164287/25000000000000000000000000:ℝ) := by
  have hlo : (20089963402161/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(43278094269113915002275/46648678704053587338752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43278094269113915002275/46648678704053587338752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(43278094269113915002275/46648678704053587338752:ℝ)) ≤ (6394835294387/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(43278094269113915002275/46648678704053587338752:ℝ)) (by norm_num : 2*(43278094269113915002275/46648678704053587338752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(43278094269113915002275/46648678704053587338752:ℝ)) ≤ (20089969796999138491/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (43278094269113915002275/46648678704053587338752:ℝ) (20089963402161/1000000000000:ℝ) (20089969796999138491/1000000000000000000:ℝ) (299567/50000000000000:ℝ) (599139/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1427).1 (thetaFirstMode_refined_node_1427).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0718 :
    (-690433050305430380128671/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (119/128:ℝ) ∧ thetaFirstModeFirst (119/128:ℝ) ≤ (-86303481029691187/390625000000000000000000:ℝ) := by
  have hlo : (630254719279/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(119/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(119/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(119/128:ℝ)) ≤ (3209861595161/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(119/128:ℝ)) (by norm_num : 2*(119/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(119/128:ℝ)) ≤ (10084078718326631473/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (119/128:ℝ) (630254719279/31250000000:ℝ) (10084078718326631473/500000000000000000:ℝ) (138653/25000000000000:ℝ) (69327/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1428).1 (thetaFirstMode_refined_node_1428).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0719 :
    (-1282366104914979607018227/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (477/512:ℝ) ∧ thetaFirstModeFirst (477/512:ℝ) ≤ (-1282355693078495357/6250000000000000000000000:ℝ) := by
  have hlo : (2530885866021/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(477/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(477/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(477/512:ℝ)) ≤ (805606159559/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(477/512:ℝ)) (by norm_num : 2*(477/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(477/512:ℝ)) ≤ (2530886671627437487/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (477/512:ℝ) (2530885866021/125000000000:ℝ) (2530886671627437487/125000000000000000:ℝ) (513017/100000000000000:ℝ) (513021/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1429).1 (thetaFirstMode_refined_node_1429).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0720 :
    (-205093524455116597851793/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (224729903008522098228393/241216691509014397212160:ℝ) ∧ thetaFirstModeFirst (224729903008522098228393/241216691509014397212160:ℝ) ≤ (-5127296463833603049/25000000000000000000000000:ℝ) := by
  have hlo : (10123764538193/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(224729903008522098228393/241216691509014397212160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(224729903008522098228393/241216691509014397212160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(224729903008522098228393/241216691509014397212160:ℝ)) ≤ (128899800333/20000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(224729903008522098228393/241216691509014397212160:ℝ)) (by norm_num : 2*(224729903008522098228393/241216691509014397212160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(224729903008522098228393/241216691509014397212160:ℝ)) ≤ (404950710427550469/20000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (224729903008522098228393/241216691509014397212160:ℝ) (10123764538193/500000000000:ℝ) (404950710427550469/20000000000000000:ℝ) (512793/100000000000000:ℝ) (512797/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1433).1 (thetaFirstMode_refined_node_1433).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0721 :
    (-4762097396131135711131297/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (239/256:ℝ) ∧ thetaFirstModeFirst (239/256:ℝ) ≤ (-476205570876893703/2500000000000000000000000:ℝ) := by
  have hlo : (5081582946457/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(239/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(239/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(239/256:ℝ)) ≤ (3235036851671/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(239/256:ℝ)) (by norm_num : 2*(239/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(239/256:ℝ)) ≤ (10163169127951651903/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (239/256:ℝ) (5081582946457/250000000000:ℝ) (10163169127951651903/500000000000000000:ℝ) (94879/20000000000000:ℝ) (474399/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1434).1 (thetaFirstMode_refined_node_1434).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0722 :
    (-2209836712101461238050049/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (479/512:ℝ) ∧ thetaFirstModeFirst (479/512:ℝ) ≤ (-1767852675261647937/10000000000000000000000000:ℝ) := by
  have hlo : (20405886799093/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(479/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(479/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(479/512:ℝ)) ≤ (1623849213957/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(479/512:ℝ)) (by norm_num : 2*(479/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(479/512:ℝ)) ≤ (5101473323622813501/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (479/512:ℝ) (20405886799093/1000000000000:ℝ) (5101473323622813501/250000000000000000:ℝ) (87709/20000000000000:ℝ) (438549/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1435).1 (thetaFirstMode_refined_node_1435).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0723 :
    (-1767134288055586409173623/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (233353802902454023413591/249427470805914151528960:ℝ) ∧ thetaFirstModeFirst (233353802902454023413591/249427470805914151528960:ℝ) ≤ (-552224247974378333/3125000000000000000000000:ℝ) := by
  have hlo : (1275395659661/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(233353802902454023413591/249427470805914151528960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(233353802902454023413591/249427470805914151528960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(233353802902454023413591/249427470805914151528960:ℝ)) ≤ (1299107621523/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(233353802902454023413591/249427470805914151528960:ℝ)) (by norm_num : 2*(233353802902454023413591/249427470805914151528960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(233353802902454023413591/249427470805914151528960:ℝ)) ≤ (4081267410023306139/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (233353802902454023413591/249427470805914151528960:ℝ) (1275395659661/62500000000:ℝ) (4081267410023306139/200000000000000000:ℝ) (438353/100000000000000:ℝ) (438357/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1439).1 (thetaFirstMode_refined_node_1439).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0724 :
    (-8201168928069159195281523/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15/16:ℝ) ∧ thetaFirstModeFirst (15/16:ℝ) ≤ (-6560884462435149/40000000000000000000000:ℝ) := by
  have hlo : (32777205091/1600000000:ℝ) ≤ Real.pi*Real.exp (2*(15/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15/16:ℝ)) ≤ (6520819120331/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15/16:ℝ)) (by norm_num : 2*(15/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15/16:ℝ)) ≤ (20485759702698027283/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15/16:ℝ) (32777205091/1600000000:ℝ) (20485759702698027283/1000000000000000000:ℝ) (202639/50000000000000:ℝ) (405281/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1440).1 (thetaFirstMode_refined_node_1440).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0725 :
    (-380334688387447017679939/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (481/512:ℝ) ∧ thetaFirstModeFirst (481/512:ℝ) ≤ (-3803315184435321557/25000000000000000000000000:ℝ) := by
  have hlo : (10282966076421/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(481/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(481/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(481/512:ℝ)) ≤ (6546340884763/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(481/512:ℝ)) (by norm_num : 2*(481/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(481/512:ℝ)) ≤ (20565938699185247459/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (481/512:ℝ) (10282966076421/500000000000:ℝ) (20565938699185247459/1000000000000000000:ℝ) (374417/100000000000000:ℝ) (18721/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1441).1 (thetaFirstMode_refined_node_1441).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0726 :
    (-475220539914251346587007/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (242270625732500482869609/257881768625375876508160:ℝ) ∧ thetaFirstModeFirst (242270625732500482869609/257881768625375876508160:ℝ) ≤ (-475215307691041337/3125000000000000000000000:ℝ) := by
  have hlo : (5141594382299/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(242270625732500482869609/257881768625375876508160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(242270625732500482869609/257881768625375876508160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(242270625732500482869609/257881768625375876508160:ℝ)) ≤ (6546482652489/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(242270625732500482869609/257881768625375876508160:ℝ)) (by norm_num : 2*(242270625732500482869609/257881768625375876508160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(242270625732500482869609/257881768625375876508160:ℝ)) ≤ (20566384075680874977/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (242270625732500482869609/257881768625375876508160:ℝ) (5141594382299/250000000000:ℝ) (20566384075680874977/1000000000000000000:ℝ) (93563/25000000000000:ℝ) (23391/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1445).1 (thetaFirstMode_refined_node_1445).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0727 :
    (-7053106411687972662787101/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (241/256:ℝ) ∧ thetaFirstModeFirst (241/256:ℝ) ≤ (-881630368727641443/6250000000000000000000000:ℝ) := by
  have hlo : (5161606233857/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(241/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(241/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(241/256:ℝ)) ≤ (6571962538557/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(241/256:ℝ)) (by norm_num : 2*(241/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(241/256:ℝ)) ≤ (20646431507392901301/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (241/256:ℝ) (5161606233857/250000000000:ℝ) (20646431507392901301/1000000000000000000:ℝ) (172899/50000000000000:ℝ) (345801/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1446).1 (thetaFirstMode_refined_node_1446).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0728 :
    (-1634431813641584888585789/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (483/512:ℝ) ∧ thetaFirstModeFirst (483/512:ℝ) ≤ (-653766371643753437/5000000000000000000000000:ℝ) := by
  have hlo : (10363616378929/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(483/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(483/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(483/512:ℝ)) ≤ (6597684472669/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(483/512:ℝ)) (by norm_num : 2*(483/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(483/512:ℝ)) ≤ (20727239355545621717/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (483/512:ℝ) (10363616378929/500000000000:ℝ) (20727239355545621717/1000000000000000000:ℝ) (63853/20000000000000:ℝ) (79817/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1447).1 (thetaFirstMode_refined_node_1447).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0729 :
    (-6534982617101774456742169/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (251489040682132561926807/266585749541721770268160:ℝ) ∧ thetaFirstModeFirst (251489040682132561926807/266585749541721770268160:ℝ) ≤ (-1633729769629127911/12500000000000000000000000:ℝ) := by
  have hlo : (20727679768731/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(251489040682132561926807/266585749541721770268160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(251489040682132561926807/266585749541721770268160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(251489040682132561926807/266585749541721770268160:ℝ)) ≤ (6597826760679/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(251489040682132561926807/266585749541721770268160:ℝ)) (by norm_num : 2*(251489040682132561926807/266585749541721770268160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(251489040682132561926807/266585749541721770268160:ℝ)) ≤ (20727686366561821647/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (251489040682132561926807/266585749541721770268160:ℝ) (20727679768731/1000000000000:ℝ) (20727686366561821647/1000000000000000000:ℝ) (79781/25000000000000:ℝ) (319127/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1451).1 (thetaFirstMode_refined_node_1451).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0730 :
    (-94657772384040863625399/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (121/128:ℝ) ∧ thetaFirstModeFirst (121/128:ℝ) ≤ (-121160676114110247/1000000000000000000000000:ℝ) := by
  have hlo : (10404178426581/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(121/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(121/128:ℝ)) ≤ (206984596237/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(121/128:ℝ)) (by norm_num : 2*(121/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(121/128:ℝ)) ≤ (650261358645985541/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (121/128:ℝ) (10404178426581/500000000000:ℝ) (650261358645985541/31250000000000000:ℝ) (11787/4000000000000:ℝ) (147339/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1452).1 (thetaFirstMode_refined_node_1452).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0731 :
    (-28059402249081055661703/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (485/512:ℝ) ∧ thetaFirstModeFirst (485/512:ℝ) ≤ (-2805908361233360907/25000000000000000000000000:ℝ) := by
  have hlo : (10444899229599/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(485/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(485/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(485/512:ℝ)) ≤ (265977230133/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(485/512:ℝ)) (by norm_num : 2*(485/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(485/512:ℝ)) ≤ (835592204345221869/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (485/512:ℝ) (10444899229599/500000000000:ℝ) (835592204345221869/40000000000000000:ℝ) (271893/100000000000000:ℝ) (33987/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1453).1 (thetaFirstMode_refined_node_1453).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0732 :
    (-224380198710388463775431/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (52203587185640050827165/55109141525919324349952:ℝ) ∧ thetaFirstModeFirst (52203587185640050827165/55109141525919324349952:ℝ) ≤ (-5609461880076582213/50000000000000000000000000:ℝ) := by
  have hlo : (20890247118281/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(52203587185640050827165/55109141525919324349952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(52203587185640050827165/55109141525919324349952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(52203587185640050827165/55109141525919324349952:ℝ)) ≤ (6649573565977/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(52203587185640050827165/55109141525919324349952:ℝ)) (by norm_num : 2*(52203587185640050827165/55109141525919324349952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(52203587185640050827165/55109141525919324349952:ℝ)) ≤ (20890253767858381361/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (52203587185640050827165/55109141525919324349952:ℝ) (20890247118281/1000000000000:ℝ) (20890253767858381361/1000000000000000000:ℝ) (271773/100000000000000:ℝ) (10871/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1457).1 (thetaFirstMode_refined_node_1457).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0733 :
    (-1039373003619910424765159/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (243/256:ℝ) ∧ thetaFirstModeFirst (243/256:ℝ) ≤ (-162400036851605783/1562500000000000000000000:ℝ) := by
  have hlo : (5242889704667/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(243/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(243/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(243/256:ℝ)) ≤ (6675455889457/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(243/256:ℝ)) (by norm_num : 2*(243/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(243/256:ℝ)) ≤ (20971565494126885001/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (243/256:ℝ) (5242889704667/250000000000:ℝ) (20971565494126885001/1000000000000000000:ℝ) (31349/12500000000000:ℝ) (50159/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1458).1 (thetaFirstMode_refined_node_1458).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0734 :
    (-2405504769541968288731727/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (487/512:ℝ) ∧ thetaFirstModeFirst (487/512:ℝ) ≤ (-962189115674265387/10000000000000000000000000:ℝ) := by
  have hlo : (21053639179137/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(487/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(487/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(487/512:ℝ)) ≤ (6701582885091/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(487/512:ℝ)) (by norm_num : 2*(487/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(487/512:ℝ)) ≤ (21053645880721689963/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (487/512:ℝ) (21053639179137/1000000000000:ℝ) (21053645880721689963/1000000000000000000:ℝ) (46251/20000000000000:ℝ) (115629/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1459).1 (thetaFirstMode_refined_node_1459).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0735 :
    (-240448542877429540890287/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (270866423231695777103343/284768068631243160732160:ℝ) ∧ thetaFirstModeFirst (270866423231695777103343/284768068631243160732160:ℝ) ≤ (-75139170252217327/781250000000000000000000:ℝ) := by
  have hlo : (5263522375041/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(270866423231695777103343/284768068631243160732160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(270866423231695777103343/284768068631243160732160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(270866423231695777103343/284768068631243160732160:ℝ)) ≤ (1675431556689/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(270866423231695777103343/284768068631243160732160:ℝ)) (by norm_num : 2*(270866423231695777103343/284768068631243160732160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(270866423231695777103343/284768068631243160732160:ℝ)) ≤ (5263524050473265577/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (270866423231695777103343/284768068631243160732160:ℝ) (5263522375041/250000000000:ℝ) (5263524050473265577/250000000000000000:ℝ) (14447/6250000000000:ℝ) (46231/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1463).1 (thetaFirstMode_refined_node_1463).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

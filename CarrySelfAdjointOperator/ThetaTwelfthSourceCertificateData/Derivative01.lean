import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0032 :
    (-21659323709666248210489163128623/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19/512:ℝ) ∧ thetaFirstModeFirst (19/512:ℝ) ≤ (-4331858587436380298539063/10000000000000000000000000:ℝ) := by
  have hlo : (3383627733309/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19/512:ℝ)) ≤ (1077042382751/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19/512:ℝ)) (by norm_num : 2*(19/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19/512:ℝ)) ≤ (3383628810353862343/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19/512:ℝ) (3383627733309/1000000000000:ℝ) (3383628810353862343/1000000000000000000:ℝ) (1382378175107/20000000000000:ℝ) (6911898319961/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0055).1 (thetaFirstMode_refined_node_0055).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0033 :
    (-86541109736915769008140376073/200000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (58618940391/1568203548160:ℝ) ∧ thetaFirstModeFirst (58618940391/1568203548160:ℝ) ≤ (-5408811670908595243752511/12500000000000000000000000:ℝ) := by
  have hlo : (3385457423141/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(58618940391/1568203548160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(58618940391/1568203548160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(58618940391/1568203548160:ℝ)) ≤ (538812395617/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(58618940391/1568203548160:ℝ)) (by norm_num : 2*(58618940391/1568203548160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(58618940391/1568203548160:ℝ)) ≤ (1692729250383597881/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (58618940391/1568203548160:ℝ) (3385457423141/1000000000000:ℝ) (1692729250383597881/500000000000000000:ℝ) (1725047079571/25000000000000:ℝ) (55201566033/800000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0059).1 (thetaFirstMode_refined_node_0059).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0034 :
    (-429713601120990297218690516651/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/128:ℝ) ∧ thetaFirstModeFirst (5/128:ℝ) ≤ (-4297129888397222350343481/10000000000000000000000000:ℝ) := by
  have hlo : (3396870877819/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/128:ℝ)) ≤ (21625156149/20000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/128:ℝ)) (by norm_num : 2*(5/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/128:ℝ)) ≤ (67937439181605357/20000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/128:ℝ) (3396870877819/1000000000000:ℝ) (67937439181605357/20000000000000000:ℝ) (1365524692699/20000000000000:ℝ) (6827630845943/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0060).1 (thetaFirstMode_refined_node_0060).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0035 :
    (-5328073982376069748565638126329/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21/512:ℝ) ∧ thetaFirstModeFirst (21/512:ℝ) ≤ (-21312265474576870512732363/50000000000000000000000000:ℝ) := by
  have hlo : (3410165854531/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21/512:ℝ)) ≤ (542744865427/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21/512:ℝ)) (by norm_num : 2*(21/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21/512:ℝ)) ≤ (1705083470011405211/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21/512:ℝ) (3410165854531/1000000000000:ℝ) (1705083470011405211/500000000000000000:ℝ) (6744033843673/100000000000000:ℝ) (3372020582139/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0061).1 (thetaFirstMode_refined_node_0061).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0036 :
    (-21290550011442000564661609608841/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (143436821409/3476346088960:ℝ) ∧ thetaFirstModeFirst (143436821409/3476346088960:ℝ) ≤ (-10645259788265165656838703/25000000000000000000000000:ℝ) := by
  have hlo : (1705919220389/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(143436821409/3476346088960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(143436821409/3476346088960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(143436821409/3476346088960:ℝ)) ≤ (1086022131703/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(143436821409/3476346088960:ℝ)) (by norm_num : 2*(143436821409/3476346088960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(143436821409/3476346088960:ℝ)) ≤ (3411839526803222879/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (143436821409/3476346088960:ℝ) (1705919220389/500000000000:ℝ) (3411839526803222879/1000000000000000000:ℝ) (6733588693827/100000000000000:ℝ) (6733596006679/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0065).1 (thetaFirstMode_refined_node_0065).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0037 :
    (-2113918342479670500154719740877/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11/256:ℝ) ∧ thetaFirstModeFirst (11/256:ℝ) ≤ (-10569576564830130184571233/25000000000000000000000000:ℝ) := by
  have hlo : (3423512866311/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11/256:ℝ)) ≤ (1089738217539/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11/256:ℝ)) (by norm_num : 2*(11/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11/256:ℝ)) ≤ (3423513956052999627/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11/256:ℝ) (3423512866311/1000000000000:ℝ) (3423513956052999627/1000000000000000000:ℝ) (3330560489303/50000000000000:ℝ) (666112823751/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0066).1 (thetaFirstMode_refined_node_0066).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0038 :
    (-524158864507972521735015212489/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23/512:ℝ) ∧ thetaFirstModeFirst (23/512:ℝ) ≤ (-10483162222833069136581091/25000000000000000000000000:ℝ) := by
  have hlo : (3436912116819/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23/512:ℝ)) ≤ (109400333233/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23/512:ℝ)) (by norm_num : 2*(23/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23/512:ℝ)) ≤ (343691321082460169/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23/512:ℝ) (3436912116819/1000000000000:ℝ) (343691321082460169/100000000000000000:ℝ) (3289441891889/50000000000000:ℝ) (1644722745281/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0067).1 (thetaFirstMode_refined_node_0067).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0039 :
    (-523663174803192504006886623081/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (323819456607/7172691612160:ℝ) ∧ thetaFirstModeFirst (323819456607/7172691612160:ℝ) ≤ (-10473248437966753183534873/25000000000000000000000000:ℝ) := by
  have hlo : (1719227066433/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(323819456607/7172691612160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(323819456607/7172691612160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(323819456607/7172691612160:ℝ)) ≤ (218898834277/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(323819456607/7172691612160:ℝ)) (by norm_num : 2*(323819456607/7172691612160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(323819456607/7172691612160:ℝ)) ≤ (687691045472783261/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (323819456607/7172691612160:ℝ) (1719227066433/500000000000:ℝ) (687691045472783261/200000000000000000:ℝ) (6569483518681/100000000000000:ℝ) (821186338621/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0071).1 (thetaFirstMode_refined_node_0071).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0040 :
    (-2599227671987338000656508596003/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/64:ℝ) ∧ thetaFirstModeFirst (3/64:ℝ) ≤ (-20793791402375408265293881/50000000000000000000000000:ℝ) := by
  have hlo : (3450363810509/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/64:ℝ)) ≤ (274571285077/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/64:ℝ)) (by norm_num : 2*(3/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/64:ℝ)) ≤ (862591227198907661/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/64:ℝ) (3450363810509/1000000000000:ℝ) (862591227198907661/250000000000000000:ℝ) (6497321127709/100000000000000:ℝ) (3248664131823/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0072).1 (thetaFirstMode_refined_node_0072).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0041 :
    (-20621595730971378406221624299829/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (25/512:ℝ) ∧ thetaFirstModeFirst (25/512:ℝ) ≤ (-10310782959610823944320279/25000000000000000000000000:ℝ) := by
  have hlo : (3463868152641/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(25/512:ℝ)) ≤ (1102583706809/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(25/512:ℝ)) (by norm_num : 2*(25/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(25/512:ℝ)) ≤ (3463869255225206737/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (25/512:ℝ) (3463868152641/1000000000000:ℝ) (3463869255225206737/1000000000000000000:ℝ) (3208215916119/50000000000000:ℝ) (6416438906917/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0073).1 (thetaFirstMode_refined_node_0073).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0042 :
    (-206033926439249124145660343477/500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (136694029725/2787696138752:ℝ) ∧ thetaFirstModeFirst (136694029725/2787696138752:ℝ) ≤ (-10301681424662989395362739/25000000000000000000000000:ℝ) := by
  have hlo : (3465300007537/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(136694029725/2787696138752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(136694029725/2787696138752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(136694029725/2787696138752:ℝ)) ≤ (1103039480473/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(136694029725/2787696138752:ℝ)) (by norm_num : 2*(136694029725/2787696138752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(136694029725/2787696138752:ℝ)) ≤ (3465301110577613489/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (136694029725/2787696138752:ℝ) (3465300007537/1000000000000:ℝ) (3465301110577613489/1000000000000000000:ℝ) (3203956520547/50000000000000:ℝ) (64079201093/1000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0077).1 (thetaFirstMode_refined_node_0077).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0043 :
    (-255621118784034415451559961067/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13/256:ℝ) ∧ thetaFirstModeFirst (13/256:ℝ) ≤ (-1022482992668284945294447/2500000000000000000000000:ℝ) := by
  have hlo : (3477425349273/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13/256:ℝ)) ≤ (69181193589/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13/256:ℝ)) (by norm_num : 2*(13/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13/256:ℝ)) ≤ (217339153510847277/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13/256:ℝ) (3477425349273/1000000000000:ℝ) (217339153510847277/62500000000000000:ℝ) (316810733639/5000000000000:ℝ) (1267244337271/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0078).1 (thetaFirstMode_refined_node_0078).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0044 :
    (-3168455388153843058102657/7812500000000000000000000:ℝ) ≤ thetaFirstModeFirst (27/512:ℝ) ∧ thetaFirstModeFirst (27/512:ℝ) ≤ (-2534760624729362313169221/6250000000000000000000000:ℝ) := by
  have hlo : (436379450909/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(27/512:ℝ)) ≤ (555615689/500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(27/512:ℝ)) (by norm_num : 2*(27/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(27/512:ℝ)) ≤ (1745518359252577/500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (27/512:ℝ) (436379450909/125000000000:ℝ) (1745518359252577/500000000000000:ℝ) (6256668378569/100000000000000:ℝ) (1955211041/31250000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0079).1 (thetaFirstMode_refined_node_0079).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0045 :
    (-2026130524034421173072393168211/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1362565468143/25744761372160:ℝ) ∧ thetaFirstModeFirst (1362565468143/25744761372160:ℝ) ≤ (-10130637885004480828793473/25000000000000000000000000:ℝ) := by
  have hlo : (1746186661131/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1362565468143/25744761372160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1362565468143/25744761372160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1362565468143/25744761372160:ℝ)) ≤ (222331437199/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1362565468143/25744761372160:ℝ)) (by norm_num : 2*(1362565468143/25744761372160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1362565468143/25744761372160:ℝ)) ≤ (698474886784318007/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1362565468143/25744761372160:ℝ) (1746186661131/500000000000:ℝ) (698474886784318007/200000000000000000:ℝ) (6248902811683/100000000000000:ℝ) (3124454879173/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0083).1 (thetaFirstMode_refined_node_0083).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0046 :
    (-20106882402249366437974215035373/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/128:ℝ) ∧ thetaFirstModeFirst (7/128:ℝ) ≤ (-2010685307950647689200857/5000000000000000000000000:ℝ) := by
  have hlo : (700939826863/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/128:ℝ)) ≤ (1115580614643/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/128:ℝ)) (by norm_num : 2*(7/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/128:ℝ)) ≤ (3504700249898146299/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/128:ℝ) (700939826863/200000000000:ℝ) (3504700249898146299/1000000000000000000:ℝ) (3088895816439/50000000000000:ℝ) (6177798524727/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0084).1 (thetaFirstMode_refined_node_0084).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0047 :
    (-19936004915881567533863341562369/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29/512:ℝ) ∧ thetaFirstModeFirst (29/512:ℝ) ≤ (-4983993939333095022983139/12500000000000000000000000:ℝ) := by
  have hlo : (3518416138891/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29/512:ℝ)) ≤ (1119946873717/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29/512:ℝ)) (by norm_num : 2*(29/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29/512:ℝ)) ≤ (3518417258841211181/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29/512:ℝ) (3518416138891/1000000000000:ℝ) (3518417258841211181/1000000000000000000:ℝ) (1524895768329/25000000000000:ℝ) (6099589904549/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0085).1 (thetaFirstMode_refined_node_0085).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0048 :
    (-796816209155865795231474753921/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2586561620841/45522720232960:ℝ) ∧ thetaFirstModeFirst (2586561620841/45522720232960:ℝ) ≤ (-3984075217078425251079549/10000000000000000000000000:ℝ) := by
  have hlo : (703934502679/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(2586561620841/45522720232960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2586561620841/45522720232960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2586561620841/45522720232960:ℝ)) ≤ (44813871609/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2586561620841/45522720232960:ℝ)) (by norm_num : 2*(2586561620841/45522720232960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2586561620841/45522720232960:ℝ)) ≤ (140786945349733137/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2586561620841/45522720232960:ℝ) (703934502679/200000000000:ℝ) (140786945349733137/40000000000000000:ℝ) (6092468283531/100000000000000:ℝ) (6092475109233/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0089).1 (thetaFirstMode_refined_node_0089).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0049 :
    (-3953098722851508546114689751313/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15/256:ℝ) ∧ thetaFirstModeFirst (15/256:ℝ) ≤ (-3953092924098674439516283/10000000000000000000000000:ℝ) := by
  have hlo : (706437366061/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15/256:ℝ)) ≤ (224866044369/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15/256:ℝ)) (by norm_num : 2*(15/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15/256:ℝ)) ≤ (706437590927339817/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15/256:ℝ) (706437366061/200000000000:ℝ) (706437590927339817/200000000000000000:ℝ) (6022041292103/100000000000000:ℝ) (6022048062889/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0090).1 (thetaFirstMode_refined_node_0090).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0050 :
    (-9797680007378481496928448322373/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (31/512:ℝ) ∧ thetaFirstModeFirst (31/512:ℝ) ≤ (-489883279657990947463667/1250000000000000000000000:ℝ) := by
  have hlo : (3546011418681/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(31/512:ℝ)) ≤ (1128730725913/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(31/512:ℝ)) (by norm_num : 2*(31/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(31/512:ℝ)) ≤ (3546012547413199409/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (31/512:ℝ) (3546011418681/1000000000000:ℝ) (3546012547413199409/1000000000000000000:ℝ) (148629120907/2500000000000:ℝ) (2972585773397/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0091).1 (thetaFirstMode_refined_node_0091).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0051 :
    (-2447602546722036932239545475457/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4705751134359/77506860444160:ℝ) ∧ thetaFirstModeFirst (4705751134359/77506860444160:ℝ) ≤ (-9790395779758562435714121/25000000000000000000000000:ℝ) := by
  have hlo : (3547196835349/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(4705751134359/77506860444160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4705751134359/77506860444160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4705751134359/77506860444160:ℝ)) ≤ (282277013959/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4705751134359/77506860444160:ℝ)) (by norm_num : 2*(4705751134359/77506860444160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4705751134359/77506860444160:ℝ)) ≤ (886799491114496687/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4705751134359/77506860444160:ℝ) (3547196835349/1000000000000:ℝ) (886799491114496687/250000000000000000:ℝ) (2969308861029/50000000000000:ℝ) (2969312213711/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0095).1 (thetaFirstMode_refined_node_0095).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0052 :
    (-9712807780648039536783710416019/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/16:ℝ) ∧ thetaFirstModeFirst (1/16:ℝ) ≤ (-242819836234221746329167/625000000000000000000000:ℝ) := by
  have hlo : (3559890114967/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/16:ℝ)) ≤ (1133148453067/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/16:ℝ)) (by norm_num : 2*(1/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/16:ℝ)) ≤ (3559891248116115731/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/16:ℝ) (3559890114967/1000000000000:ℝ) (3559891248116115731/1000000000000000000:ℝ) (73361902601/1250000000000:ℝ) (2934479429249/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0096).1 (thetaFirstMode_refined_node_0096).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0053 :
    (-19256271622363056000386282897917/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (33/512:ℝ) ∧ thetaFirstModeFirst (33/512:ℝ) ≤ (-4814060781548974449617637/12500000000000000000000000:ℝ) := by
  have hlo : (3573823130933/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(33/512:ℝ)) ≤ (1137583470717/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(33/512:ℝ)) (by norm_num : 2*(33/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(33/512:ℝ)) ≤ (3573824268520232181/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (33/512:ℝ) (3573823130933/1000000000000:ℝ) (3573824268520232181/1000000000000000000:ℝ) (1448350466289/25000000000000:ℝ) (5793408455657/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0097).1 (thetaFirstMode_refined_node_0097).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0054 :
    (-1924266908892634104655381558467/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8248340454057/127663103388160:ℝ) ∧ thetaFirstModeFirst (8248340454057/127663103388160:ℝ) ≤ (-769705624247290117610637/2000000000000000000000000:ℝ) := by
  have hlo : (714989225059/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(8248340454057/127663103388160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8248340454057/127663103388160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8248340454057/127663103388160:ℝ)) ≤ (568970465499/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8248340454057/127663103388160:ℝ)) (by norm_num : 2*(8248340454057/127663103388160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8248340454057/127663103388160:ℝ)) ≤ (1787473631618399907/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8248340454057/127663103388160:ℝ) (714989225059/200000000000:ℝ) (1787473631618399907/500000000000000000:ℝ) (1157470820943/20000000000000:ℝ) (1157472138081/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0101).1 (thetaFirstMode_refined_node_0101).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0055 :
    (-4771834872341895137550187393991/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17/256:ℝ) ∧ thetaFirstModeFirst (17/256:ℝ) ≤ (-9543655580069378252100291/25000000000000000000000000:ℝ) := by
  have hlo : (3587810679183/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17/256:ℝ)) ≤ (571017923267/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17/256:ℝ)) (by norm_num : 2*(17/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17/256:ℝ)) ≤ (1793905910610144331/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17/256:ℝ) (3587810679183/1000000000000:ℝ) (1793905910610144331/500000000000000000:ℝ) (2859256110477/50000000000000:ℝ) (2859259375861/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0102).1 (thetaFirstMode_refined_node_0102).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0056 :
    (-1891883037452610718912070196731/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (35/512:ℝ) ∧ thetaFirstModeFirst (35/512:ℝ) ≤ (-1182425138294745884210001/3125000000000000000000000:ℝ) := by
  have hlo : (900463243287/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(35/512:ℝ)) ≤ (573252824229/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(35/512:ℝ)) (by norm_num : 2*(35/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(35/512:ℝ)) ≤ (1800927059828056797/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (35/512:ℝ) (900463243287/250000000000:ℝ) (1800927059828056797/500000000000000000:ℝ) (1411070411223/25000000000000:ℝ) (1128857623223/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0103).1 (thetaFirstMode_refined_node_0103).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0057 :
    (-9453031325967523810465966908297/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2798051987115/40842963901952:ℝ) ∧ thetaFirstModeFirst (2798051987115/40842963901952:ℝ) ≤ (-1890603450284284156080951/5000000000000000000000000:ℝ) := by
  have hlo : (360292064551/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(2798051987115/40842963901952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2798051987115/40842963901952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2798051987115/40842963901952:ℝ)) ≤ (1146845499197/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2798051987115/40842963901952:ℝ)) (by norm_num : 2*(2798051987115/40842963901952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2798051987115/40842963901952:ℝ)) ≤ (3602921792358800821/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2798051987115/40842963901952:ℝ) (360292064551/100000000000:ℝ) (3602921792358800821/1000000000000000000:ℝ) (5638676396401/100000000000000:ℝ) (2819341431557/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0107).1 (thetaFirstMode_refined_node_0107).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0058 :
    (-4687688852339902010928426547041/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/128:ℝ) ∧ thetaFirstModeFirst (9/128:ℝ) ≤ (-23438409269323013106193/62500000000000000000000:ℝ) := by
  have hlo : (1807975113549/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/128:ℝ)) ≤ (287748236173/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/128:ℝ)) (by norm_num : 2*(9/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/128:ℝ)) ≤ (903987844523443589/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/128:ℝ) (1807975113549/500000000000:ℝ) (903987844523443589/250000000000000000:ℝ) (13926771157/250000000000:ℝ) (5570714874669/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0108).1 (thetaFirstMode_refined_node_0108).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0059 :
    (-9291562821391630894250339304297/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (37/512:ℝ) ∧ thetaFirstModeFirst (37/512:ℝ) ≤ (-464577445432171790500551/1250000000000000000000000:ℝ) := by
  have hlo : (181505132807/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(37/512:ℝ)) ≤ (577748901853/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(37/512:ℝ)) (by norm_num : 2*(37/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(37/512:ℝ)) ≤ (1815051905819071829/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (37/512:ℝ) (181505132807/50000000000:ℝ) (1815051905819071829/500000000000000000:ℝ) (2748895478593/50000000000000:ℝ) (5497797309893/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0109).1 (thetaFirstMode_refined_node_0109).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0060 :
    (-1857110670608614599858865705377/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23045391280593/318280722972160:ℝ) ∧ thetaFirstModeFirst (23045391280593/318280722972160:ℝ) ≤ (-580346215396718945662957/1562500000000000000000000:ℝ) := by
  have hlo : (453890121897/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(23045391280593/318280722972160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23045391280593/318280722972160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23045391280593/318280722972160:ℝ)) ≤ (115582194479/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23045391280593/318280722972160:ℝ)) (by norm_num : 2*(23045391280593/318280722972160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23045391280593/318280722972160:ℝ)) ≤ (363112213099865047/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23045391280593/318280722972160:ℝ) (453890121897/125000000000:ℝ) (363112213099865047/100000000000000000:ℝ) (1373145106981/25000000000000:ℝ) (5492586776391/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0113).1 (thetaFirstMode_refined_node_0113).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0061 :
    (-4603988009807282375485863725769/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19/256:ℝ) ∧ thetaFirstModeFirst (19/256:ℝ) ≤ (-4603981095641749754190571/12500000000000000000000000:ℝ) := by
  have hlo : (3644310476223/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19/256:ℝ)) ≤ (1160020294241/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19/256:ℝ)) (by norm_num : 2*(19/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19/256:ℝ)) ≤ (3644311636245465913/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19/256:ℝ) (3644310476223/1000000000000:ℝ) (3644311636245465913/1000000000000000000:ℝ) (1356381841877/25000000000000:ℝ) (1356383415313/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0114).1 (thetaFirstMode_refined_node_0114).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0062 :
    (-9124622738576661921007532794953/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (39/512:ℝ) ∧ thetaFirstModeFirst (39/512:ℝ) ≤ (-9124608994890436277857697/25000000000000000000000000:ℝ) := by
  have hlo : (3658573904141/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(39/512:ℝ)) ≤ (1164560485303/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(39/512:ℝ)) (by norm_num : 2*(39/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(39/512:ℝ)) ≤ (3658575068704507679/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (39/512:ℝ) (3658573904141/1000000000000:ℝ) (3658575068704507679/1000000000000000000:ℝ) (2676957945317/50000000000000:ℝ) (2676961062807/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0115).1 (thetaFirstMode_refined_node_0115).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0063 :
    (-569934446770298107902169363121/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (36980403679791/484639493685760:ℝ) ∧ thetaFirstModeFirst (36980403679791/484639493685760:ℝ) ≤ (-1823787482083737217849107/5000000000000000000000000:ℝ) := by
  have hlo : (1829773967263/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(36980403679791/484639493685760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(36980403679791/484639493685760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(36980403679791/484639493685760:ℝ)) ≤ (291217632217/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(36980403679791/484639493685760:ℝ)) (by norm_num : 2*(36980403679791/484639493685760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(36980403679791/484639493685760:ℝ)) ≤ (914887274849501681/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (36980403679791/484639493685760:ℝ) (1829773967263/500000000000:ℝ) (914887274849501681/250000000000000000:ℝ) (1069811902989/20000000000000:ℝ) (668633218241/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0119).1 (thetaFirstMode_refined_node_0119).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0608 :
    (-143437439005532781622460523/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (403/512:ℝ) ∧ thetaFirstModeFirst (403/512:ℝ) ≤ (-4482396845767395801/195312500000000000000000:ℝ) := by
  have hlo : (236943241101/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(403/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(403/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(403/512:ℝ)) ≤ (4826969075063/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(403/512:ℝ)) (by norm_num : 2*(403/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(403/512:ℝ)) ≤ (15164372257434395359/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (403/512:ℝ) (236943241101/15625000000:ℝ) (15164372257434395359/1000000000000000000:ℝ) (19234701/25000000000000:ℝ) (9617397/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1207).1 (thetaFirstMode_refined_node_1207).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0609 :
    (-573543693293688058820251719/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (49289005090173420207207/62619246315825509148160:ℝ) ∧ thetaFirstModeFirst (49289005090173420207207/62619246315825509148160:ℝ) ≤ (-7169259169044547/312500000000000000000:ℝ) := by
  have hlo : (4738987309/312500000:ℝ) ≤ Real.pi*Real.exp (2*(49289005090173420207207/62619246315825509148160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49289005090173420207207/62619246315825509148160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(49289005090173420207207/62619246315825509148160:ℝ)) ≤ (4827093839303/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(49289005090173420207207/62619246315825509148160:ℝ)) (by norm_num : 2*(49289005090173420207207/62619246315825509148160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(49289005090173420207207/62619246315825509148160:ℝ)) ≤ (15164764215897429679/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (49289005090173420207207/62619246315825509148160:ℝ) (4738987309/312500000:ℝ) (15164764215897429679/1000000000000000000:ℝ) (1538183/2000000000000:ℝ) (38454761/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1211).1 (thetaFirstMode_refined_node_1211).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0610 :
    (-1086739292051088542535118539/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (101/128:ℝ) ∧ thetaFirstModeFirst (101/128:ℝ) ≤ (-1086733669606481414637/50000000000000000000000000:ℝ) := by
  have hlo : (15223719086473/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(101/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(101/128:ℝ)) ≤ (4845861297863/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(101/128:ℝ)) (by norm_num : 2*(101/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(101/128:ℝ)) ≤ (15223723932337315759/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (101/128:ℝ) (15223719086473/1000000000000:ℝ) (15223723932337315759/1000000000000000000:ℝ) (72576069/100000000000000:ℝ) (72576421/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1212).1 (thetaFirstMode_refined_node_1212).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0611 :
    (-1028957029458779308852977933/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (405/512:ℝ) ∧ thetaFirstModeFirst (405/512:ℝ) ≤ (-205790335072329053403/10000000000000000000000000:ℝ) := by
  have hlo : (3056660607659/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(405/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(405/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(405/512:ℝ)) ≤ (4864827462731/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(405/512:ℝ)) (by norm_num : 2*(405/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(405/512:ℝ)) ≤ (15283307903123470483/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (405/512:ℝ) (3056660607659/200000000000:ℝ) (15283307903123470483/1000000000000000000:ℝ) (68444817/100000000000000:ℝ) (68445151/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1213).1 (thetaFirstMode_refined_node_1213).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0612 :
    (-257146535571036027014468161/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (10306934712842449320045/13029789587177640023552:ℝ) ∧ thetaFirstModeFirst (10306934712842449320045/13029789587177640023552:ℝ) ≤ (-257145200802361081561/12500000000000000000000000:ℝ) := by
  have hlo : (7641848060059/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(10306934712842449320045/13029789587177640023552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(10306934712842449320045/13029789587177640023552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(10306934712842449320045/13029789587177640023552:ℝ)) ≤ (1216238146147/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(10306934712842449320045/13029789587177640023552:ℝ)) (by norm_num : 2*(10306934712842449320045/13029789587177640023552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(10306934712842449320045/13029789587177640023552:ℝ)) ≤ (3820925246268392171/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (10306934712842449320045/13029789587177640023552:ℝ) (7641848060059/500000000000:ℝ) (3820925246268392171/250000000000000000:ℝ) (34209179/50000000000000:ℝ) (68418691/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1217).1 (thetaFirstMode_refined_node_1217).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0613 :
    (-974019628195177236729921279/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (203/256:ℝ) ∧ thetaFirstModeFirst (203/256:ℝ) ≤ (-974014543593470253147/50000000000000000000000000:ℝ) := by
  have hlo : (15343120195111/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(203/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(203/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(203/256:ℝ)) ≤ (4883867859071/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(203/256:ℝ)) (by norm_num : 2*(203/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(203/256:ℝ)) ≤ (15343125078982440103/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (203/256:ℝ) (15343120195111/1000000000000:ℝ) (15343125078982440103/1000000000000000000:ℝ) (64533677/100000000000000:ℝ) (64533993/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1218).1 (thetaFirstMode_refined_node_1218).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0614 :
    (-460899671713523687379383837/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (407/512:ℝ) ∧ thetaFirstModeFirst (407/512:ℝ) ≤ (-11522431429625069401/625000000000000000000000:ℝ) := by
  have hlo : (770158573483/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(407/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(407/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(407/512:ℝ)) ≤ (2451491388707/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(407/512:ℝ)) (by norm_num : 2*(407/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(407/512:ℝ)) ≤ (7701588186322190251/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (407/512:ℝ) (770158573483/50000000000:ℝ) (7701588186322190251/500000000000000000:ℝ) (15207947/25000000000000:ℝ) (60832087/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1219).1 (thetaFirstMode_refined_node_1219).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0615 :
    (-460732948638730350424083/25000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (53870833123989848203743/67767622995901638300160:ℝ) ∧ thetaFirstModeFirst (53870833123989848203743/67767622995901638300160:ℝ) ≤ (-460730534105283632101/25000000000000000000000000:ℝ) := by
  have hlo : (7701782843901/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(53870833123989848203743/67767622995901638300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53870833123989848203743/67767622995901638300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(53870833123989848203743/67767622995901638300160:ℝ)) ≤ (1225777065243/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(53870833123989848203743/67767622995901638300160:ℝ)) (by norm_num : 2*(53870833123989848203743/67767622995901638300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(53870833123989848203743/67767622995901638300160:ℝ)) ≤ (3850892647727952099/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (53870833123989848203743/67767622995901638300160:ℝ) (7701782843901/500000000000:ℝ) (3850892647727952099/250000000000000000:ℝ) (60808201/100000000000000:ℝ) (121617/200000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1223).1 (thetaFirstMode_refined_node_1223).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0616 :
    (-43608675798027496137440357/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (51/64:ℝ) ∧ thetaFirstModeFirst (51/64:ℝ) ≤ (-218042232092081089451/12500000000000000000000000:ℝ) := by
  have hlo : (3865864444563/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(51/64:ℝ)) ≤ (4922172509433/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(51/64:ℝ)) (by norm_num : 2*(51/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(51/64:ℝ)) ≤ (15463462700427146769/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (51/64:ℝ) (3865864444563/250000000000:ℝ) (15463462700427146769/1000000000000000000:ℝ) (57328777/100000000000000:ℝ) (2866453/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1224).1 (thetaFirstMode_refined_node_1224).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0617 :
    (-825024436280679444573946443/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (409/512:ℝ) ∧ thetaFirstModeFirst (409/512:ℝ) ≤ (-51563754746382324809/3125000000000000000000000:ℝ) := by
  have hlo : (970248752549/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(409/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(409/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(409/512:ℝ)) ≤ (4941437347939/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(409/512:ℝ)) (by norm_num : 2*(409/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(409/512:ℝ)) ≤ (15523984982223726827/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (409/512:ℝ) (970248752549/62500000000:ℝ) (15523984982223726827/1000000000000000000:ℝ) (54014741/100000000000000:ℝ) (54015009/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1225).1 (thetaFirstMode_refined_node_1225).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0618 :
    (-824724907872944656516977819/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (56300658464195197911441/70477940425169641423360:ℝ) ∧ thetaFirstModeFirst (56300658464195197911441/70477940425169641423360:ℝ) ≤ (-103090070349974624473/6250000000000000000000000:ℝ) := by
  have hlo : (3881093852019/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(56300658464195197911441/70477940425169641423360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(56300658464195197911441/70477940425169641423360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(56300658464195197911441/70477940425169641423360:ℝ)) ≤ (4941563197283/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(56300658464195197911441/70477940425169641423360:ℝ)) (by norm_num : 2*(56300658464195197911441/70477940425169641423360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(56300658464195197911441/70477940425169641423360:ℝ)) ≤ (15524380349641891819/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (56300658464195197911441/70477940425169641423360:ℝ) (3881093852019/250000000000:ℝ) (15524380349641891819/1000000000000000000:ℝ) (26996867/50000000000000:ℝ) (53994001/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1229).1 (thetaFirstMode_refined_node_1229).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0619 :
    (-780239157933164564318631603/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (205/256:ℝ) ∧ thetaFirstModeFirst (205/256:ℝ) ≤ (-39011751291867380607/2500000000000000000000000:ℝ) := by
  have hlo : (3116947836151/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(205/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(205/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(205/256:ℝ)) ≤ (4960777586891/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(205/256:ℝ)) (by norm_num : 2*(205/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(205/256:ℝ)) ≤ (15584744141533657363/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (205/256:ℝ) (3116947836151/200000000000:ℝ) (15584744141533657363/1000000000000000000:ℝ) (12720057/25000000000000:ℝ) (50880481/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1230).1 (thetaFirstMode_refined_node_1230).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0620 :
    (-46106834454225713055426399/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (411/512:ℝ) ∧ thetaFirstModeFirst (411/512:ℝ) ≤ (-3688527088288399797/250000000000000000000000:ℝ) := by
  have hlo : (625829445011/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(411/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(411/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(411/512:ℝ)) ≤ (2490096760699/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(411/512:ℝ)) (by norm_num : 2*(411/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(411/512:ℝ)) ≤ (7822870552734653507/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (411/512:ℝ) (625829445011/40000000000:ℝ) (7822870552734653507/500000000000000000:ℝ) (5989527/12500000000000:ℝ) (5989557/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1231).1 (thetaFirstMode_refined_node_1231).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0621 :
    (-184360137887577686924503227/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (58827419272179392782959/73282635538862459829760:ℝ) ∧ thetaFirstModeFirst (58827419272179392782959/73282635538862459829760:ℝ) ≤ (-184359158332087160407/12500000000000000000000000:ℝ) := by
  have hlo : (15646132654547/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(58827419272179392782959/73282635538862459829760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(58827419272179392782959/73282635538862459829760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(58827419272179392782959/73282635538862459829760:ℝ)) ≤ (1245079935153/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(58827419272179392782959/73282635538862459829760:ℝ)) (by norm_num : 2*(58827419272179392782959/73282635538862459829760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(58827419272179392782959/73282635538862459829760:ℝ)) ≤ (3911534408717118729/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (58827419272179392782959/73282635538862459829760:ℝ) (15646132654547/1000000000000:ℝ) (3911534408717118729/250000000000000000:ℝ) (11974381/25000000000000:ℝ) (47897763/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1235).1 (thetaFirstMode_refined_node_1235).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0622 :
    (-3486655607294994757452767/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (103/128:ℝ) ∧ thetaFirstModeFirst (103/128:ℝ) ≤ (-348663693584401058843/25000000000000000000000000:ℝ) := by
  have hlo : (7853485902543/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(103/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(103/128:ℝ)) ≤ (199987417909/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(103/128:ℝ)) (by norm_num : 2*(103/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(103/128:ℝ)) ≤ (628279072190989037/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (103/128:ℝ) (7853485902543/500000000000:ℝ) (628279072190989037/40000000000000000:ℝ) (45114101/100000000000000:ℝ) (5639291/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1236).1 (thetaFirstMode_refined_node_1236).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0623 :
    (-329502418214358820306201177/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (413/512:ℝ) ∧ thetaFirstModeFirst (413/512:ℝ) ≤ (-164750325583458751739/12500000000000000000000000:ℝ) := by
  have hlo : (3942111788643/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(413/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(413/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(413/512:ℝ)) ≤ (2509626831647/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(413/512:ℝ)) (by norm_num : 2*(413/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(413/512:ℝ)) ≤ (7884226086914393671/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (413/512:ℝ) (3942111788643/250000000000:ℝ) (7884226086914393671/500000000000000000:ℝ) (42465673/100000000000000:ℝ) (42465887/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1237).1 (thetaFirstMode_refined_node_1237).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0624 :
    (-658763833043370852357635337/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (61454482584883441479657/76184511352508643612160:ℝ) ∧ thetaFirstModeFirst (61454482584883441479657/76184511352508643612160:ℝ) ≤ (-65876029894147087197/5000000000000000000000000:ℝ) := by
  have hlo : (7884422429327/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(61454482584883441479657/76184511352508643612160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61454482584883441479657/76184511352508643612160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(61454482584883441479657/76184511352508643612160:ℝ)) ≤ (5019380256461/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(61454482584883441479657/76184511352508643612160:ℝ)) (by norm_num : 2*(61454482584883441479657/76184511352508643612160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(61454482584883441479657/76184511352508643612160:ℝ)) ≤ (15768849878036082373/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (61454482584883441479657/76184511352508643612160:ℝ) (7884422429327/500000000000:ℝ) (15768849878036082373/1000000000000000000:ℝ) (8489811/20000000000000:ℝ) (42449269/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1241).1 (thetaFirstMode_refined_node_1241).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0625 :
    (-622635042916985816620705343/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (207/256:ℝ) ∧ thetaFirstModeFirst (207/256:ℝ) ≤ (-19457239961648375731/1562500000000000000000000:ℝ) := by
  have hlo : (15830163111773/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(207/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(207/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(207/256:ℝ)) ≤ (5038898466693/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(207/256:ℝ)) (by norm_num : 2*(207/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(207/256:ℝ)) ≤ (15830168150673461949/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (207/256:ℝ) (15830163111773/1000000000000:ℝ) (15830168150673461949/1000000000000000000:ℝ) (1248847/3125000000000:ℝ) (39963307/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1242).1 (thetaFirstMode_refined_node_1242).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0626 :
    (-147032555738495212791660307/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (415/512:ℝ) ∧ thetaFirstModeFirst (415/512:ℝ) ≤ (-735158806386425209/62500000000000000000000:ℝ) := by
  have hlo : (19865150773/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(415/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(415/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(415/512:ℝ)) ≤ (5058620157679/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(415/512:ℝ)) (by norm_num : 2*(415/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(415/512:ℝ)) ≤ (15892125677023242647/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (415/512:ℝ) (19865150773/1250000000:ℝ) (15892125677023242647/1000000000000000000:ℝ) (37598933/100000000000000:ℝ) (9399781/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1243).1 (thetaFirstMode_refined_node_1243).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0627 :
    (-23516574116722947004006353/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (12837063038463911715435/15837287983182423613952:ℝ) ∧ thetaFirstModeFirst (12837063038463911715435/15837287983182423613952:ℝ) ≤ (-293955587533503965049/25000000000000000000000000:ℝ) := by
  have hlo : (15892519510127/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(12837063038463911715435/15837287983182423613952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(12837063038463911715435/15837287983182423613952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(12837063038463911715435/15837287983182423613952:ℝ)) ≤ (1011749425777/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(12837063038463911715435/15837287983182423613952:ℝ)) (by norm_num : 2*(12837063038463911715435/15837287983182423613952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(12837063038463911715435/15837287983182423613952:ℝ)) ≤ (3178504913775042761/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (12837063038463911715435/15837287983182423613952:ℝ) (15892519510127/1000000000000:ℝ) (3178504913775042761/200000000000000000:ℝ) (18792087/50000000000000:ℝ) (7516873/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1247).1 (thetaFirstMode_refined_node_1247).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0628 :
    (-555402747527111927358116591/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13/16:ℝ) ∧ thetaFirstModeFirst (13/16:ℝ) ≤ (-69424965680054293149/6250000000000000000000000:ℝ) := by
  have hlo : (3988580154963/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13/16:ℝ)) ≤ (5078419037181/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13/16:ℝ)) (by norm_num : 2*(13/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13/16:ℝ)) ≤ (15954325698274569333/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13/16:ℝ) (3988580154963/250000000000:ℝ) (15954325698274569333/1000000000000000000:ℝ) (17683023/50000000000000:ℝ) (35366227/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1248).1 (thetaFirstMode_refined_node_1248).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0629 :
    (-262184319428565050816787673/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (417/512:ℝ) ∧ thetaFirstModeFirst (417/512:ℝ) ≤ (-262182886591060890091/25000000000000000000000000:ℝ) := by
  have hlo : (16016764065227/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(417/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(417/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(417/512:ℝ)) ≤ (2549147703653/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(417/512:ℝ)) (by norm_num : 2*(417/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(417/512:ℝ)) ≤ (8008384581762339229/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (417/512:ℝ) (16016764065227/1000000000000:ℝ) (8008384581762339229/500000000000000000:ℝ) (16628833/50000000000000:ℝ) (33257837/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1249).1 (thetaFirstMode_refined_node_1249).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0630 :
    (-262087729107131110010299747/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (67023486088292228081193/82291363666684906908160:ℝ) ∧ thetaFirstModeFirst (67023486088292228081193/82291363666684906908160:ℝ) ≤ (-104834521660100607077/10000000000000000000000000:ℝ) := by
  have hlo : (3203432831487/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(67023486088292228081193/82291363666684906908160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67023486088292228081193/82291363666684906908160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(67023486088292228081193/82291363666684906908160:ℝ)) ≤ (2549211380319/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(67023486088292228081193/82291363666684906908160:ℝ)) (by norm_num : 2*(67023486088292228081193/82291363666684906908160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(67023486088292228081193/82291363666684906908160:ℝ)) ≤ (8008584627930508167/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (67023486088292228081193/82291363666684906908160:ℝ) (3203432831487/200000000000:ℝ) (8008584627930508167/500000000000000000:ℝ) (33244571/100000000000000:ℝ) (33244741/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1253).1 (thetaFirstMode_refined_node_1253).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0631 :
    (-15467109871519912352116813/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (209/256:ℝ) ∧ thetaFirstModeFirst (209/256:ℝ) ≤ (-61868100913995935529/6250000000000000000000000:ℝ) := by
  have hlo : (2009931488417/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(209/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(209/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(209/256:ℝ)) ≤ (319890598209/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(209/256:ℝ)) (by norm_num : 2*(209/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(209/256:ℝ)) ≤ (1004966064099206937/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (209/256:ℝ) (2009931488417/125000000000:ℝ) (1004966064099206937/62500000000000000:ℝ) (31267337/100000000000000:ℝ) (15633749/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1254).1 (thetaFirstMode_refined_node_1254).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0632 :
    (-467062426228801168325964729/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (419/512:ℝ) ∧ thetaFirstModeFirst (419/512:ℝ) ≤ (-467059859576881899207/50000000000000000000000000:ℝ) := by
  have hlo : (16142385102723/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(419/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(419/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(419/512:ℝ)) ≤ (5138281833773/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(419/512:ℝ)) (by norm_num : 2*(419/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(419/512:ℝ)) ≤ (16142390241008420389/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (419/512:ℝ) (16142385102723/1000000000000:ℝ) (16142390241008420389/1000000000000000000:ℝ) (29388909/100000000000000:ℝ) (29389061/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1255).1 (thetaFirstMode_refined_node_1255).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0633 :
    (-58361215101033611177754681/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (69972668969052009938391/85502296803586871580160:ℝ) ∧ thetaFirstModeFirst (69972668969052009938391/85502296803586871580160:ℝ) ≤ (-72951117836134217/7812500000000000000000:ℝ) := by
  have hlo : (252231037629/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(69972668969052009938391/85502296803586871580160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69972668969052009938391/85502296803586871580160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(69972668969052009938391/85502296803586871580160:ℝ)) ≤ (2569204786659/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(69972668969052009938391/85502296803586871580160:ℝ)) (by norm_num : 2*(69972668969052009938391/85502296803586871580160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(69972668969052009938391/85502296803586871580160:ℝ)) ≤ (8071395773334407787/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (69972668969052009938391/85502296803586871580160:ℝ) (252231037629/15625000000:ℝ) (8071395773334407787/500000000000000000:ℝ) (293773/1000000000000:ℝ) (7344363/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1259).1 (thetaFirstMode_refined_node_1259).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0634 :
    (-44063970500189336649822529/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (105/128:ℝ) ∧ thetaFirstModeFirst (105/128:ℝ) ≤ (-55079660112310537893/6250000000000000000000000:ℝ) := by
  have hlo : (2025695576459/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(105/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(105/128:ℝ)) ≤ (5158392500259/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(105/128:ℝ)) (by norm_num : 2*(105/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(105/128:ℝ)) ≤ (16205569770066172587/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (105/128:ℝ) (2025695576459/125000000000:ℝ) (16205569770066172587/1000000000000000000:ℝ) (27616527/100000000000000:ℝ) (2761667/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1260).1 (thetaFirstMode_refined_node_1260).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0635 :
    (-25975555842139422315591199/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (421/512:ℝ) ∧ thetaFirstModeFirst (421/512:ℝ) ≤ (-103901649138329984669/12500000000000000000000000:ℝ) := by
  have hlo : (4067247849557/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(421/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(421/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(421/512:ℝ)) ≤ (5178581877669/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(421/512:ℝ)) (by norm_num : 2*(421/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(421/512:ℝ)) ≤ (16268996576811786717/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (421/512:ℝ) (4067247849557/250000000000:ℝ) (16268996576811786717/1000000000000000000:ℝ) (25944617/100000000000000:ℝ) (1621547/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1261).1 (thetaFirstMode_refined_node_1261).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0636 :
    (-207727320810335136609106977/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (73036644780581807459409/88822326679864764136960:ℝ) ∧ thetaFirstModeFirst (73036644780581807459409/88822326679864764136960:ℝ) ≤ (-162286072146599511/19531250000000000000000:ℝ) := by
  have hlo : (3253878785987/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(73036644780581807459409/88822326679864764136960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73036644780581807459409/88822326679864764136960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(73036644780581807459409/88822326679864764136960:ℝ)) ≤ (2589355003759/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(73036644780581807459409/88822326679864764136960:ℝ)) (by norm_num : 2*(73036644780581807459409/88822326679864764136960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(73036644780581807459409/88822326679864764136960:ℝ)) ≤ (8134699554324248087/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (73036644780581807459409/88822326679864764136960:ℝ) (3253878785987/200000000000:ℝ) (8134699554324248087/500000000000000000:ℝ) (50653/195312500000:ℝ) (25934471/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1265).1 (thetaFirstMode_refined_node_1265).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0637 :
    (-48987821802785003311931581/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (211/256:ℝ) ∧ thetaFirstModeFirst (211/256:ℝ) ≤ (-3135203241903843201/400000000000000000000000:ℝ) := by
  have hlo : (16332666430207/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(211/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(211/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(211/256:ℝ)) ≤ (1299712568517/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(211/256:ℝ)) (by norm_num : 2*(211/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(211/256:ℝ)) ≤ (4083167907265027581/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (211/256:ℝ) (16332666430207/1000000000000:ℝ) (4083167907265027581/250000000000000000:ℝ) (194943/800000000000:ℝ) (12184001/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1266).1 (thetaFirstMode_refined_node_1266).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0638 :
    (-184728149789246975084540257/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (423/512:ℝ) ∧ thetaFirstModeFirst (423/512:ℝ) ≤ (-73890845283712051279/10000000000000000000000000:ℝ) := by
  have hlo : (3279318135843/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(423/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(423/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(423/512:ℝ)) ≤ (5219197998727/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(423/512:ℝ)) (by norm_num : 2*(423/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(423/512:ℝ)) ≤ (16396595898414752111/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (423/512:ℝ) (3279318135843/200000000000:ℝ) (16396595898414752111/1000000000000000000:ℝ) (22881253/100000000000000:ℝ) (11440687/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1267).1 (thetaFirstMode_refined_node_1267).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0639 :
    (-46164833162719103188474261/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (76219304315222090354607/92254615216783819932160:ℝ) ∧ thetaFirstModeFirst (76219304315222090354607/92254615216783819932160:ℝ) ≤ (-184658296068738265389/25000000000000000000000000:ℝ) := by
  have hlo : (8198497224977/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(76219304315222090354607/92254615216783819932160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(76219304315222090354607/92254615216783819932160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(76219304315222090354607/92254615216783819932160:ℝ)) ≤ (1304831630743/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(76219304315222090354607/92254615216783819932160:ℝ)) (by norm_num : 2*(76219304315222090354607/92254615216783819932160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(76219304315222090354607/92254615216783819932160:ℝ)) ≤ (4099249917320793599/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (76219304315222090354607/92254615216783819932160:ℝ) (8198497224977/500000000000:ℝ) (4099249917320793599/250000000000000000:ℝ) (22872157/100000000000000:ℝ) (11436139/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1271).1 (thetaFirstMode_refined_node_1271).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

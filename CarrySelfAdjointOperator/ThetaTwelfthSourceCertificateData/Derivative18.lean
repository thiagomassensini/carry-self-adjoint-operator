import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0576 :
    (-896532731548993082115411401/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29739470398816532457609/39964118478267692316160:ℝ) ∧ thetaFirstModeFirst (29739470398816532457609/39964118478267692316160:ℝ) ≤ (-1793056935135439122237/25000000000000000000000000:ℝ) := by
  have hlo : (6957993110757/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(29739470398816532457609/39964118478267692316160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29739470398816532457609/39964118478267692316160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29739470398816532457609/39964118478267692316160:ℝ)) ≤ (4429596911857/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29739470398816532457609/39964118478267692316160:ℝ)) (by norm_num : 2*(29739470398816532457609/39964118478267692316160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29739470398816532457609/39964118478267692316160:ℝ)) ≤ (13915990651111568201/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29739470398816532457609/39964118478267692316160:ℝ) (6957993110757/500000000000:ℝ) (13915990651111568201/1000000000000000000:ℝ) (262411641/100000000000000:ℝ) (65603201/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1145).1 (thetaFirstMode_refined_node_1145).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0577 :
    (-341408544029594829048809063/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (191/256:ℝ) ∧ thetaFirstModeFirst (191/256:ℝ) ≤ (-853517286409715645717/12500000000000000000000000:ℝ) := by
  have hlo : (3492517478387/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(191/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(191/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(191/256:ℝ)) ≤ (889362457859/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(191/256:ℝ)) (by norm_num : 2*(191/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(191/256:ℝ)) ≤ (2794014872072629387/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (191/256:ℝ) (3492517478387/250000000000:ℝ) (2794014872072629387/200000000000000000:ℝ) (248837591/100000000000000:ℝ) (124419349/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1146).1 (thetaFirstMode_refined_node_1146).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0578 :
    (-203029796327843336823228453/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (383/512:ℝ) ∧ thetaFirstModeFirst (383/512:ℝ) ≤ (-40605764623404394999/625000000000000000000000:ℝ) := by
  have hlo : (14024747221239/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(383/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(383/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(383/512:ℝ)) ≤ (558027077563/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(383/512:ℝ)) (by norm_num : 2*(383/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(383/512:ℝ)) ≤ (1753093960682377859/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (383/512:ℝ) (14024747221239/1000000000000:ℝ) (1753093960682377859/125000000000000000:ℝ) (2947841/1250000000000:ℝ) (117914167/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1147).1 (thetaFirstMode_refined_node_1147).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0579 :
    (-1623674954201119793003664367/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (31174323728860831314807/41673534214555068828160:ℝ) ∧ thetaFirstModeFirst (31174323728860831314807/41673534214555068828160:ℝ) ≤ (-129893374030726408869/2000000000000000000000000:ℝ) := by
  have hlo : (561005146081/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(31174323728860831314807/41673534214555068828160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31174323728860831314807/41673534214555068828160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(31174323728860831314807/41673534214555068828160:ℝ)) ≤ (4464338033719/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(31174323728860831314807/41673534214555068828160:ℝ)) (by norm_num : 2*(31174323728860831314807/41673534214555068828160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(31174323728860831314807/41673534214555068828160:ℝ)) ≤ (14025133116365374367/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (31174323728860831314807/41673534214555068828160:ℝ) (561005146081/40000000000:ℝ) (14025133116365374367/1000000000000000000:ℝ) (235738949/100000000000000:ℝ) (117870001/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1151).1 (thetaFirstMode_refined_node_1151).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0580 :
    (-618047811068838252726902079/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/4:ℝ) ∧ thetaFirstModeFirst (3/4:ℝ) ≤ (-1545112091390414497951/25000000000000000000000000:ℝ) := by
  have hlo : (14079638529861/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/4:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/4:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/4:ℝ)) ≤ (4481689070339/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/4:ℝ)) (by norm_num : 2*(3/4:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/4:ℝ)) ≤ (14079643011553510027/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/4:ℝ) (14079638529861/1000000000000:ℝ) (14079643011553510027/1000000000000000000:ℝ) (111724691/50000000000000:ℝ) (44690077/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1152).1 (thetaFirstMode_refined_node_1152).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0581 :
    (-2939077011211527041464266069/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (385/512:ℝ) ∧ thetaFirstModeFirst (385/512:ℝ) ≤ (-2939062812782684309853/50000000000000000000000000:ℝ) := by
  have hlo : (14134744676991/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(385/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(385/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(385/512:ℝ)) ≤ (4499229905409/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(385/512:ℝ)) (by norm_num : 2*(385/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(385/512:ℝ)) ≤ (14134749176223576537/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (385/512:ℝ) (14134744676991/1000000000000:ℝ) (14134749176223576537/1000000000000000000:ℝ) (211675683/100000000000000:ℝ) (211676637/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1153).1 (thetaFirstMode_refined_node_1153).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0582 :
    (-2938054038277696384625885119/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (6534077305948613955765/8689317914228980285952:ℝ) ∧ thetaFirstModeFirst (6534077305948613955765/8689317914228980285952:ℝ) ≤ (-18362749085630808099/312500000000000000000000:ℝ) := by
  have hlo : (1766890887811/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(6534077305948613955765/8689317914228980285952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(6534077305948613955765/8689317914228980285952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(6534077305948613955765/8689317914228980285952:ℝ)) ≤ (4499351635251/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(6534077305948613955765/8689317914228980285952:ℝ)) (by norm_num : 2*(6534077305948613955765/8689317914228980285952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(6534077305948613955765/8689317914228980285952:ℝ)) ≤ (14135131601843094843/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (6534077305948613955765/8689317914228980285952:ℝ) (1766890887811/125000000000:ℝ) (14135131601843094843/1000000000000000000:ℝ) (10579809/5000000000000:ℝ) (211597133/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1157).1 (thetaFirstMode_refined_node_1157).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0583 :
    (-349338200679397703756588057/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (193/256:ℝ) ∧ thetaFirstModeFirst (193/256:ℝ) ≤ (-279469205625855074361/5000000000000000000000000:ℝ) := by
  have hlo : (7095033251741/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(193/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(193/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(193/256:ℝ)) ≤ (2258419696683/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(193/256:ℝ)) (by norm_num : 2*(193/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(193/256:ℝ)) ≤ (7095035510161436019/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (193/256:ℝ) (7095033251741/500000000000:ℝ) (7095035510161436019/500000000000000000:ℝ) (40095821/20000000000000:ℝ) (50120003/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1158).1 (thetaFirstMode_refined_node_1158).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0584 :
    (-2656849832265411500852869629/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (387/512:ℝ) ∧ thetaFirstModeFirst (387/512:ℝ) ≤ (-2656836907245666823941/50000000000000000000000000:ℝ) := by
  have hlo : (14245604853481/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(387/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(387/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(387/512:ℝ)) ≤ (4534517802911/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(387/512:ℝ)) (by norm_num : 2*(387/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(387/512:ℝ)) ≤ (14245609388000577223/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (387/512:ℝ) (14245604853481/1000000000000:ℝ) (14245609388000577223/1000000000000000000:ℝ) (189833661/100000000000000:ℝ) (189834523/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1159).1 (thetaFirstMode_refined_node_1159).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0585 :
    (-53118438712850890005802797/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (34229931486855451316343/45285304621504058652160:ℝ) ∧ thetaFirstModeFirst (34229931486855451316343/45285304621504058652160:ℝ) ≤ (-663977256147342826289/12500000000000000000000000:ℝ) := by
  have hlo : (14245988286629/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(34229931486855451316343/45285304621504058652160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(34229931486855451316343/45285304621504058652160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(34229931486855451316343/45285304621504058652160:ℝ)) ≤ (2267319926749/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(34229931486855451316343/45285304621504058652160:ℝ)) (by norm_num : 2*(34229931486855451316343/45285304621504058652160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(34229931486855451316343/45285304621504058652160:ℝ)) ≤ (7122996410635171157/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (34229931486855451316343/45285304621504058652160:ℝ) (14245988286629/1000000000000:ℝ) (7122996410635171157/500000000000000000:ℝ) (47440541/25000000000000:ℝ) (7590521/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1163).1 (thetaFirstMode_refined_node_1163).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0586 :
    (-1262622235062069163251677961/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (97/128:ℝ) ∧ thetaFirstModeFirst (97/128:ℝ) ≤ (-252523214394817400157/5000000000000000000000000:ℝ) := by
  have hlo : (2860272114887/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(97/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(97/128:ℝ)) ≤ (2276132701897/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(97/128:ℝ)) (by norm_num : 2*(97/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(97/128:ℝ)) ≤ (7150682563350701921/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (97/128:ℝ) (2860272114887/200000000000:ℝ) (7150682563350701921/500000000000000000:ℝ) (89857211/50000000000000:ℝ) (179715241/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1164).1 (thetaFirstMode_refined_node_1164).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0587 :
    (-74988553721983971504019227/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (389/512:ℝ) ∧ thetaFirstModeFirst (389/512:ℝ) ≤ (-1199810983116795438807/25000000000000000000000000:ℝ) := by
  have hlo : (14357334517111/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(389/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(389/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(389/512:ℝ)) ≤ (571260308353/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(389/512:ℝ)) (by norm_num : 2*(389/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(389/512:ℝ)) ≤ (1794667385899626329/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (389/512:ℝ) (14357334517111/1000000000000:ℝ) (1794667385899626329/125000000000000000:ℝ) (85048737/50000000000000:ℝ) (42524563/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1165).1 (thetaFirstMode_refined_node_1165).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0588 :
    (-299849097179838837701341767/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (35855303234927171773041/47191752594083278773760:ℝ) ∧ thetaFirstModeFirst (35855303234927171773041/47191752594083278773760:ℝ) ≤ (-239878102454267071413/5000000000000000000000000:ℝ) := by
  have hlo : (14357718970831/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(35855303234927171773041/47191752594083278773760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35855303234927171773041/47191752594083278773760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(35855303234927171773041/47191752594083278773760:ℝ)) ≤ (4570204842269/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(35855303234927171773041/47191752594083278773760:ℝ)) (by norm_num : 2*(35855303234927171773041/47191752594083278773760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(35855303234927171773041/47191752594083278773760:ℝ)) ≤ (14357723541038394517/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (35855303234927171773041/47191752594083278773760:ℝ) (14357718970831/1000000000000:ℝ) (14357723541038394517/1000000000000000000:ℝ) (17003323/10000000000000:ℝ) (21254251/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1169).1 (thetaFirstMode_refined_node_1169).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0589 :
    (-1823816786254770653470453/40000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (195/256:ℝ) ∧ thetaFirstModeFirst (195/256:ℝ) ≤ (-91190390533012568217/2000000000000000000000000:ℝ) := by
  have hlo : (2882705507121/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(195/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(195/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(195/256:ℝ)) ≤ (2293984631933/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(195/256:ℝ)) (by norm_num : 2*(195/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(195/256:ℝ)) ≤ (7206766061788289269/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (195/256:ℝ) (2882705507121/200000000000:ℝ) (7206766061788289269/500000000000000000:ℝ) (32191977/20000000000000:ℝ) (257537/160000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1170).1 (thetaFirstMode_refined_node_1170).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0590 :
    (-541354635711101637232108007/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (391/512:ℝ) ∧ thetaFirstModeFirst (391/512:ℝ) ≤ (-108270392241695314659/2500000000000000000000000:ℝ) := by
  have hlo : (7234970243677/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(391/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(391/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(391/512:ℝ)) ≤ (1151481516963/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(391/512:ℝ)) (by norm_num : 2*(391/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(391/512:ℝ)) ≤ (3617486273320342059/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (391/512:ℝ) (7234970243677/500000000000:ℝ) (3617486273320342059/250000000000000000:ℝ) (15227967/10000000000000:ℝ) (152280373/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1171).1 (thetaFirstMode_refined_node_1171).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0591 :
    (-270582132373772827394153683/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (37548920246270157404559/49168060985435061199360:ℝ) ∧ thetaFirstModeFirst (37548920246270157404559/49168060985435061199360:ℝ) ≤ (-43292927219113365563/1000000000000000000000000:ℝ) := by
  have hlo : (289406519491/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(37548920246270157404559/49168060985435061199360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37548920246270157404559/49168060985435061199360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(37548920246270157404559/49168060985435061199360:ℝ)) ≤ (4606048772263/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(37548920246270157404559/49168060985435061199360:ℝ)) (by norm_num : 2*(37548920246270157404559/49168060985435061199360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(37548920246270157404559/49168060985435061199360:ℝ)) ≤ (14470330580600034959/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (37548920246270157404559/49168060985435061199360:ℝ) (289406519491/20000000000:ℝ) (14470330580600034959/1000000000000000000:ℝ) (152221993/100000000000000:ℝ) (19027837/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1175).1 (thetaFirstMode_refined_node_1175).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0592 :
    (-1028173668489559087449442309/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (49/64:ℝ) ∧ thetaFirstModeFirst (49/64:ℝ) ≤ (-205633714848588242127/5000000000000000000000000:ℝ) := by
  have hlo : (7263287116577/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(49/64:ℝ)) ≤ (4623953152783/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(49/64:ℝ)) (by norm_num : 2*(49/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(49/64:ℝ)) ≤ (14526578857111003319/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (49/64:ℝ) (7263287116577/500000000000:ℝ) (14526578857111003319/1000000000000000000:ℝ) (28807151/20000000000000:ℝ) (72018211/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1176).1 (thetaFirstMode_refined_node_1176).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0593 :
    (-305052602816992669344287/7812500000000000000000000000:ℝ) ≤ thetaFirstModeFirst (393/512:ℝ) ∧ thetaFirstModeFirst (393/512:ℝ) ≤ (-61010217271264374633/1562500000000000000000000:ℝ) := by
  have hlo : (911464352323/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(393/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(393/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(393/512:ℝ)) ≤ (18133010913/3906250000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(393/512:ℝ)) (by norm_num : 2*(393/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(393/512:ℝ)) ≤ (56966540153204409/3906250000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (393/512:ℝ) (911464352323/62500000000:ℝ) (56966540153204409/3906250000000000:ℝ) (68103971/50000000000000:ℝ) (5448343/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1177).1 (thetaFirstMode_refined_node_1177).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0594 :
    (-243955966584715408959034827/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (39313276758463040392257/51216412690723244700160:ℝ) ∧ thetaFirstModeFirst (39313276758463040392257/51216412690723244700160:ℝ) ≤ (-97581901365402252519/2500000000000000000000000:ℝ) := by
  have hlo : (1458381617073/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(39313276758463040392257/51216412690723244700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39313276758463040392257/51216412690723244700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(39313276758463040392257/51216412690723244700160:ℝ)) ≤ (580271728901/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(39313276758463040392257/51216412690723244700160:ℝ)) (by norm_num : 2*(39313276758463040392257/51216412690723244700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(39313276758463040392257/51216412690723244700160:ℝ)) ≤ (1822977601613279293/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (39313276758463040392257/51216412690723244700160:ℝ) (1458381617073/100000000000:ℝ) (1822977601613279293/125000000000000000:ℝ) (68078103/50000000000000:ℝ) (136156839/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1181).1 (thetaFirstMode_refined_node_1181).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0595 :
    (-231646744760667274867987257/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (197/256:ℝ) ∧ thetaFirstModeFirst (197/256:ℝ) ≤ (-926582354629352300893/25000000000000000000000000:ℝ) := by
  have hlo : (7320253783471/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(197/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(197/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(197/256:ℝ)) ≤ (2330109633419/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(197/256:ℝ)) (by norm_num : 2*(197/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(197/256:ℝ)) ≤ (7320256113581696467/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (197/256:ℝ) (7320253783471/500000000000:ℝ) (7320256113581696467/500000000000000000:ℝ) (128776883/100000000000000:ℝ) (32194371/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1182).1 (thetaFirstMode_refined_node_1182).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0596 :
    (-1758654515732965610741962569/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (395/512:ℝ) ∧ thetaFirstModeFirst (395/512:ℝ) ≤ (-219830713874743950111/6250000000000000000000000:ℝ) := by
  have hlo : (1837226111677/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(395/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(395/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(395/512:ℝ)) ≤ (4678458849341/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(395/512:ℝ)) (by norm_num : 2*(395/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(395/512:ℝ)) ≤ (14697813571877740213/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (395/512:ℝ) (1837226111677/125000000000:ℝ) (14697813571877740213/1000000000000000000:ℝ) (121724043/100000000000000:ℝ) (121724613/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1183).1 (thetaFirstMode_refined_node_1183).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0597 :
    (-87901588057022216815845429/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8230188948417592711155/10667809430360898647552:ℝ) ∧ thetaFirstModeFirst (8230188948417592711155/10667809430360898647552:ℝ) ≤ (-43950573548455566307/1250000000000000000000000:ℝ) := by
  have hlo : (734909824311/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(8230188948417592711155/10667809430360898647552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8230188948417592711155/10667809430360898647552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8230188948417592711155/10667809430360898647552:ℝ)) ≤ (1169645555997/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8230188948417592711155/10667809430360898647552:ℝ)) (by norm_num : 2*(8230188948417592711155/10667809430360898647552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8230188948417592711155/10667809430360898647552:ℝ)) ≤ (3674550291201283221/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8230188948417592711155/10667809430360898647552:ℝ) (734909824311/50000000000:ℝ) (3674550291201283221/250000000000000000:ℝ) (60838837/50000000000000:ℝ) (24335649/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1187).1 (thetaFirstMode_refined_node_1187).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0598 :
    (-1668581238067534158733256773/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (99/128:ℝ) ∧ thetaFirstModeFirst (99/128:ℝ) ≤ (-166857285040154310147/5000000000000000000000000:ℝ) := by
  have hlo : (14755334490941/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(99/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(99/128:ℝ)) ≤ (4696769819551/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(99/128:ℝ)) (by norm_num : 2*(99/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(99/128:ℝ)) ≤ (14755339187712684743/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (99/128:ℝ) (14755334490941/1000000000000:ℝ) (14755339187712684743/1000000000000000000:ℝ) (11503167/10000000000000:ℝ) (115032211/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1188).1 (thetaFirstMode_refined_node_1188).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0599 :
    (-49461388788087094434926977/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (397/512:ℝ) ∧ thetaFirstModeFirst (397/512:ℝ) ≤ (-1582756457897761047819/50000000000000000000000000:ℝ) := by
  have hlo : (14813085237289/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(397/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(397/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(397/512:ℝ)) ≤ (589394057109/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(397/512:ℝ)) (by norm_num : 2*(397/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(397/512:ℝ)) ≤ (1851636244055234637/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (397/512:ℝ) (14813085237289/1000000000000:ℝ) (1851636244055234637/125000000000000000:ℝ) (108682771/100000000000000:ℝ) (27170821/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1189).1 (thetaFirstMode_refined_node_1189).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0600 :
    (-197775250872396195097220583/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (43064575909141158188793/55538261523062839068160:ℝ) ∧ thetaFirstModeFirst (43064575909141158188793/55538261523062839068160:ℝ) ≤ (-1582194023640968293451/50000000000000000000000000:ℝ) := by
  have hlo : (14813473902201/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(43064575909141158188793/55538261523062839068160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43064575909141158188793/55538261523062839068160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(43064575909141158188793/55538261523062839068160:ℝ)) ≤ (2357638086391/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(43064575909141158188793/55538261523062839068160:ℝ)) (by norm_num : 2*(43064575909141158188793/55538261523062839068160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(43064575909141158188793/55538261523062839068160:ℝ)) ≤ (7406739308739360863/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (43064575909141158188793/55538261523062839068160:ℝ) (14813473902201/1000000000000:ℝ) (7406739308739360863/500000000000000000:ℝ) (108641251/100000000000000:ℝ) (27160441/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1193).1 (thetaFirstMode_refined_node_1193).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0601 :
    (-187627697452966701727544563/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (199/256:ℝ) ∧ thetaFirstModeFirst (199/256:ℝ) ≤ (-1501013973206842939359/50000000000000000000000000:ℝ) := by
  have hlo : (14871062013667/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(199/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(199/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(199/256:ℝ)) ≤ (2366803520901/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(199/256:ℝ)) (by norm_num : 2*(199/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(199/256:ℝ)) ≤ (7435533373637935293/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (199/256:ℝ) (14871062013667/1000000000000:ℝ) (7435533373637935293/500000000000000000:ℝ) (102661077/100000000000000:ℝ) (25665391/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1194).1 (thetaFirstMode_refined_node_1194).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0602 :
    (-284635402158587686803849571/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (399/512:ℝ) ∧ thetaFirstModeFirst (399/512:ℝ) ≤ (-17789622286559827833/625000000000000000000000:ℝ) := by
  have hlo : (3732316426183/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(399/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(399/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(399/512:ℝ)) ≤ (950426771187/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(399/512:ℝ)) (by norm_num : 2*(399/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(399/512:ℝ)) ≤ (2985854091373680891/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (399/512:ℝ) (3732316426183/250000000000:ℝ) (2985854091373680891/200000000000000000:ℝ) (4847551/5000000000000:ℝ) (96951481/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1195).1 (thetaFirstMode_refined_node_1195).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0603 :
    (-284533901394894733744266069/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (45056903762744623817991/57816411855179361794560:ℝ) ∧ thetaFirstModeFirst (45056903762744623817991/57816411855179361794560:ℝ) ≤ (-1422662264411540062911/50000000000000000000000000:ℝ) := by
  have hlo : (14929655454607/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(45056903762744623817991/57816411855179361794560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45056903762744623817991/57816411855179361794560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(45056903762744623817991/57816411855179361794560:ℝ)) ≤ (4752257917199/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(45056903762744623817991/57816411855179361794560:ℝ)) (by norm_num : 2*(45056903762744623817991/57816411855179361794560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(45056903762744623817991/57816411855179361794560:ℝ)) ≤ (14929660206866958007/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (45056903762744623817991/57816411855179361794560:ℝ) (14929655454607/1000000000000:ℝ) (14929660206866958007/1000000000000000000:ℝ) (96913873/100000000000000:ℝ) (19382867/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1199).1 (thetaFirstMode_refined_node_1199).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0604 :
    (-84316365055329730026288149/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (25/32:ℝ) ∧ thetaFirstModeFirst (25/32:ℝ) ≤ (-168631870475918828439/6250000000000000000000000:ℝ) := by
  have hlo : (14987697198603/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(25/32:ℝ)) ≤ (298170823873/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(25/32:ℝ)) (by norm_num : 2*(25/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(25/32:ℝ)) ≤ (936731373083649689/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (25/32:ℝ) (14987697198603/1000000000000:ℝ) (936731373083649689/62500000000000000:ℝ) (11442213/12500000000000:ℝ) (91538141/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1200).1 (thetaFirstMode_refined_node_1200).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0605 :
    (-51140545259715366370742567/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (401/512:ℝ) ∧ thetaFirstModeFirst (401/512:ℝ) ≤ (-12785070771648217/500000000000000000000:ℝ) := by
  have hlo : (24074171819/1600000000:ℝ) ≤ Real.pi*Real.exp (2*(401/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(401/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(401/512:ℝ)) ≤ (957881060741/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(401/512:ℝ)) (by norm_num : 2*(401/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(401/512:ℝ)) ≤ (3009272435256500413/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (401/512:ℝ) (24074171819/1600000000:ℝ) (3009272435256500413/200000000000000000:ℝ) (540043/625000000000:ℝ) (17281459/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1201).1 (thetaFirstMode_refined_node_1201).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0606 :
    (-127805607741068420352915781/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (47130745688792656218009/60175914297020011010560:ℝ) ∧ thetaFirstModeFirst (47130745688792656218009/60175914297020011010560:ℝ) ≤ (-319512384466385954059/12500000000000000000000000:ℝ) := by
  have hlo : (15046748234561/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(47130745688792656218009/60175914297020011010560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47130745688792656218009/60175914297020011010560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(47130745688792656218009/60175914297020011010560:ℝ)) ≤ (4789529714413/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(47130745688792656218009/60175914297020011010560:ℝ)) (by norm_num : 2*(47130745688792656218009/60175914297020011010560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(47130745688792656218009/60175914297020011010560:ℝ)) ≤ (15046753024091879909/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (47130745688792656218009/60175914297020011010560:ℝ) (15046748234561/1000000000000:ℝ) (15046753024091879909/1000000000000000000:ℝ) (21593419/25000000000000:ℝ) (8637409/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1205).1 (thetaFirstMode_refined_node_1205).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0607 :
    (-15142202704754247770000391/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (201/256:ℝ) ∧ thetaFirstModeFirst (201/256:ℝ) ≤ (-1211369986185966308259/50000000000000000000000000:ℝ) := by
  have hlo : (15105247164633/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(201/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(201/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(201/256:ℝ)) ≤ (240407525303/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(201/256:ℝ)) (by norm_num : 2*(201/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(201/256:ℝ)) ≤ (755262598639227679/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (201/256:ℝ) (15105247164633/1000000000000:ℝ) (755262598639227679/50000000000000000:ℝ) (81544923/100000000000000:ℝ) (20386329/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1206).1 (thetaFirstMode_refined_node_1206).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

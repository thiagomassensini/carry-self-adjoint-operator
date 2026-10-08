import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0096 :
    (-3678494657931738982296229173327/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2062244582827209/17296952731317760:ℝ) ∧ thetaFirstModeFirst (2062244582827209/17296952731317760:ℝ) ≤ (-3678488739652285102780327/12500000000000000000000000:ℝ) := by
  have hlo : (996891936647/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(2062244582827209/17296952731317760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2062244582827209/17296952731317760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2062244582827209/17296952731317760:ℝ)) ≤ (634641249817/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2062244582827209/17296952731317760:ℝ)) (by norm_num : 2*(2062244582827209/17296952731317760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2062244582827209/17296952731317760:ℝ)) ≤ (1993784507936338481/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2062244582827209/17296952731317760:ℝ) (996891936647/250000000000:ℝ) (1993784507936338481/500000000000000000:ℝ) (3936772777441/100000000000000:ℝ) (1968388887167/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0185).1 (thetaFirstMode_refined_node_0185).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0097 :
    (-728374768609252081346732410117/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (31/256:ℝ) ∧ thetaFirstModeFirst (31/256:ℝ) ≤ (-910466991673405084884663/3125000000000000000000000:ℝ) := by
  have hlo : (4002492042703/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(31/256:ℝ)) ≤ (63701652581/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(31/256:ℝ)) (by norm_num : 2*(31/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(31/256:ℝ)) ≤ (200124665836901533/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (31/256:ℝ) (4002492042703/1000000000000:ℝ) (200124665836901533/50000000000000000:ℝ) (242629959321/6250000000000:ℝ) (3882084295049/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0186).1 (thetaFirstMode_refined_node_0186).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0098 :
    (-7207504145120805056994809388927/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (63/512:ℝ) ∧ thetaFirstModeFirst (63/512:ℝ) ≤ (-360374624006484139939341/1250000000000000000000000:ℝ) := by
  have hlo : (1004539338409/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(63/512:ℝ)) ≤ (639509737999/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(63/512:ℝ)) (by norm_num : 2*(63/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(63/512:ℝ)) ≤ (2009079316329492407/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (63/512:ℝ) (1004539338409/250000000000:ℝ) (2009079316329492407/500000000000000000:ℝ) (382547319749/10000000000000:ℝ) (3825478090361/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0187).1 (thetaFirstMode_refined_node_0187).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0099 :
    (-14408577644800851888832590948399/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2756444578756407/22386559816092160:ℝ) ∧ thetaFirstModeFirst (2756444578756407/22386559816092160:ℝ) ≤ (-900534645139719151767933/3125000000000000000000000:ℝ) := by
  have hlo : (502352616071/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(2756444578756407/22386559816092160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2756444578756407/22386559816092160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2756444578756407/22386559816092160:ℝ)) ≤ (1279230698503/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2756444578756407/22386559816092160:ℝ)) (by norm_num : 2*(2756444578756407/22386559816092160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2756444578756407/22386559816092160:ℝ)) ≤ (4018822207802135279/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2756444578756407/22386559816092160:ℝ) (502352616071/125000000000:ℝ) (4018822207802135279/1000000000000000000:ℝ) (1911546687323/50000000000000:ℝ) (3823098265281/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0191).1 (thetaFirstMode_refined_node_0191).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0100 :
    (-445725857800306196260935340291/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/8:ℝ) ∧ thetaFirstModeFirst (1/8:ℝ) ≤ (-3565801073784060764836029/12500000000000000000000000:ℝ) := by
  have hlo : (2016941988431/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/8:ℝ)) ≤ (80251588543/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/8:ℝ)) (by norm_num : 2*(1/8:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/8:ℝ)) ≤ (252117828805568999/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/8:ℝ) (2016941988431/500000000000:ℝ) (252117828805568999/62500000000000000:ℝ) (1884730660659/50000000000000:ℝ) (1884733080709/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0192).1 (thetaFirstMode_refined_node_0192).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0101 :
    (-1411216093416240496863114963621/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (65/512:ℝ) ∧ thetaFirstModeFirst (65/512:ℝ) ≤ (-441004311101183622189327/1562500000000000000000000:ℝ) := by
  have hlo : (126552254761/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(65/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(65/512:ℝ)) ≤ (1289050950077/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(65/512:ℝ)) (by norm_num : 2*(65/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(65/512:ℝ)) ≤ (4049673441405252661/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (65/512:ℝ) (126552254761/31250000000:ℝ) (4049673441405252661/1000000000000000000:ℝ) (3714040946007/100000000000000:ℝ) (371404573361/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0193).1 (thetaFirstMode_refined_node_0193).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0102 :
    (-440812068793677968734930153603/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (730222341159285/5748281504317952:ℝ) ∧ thetaFirstModeFirst (730222341159285/5748281504317952:ℝ) ≤ (-705298161482869393851891/2500000000000000000000000:ℝ) := by
  have hlo : (202516020149/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(730222341159285/5748281504317952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(730222341159285/5748281504317952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(730222341159285/5748281504317952:ℝ)) ≤ (80578580919/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(730222341159285/5748281504317952:ℝ)) (by norm_num : 2*(730222341159285/5748281504317952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(730222341159285/5748281504317952:ℝ)) ≤ (253145105765063967/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (730222341159285/5748281504317952:ℝ) (202516020149/50000000000:ℝ) (253145105765063967/62500000000000000:ℝ) (3711782621959/100000000000000:ℝ) (1855893703709/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0197).1 (thetaFirstMode_refined_node_0197).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0103 :
    (-13961816701874181469687612947111/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (33/256:ℝ) ∧ thetaFirstModeFirst (33/256:ℝ) ≤ (-3490448474631589902421221/12500000000000000000000000:ℝ) := by
  have hlo : (1016380530253/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(33/256:ℝ)) ≤ (1294096152847/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(33/256:ℝ)) (by norm_num : 2*(33/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(33/256:ℝ)) ≤ (4065523415111065271/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (33/256:ℝ) (1016380530253/250000000000:ℝ) (4065523415111065271/1000000000000000000:ℝ) (3659209265657/100000000000000:ℝ) (3659214001041/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0198).1 (thetaFirstMode_refined_node_0198).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0104 :
    (-3453050645873489593705774321251/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (67/512:ℝ) ∧ thetaFirstModeFirst (67/512:ℝ) ≤ (-1381217995574941985536647/5000000000000000000000000:ℝ) := by
  have hlo : (4081434124697/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(67/512:ℝ)) ≤ (649580550991/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(67/512:ℝ)) (by norm_num : 2*(67/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(67/512:ℝ)) ≤ (2040717711929468663/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (67/512:ℝ) (4081434124697/1000000000000:ℝ) (2040717711929468663/500000000000000000:ℝ) (360496344351/10000000000000:ℝ) (1802484063477/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0199).1 (thetaFirstMode_refined_node_0199).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0105 :
    (-862891861876883622691457190309/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4795188919157943/36622101413148160:ℝ) ∧ thetaFirstModeFirst (4795188919157943/36622101413148160:ℝ) ≤ (-13482663251236455997329/48828125000000000000000:ℝ) := by
  have hlo : (996598633/244140625:ℝ) ≤ Real.pi*Real.exp (2*(4795188919157943/36622101413148160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4795188919157943/36622101413148160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4795188919157943/36622101413148160:ℝ)) ≤ (324840717761/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4795188919157943/36622101413148160:ℝ)) (by norm_num : 2*(4795188919157943/36622101413148160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4795188919157943/36622101413148160:ℝ)) ≤ (1020517325032933273/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4795188919157943/36622101413148160:ℝ) (996598633/244140625:ℝ) (1020517325032933273/250000000000000000:ℝ) (3602818939147/100000000000000:ℝ) (900705905133/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0203).1 (thetaFirstMode_refined_node_0203).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0106 :
    (-426978946296379989904850928447/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17/128:ℝ) ∧ thetaFirstModeFirst (17/128:ℝ) ≤ (-6831651914670080589950893/25000000000000000000000000:ℝ) := by
  have hlo : (4097408406203/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17/128:ℝ)) ≤ (81515367173/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17/128:ℝ)) (by norm_num : 2*(17/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17/128:ℝ)) ≤ (256088106903126589/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17/128:ℝ) (4097408406203/1000000000000:ℝ) (256088106903126589/62500000000000000:ℝ) (1775650306231/50000000000000:ℝ) (1775652622123/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0204).1 (thetaFirstMode_refined_node_0204).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0107 :
    (-1689399421127345730796489727379/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (69/512:ℝ) ∧ thetaFirstModeFirst (69/512:ℝ) ≤ (-6757586546227492336257371/25000000000000000000000000:ℝ) := by
  have hlo : (2056722604639/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(69/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(69/512:ℝ)) ≤ (163668818599/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(69/512:ℝ)) (by norm_num : 2*(69/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(69/512:ℝ)) ≤ (514180814828888207/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (69/512:ℝ) (2056722604639/500000000000:ℝ) (514180814828888207/125000000000000000:ℝ) (3498217875589/100000000000000:ℝ) (3498222455997/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0205).1 (thetaFirstMode_refined_node_0205).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0108 :
    (-844343231971522615162708807799/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (6247526395102641/46332533517852160:ℝ) ∧ thetaFirstModeFirst (6247526395102641/46332533517852160:ℝ) ≤ (-13509469441754495278831749/50000000000000000000000000:ℝ) := by
  have hlo : (4114065578633/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(6247526395102641/46332533517852160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(6247526395102641/46332533517852160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(6247526395102641/46332533517852160:ℝ)) ≤ (327387004633/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(6247526395102641/46332533517852160:ℝ)) (by norm_num : 2*(6247526395102641/46332533517852160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(6247526395102641/46332533517852160:ℝ)) ≤ (1028516722046000369/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (6247526395102641/46332533517852160:ℝ) (4114065578633/1000000000000:ℝ) (1028516722046000369/250000000000000000:ℝ) (3496180167453/100000000000000:ℝ) (874046186471/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0209).1 (thetaFirstMode_refined_node_0209).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0109 :
    (-2673563457772826413547084387181/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (35/256:ℝ) ∧ thetaFirstModeFirst (35/256:ℝ) ≤ (-2673559037571322123658029/10000000000000000000000000:ℝ) := by
  have hlo : (4129544778627/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(35/256:ℝ)) ≤ (262895040389/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(35/256:ℝ)) (by norm_num : 2*(35/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(35/256:ℝ)) ≤ (825909218620799677/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (35/256:ℝ) (4129544778627/1000000000000:ℝ) (825909218620799677/200000000000000000:ℝ) (689142461327/20000000000000:ℝ) (3445716835953/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0210).1 (thetaFirstMode_refined_node_0210).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0110 :
    (-13221199352380881511986870454077/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (71/512:ℝ) ∧ thetaFirstModeFirst (71/512:ℝ) ≤ (-3305294356720900482817879/12500000000000000000000000:ℝ) := by
  have hlo : (1036426839977/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(71/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(71/512:ℝ)) ≤ (1319619912423/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(71/512:ℝ)) (by norm_num : 2*(71/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(71/512:ℝ)) ≤ (4145708679528709839/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (71/512:ℝ) (1036426839977/250000000000:ℝ) (4145708679528709839/1000000000000000000:ℝ) (3393780950527/100000000000000:ℝ) (3393785429043/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0211).1 (thetaFirstMode_refined_node_0211).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0111 :
    (-3303928266481065202744776473013/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8078499778926159/58225454071144960:ℝ) ∧ thetaFirstModeFirst (8078499778926159/58225454071144960:ℝ) ≤ (-13215691147006979542761091/50000000000000000000000000:ℝ) := by
  have hlo : (4146315017661/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(8078499778926159/58225454071144960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8078499778926159/58225454071144960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8078499778926159/58225454071144960:ℝ)) ≤ (659906667967/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8078499778926159/58225454071144960:ℝ)) (by norm_num : 2*(8078499778926159/58225454071144960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8078499778926159/58225454071144960:ℝ)) ≤ (2073158168738451431/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8078499778926159/58225454071144960:ℝ) (4146315017661/1000000000000:ℝ) (2073158168738451431/500000000000000000:ℝ) (3391843597631/100000000000000:ℝ) (1695924037123/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0215).1 (thetaFirstMode_refined_node_0215).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0112 :
    (-13075348738493213624644443723657/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/64:ℝ) ∧ thetaFirstModeFirst (9/64:ℝ) ≤ (-102150992097249633999117/390625000000000000000000:ℝ) := by
  have hlo : (32515103123/7812500000:ℝ) ≤ Real.pi*Real.exp (2*(9/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/64:ℝ)) ≤ (1324784758729/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/64:ℝ)) (by norm_num : 2*(9/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/64:ℝ)) ≤ (4161934524529715297/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/64:ℝ) (32515103123/7812500000:ℝ) (4161934524529715297/1000000000000000000:ℝ) (3342420823879/100000000000000:ℝ) (3342425251881/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0216).1 (thetaFirstMode_refined_node_0216).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0113 :
    (-404071015400915320485169520523/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (73/512:ℝ) ∧ thetaFirstModeFirst (73/512:ℝ) ≤ (-2586050183630350436935147/10000000000000000000000000:ℝ) := by
  have hlo : (4178222545721/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(73/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(73/512:ℝ)) ≤ (166246227459/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(73/512:ℝ)) (by norm_num : 2*(73/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(73/512:ℝ)) ≤ (522277984461602187/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (73/512:ℝ) (4178222545721/1000000000000:ℝ) (522277984461602187/125000000000000000:ℝ) (658325783107/20000000000000:ℝ) (822908323329/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0217).1 (thetaFirstMode_refined_node_0217).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0114 :
    (-12924992736998081823136428581811/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (10371833391193857/72708564804252160:ℝ) ∧ thetaFirstModeFirst (10371833391193857/72708564804252160:ℝ) ≤ (-807810698044961927923971/3125000000000000000000000:ℝ) := by
  have hlo : (261176138887/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(10371833391193857/72708564804252160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(10371833391193857/72708564804252160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(10371833391193857/72708564804252160:ℝ)) ≤ (1330159429421/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(10371833391193857/72708564804252160:ℝ)) (by norm_num : 2*(10371833391193857/72708564804252160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(10371833391193857/72708564804252160:ℝ)) ≤ (4178819552353007653/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (10371833391193857/72708564804252160:ℝ) (261176138887/62500000000:ℝ) (4178819552353007653/1000000000000000000:ℝ) (3289785996133/100000000000000:ℝ) (3289790372087/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0221).1 (thetaFirstMode_refined_node_0221).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0115 :
    (-1278597752671478576101494157989/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (37/256:ℝ) ∧ thetaFirstModeFirst (37/256:ℝ) ≤ (-127859561273107762415317/500000000000000000000000:ℝ) := by
  have hlo : (1048643911599/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(37/256:ℝ)) ≤ (133517517437/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(37/256:ℝ)) (by norm_num : 2*(37/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(37/256:ℝ)) ≤ (419457698157457141/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (37/256:ℝ) (1048643911599/250000000000:ℝ) (419457698157457141/100000000000000000:ℝ) (129656087483/4000000000000:ℝ) (3241406514929/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0222).1 (thetaFirstMode_refined_node_0222).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0116 :
    (-197538603380517279198727147167/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (75/512:ℝ) ∧ thetaFirstModeFirst (75/512:ℝ) ≤ (-3160612348033087623930969/12500000000000000000000000:ℝ) := by
  have hlo : (2105496375649/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(75/512:ℝ)) ≤ (1340400902249/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(75/512:ℝ)) (by norm_num : 2*(75/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(75/512:ℝ)) ≤ (4210994091699142657/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (75/512:ℝ) (2105496375649/500000000000:ℝ) (4210994091699142657/1000000000000000000:ℝ) (1595868786681/50000000000000:ℝ) (49870966431/1562500000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0223).1 (thetaFirstMode_refined_node_0223).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0117 :
    (-2527477475311461353611027872753/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2645329456026675/18050233071498752:ℝ) ∧ thetaFirstModeFirst (2645329456026675/18050233071498752:ℝ) ≤ (-1579670769819521443758741/6250000000000000000000000:ℝ) := by
  have hlo : (526447139861/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(2645329456026675/18050233071498752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2645329456026675/18050233071498752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2645329456026675/18050233071498752:ℝ)) ≤ (1340586912269/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2645329456026675/18050233071498752:ℝ)) (by norm_num : 2*(2645329456026675/18050233071498752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2645329456026675/18050233071498752:ℝ)) ≤ (4211578459475904517/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2645329456026675/18050233071498752:ℝ) (526447139861/125000000000:ℝ) (4211578459475904517/1000000000000000000:ℝ) (3189983630081/100000000000000:ℝ) (637997581309/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0227).1 (thetaFirstMode_refined_node_0227).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0118 :
    (-249995168035775104043002072727/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19/128:ℝ) ∧ thetaFirstModeFirst (19/128:ℝ) ≤ (-3124934338153495048876043/12500000000000000000000000:ℝ) := by
  have hlo : (4227474110931/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19/128:ℝ)) ≤ (26912941661/20000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19/128:ℝ)) (by norm_num : 2*(19/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19/128:ℝ)) ≤ (84549509131605973/20000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19/128:ℝ) (4227474110931/1000000000000:ℝ) (84549509131605973/20000000000000000:ℝ) (785657995753/25000000000000:ℝ) (3142636211899/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0228).1 (thetaFirstMode_refined_node_0228).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0119 :
    (-6178923693179714324065880414761/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (77/512:ℝ) ∧ thetaFirstModeFirst (77/512:ℝ) ≤ (-3089456628025361405326801/12500000000000000000000000:ℝ) := by
  have hlo : (2122009988391/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(77/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(77/512:ℝ)) ≤ (1350913796821/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(77/512:ℝ)) (by norm_num : 2*(77/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(77/512:ℝ)) ≤ (4244021327696275853/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (77/512:ℝ) (2122009988391/500000000000:ℝ) (4244021327696275853/1000000000000000000:ℝ) (1547041149511/50000000000000:ℝ) (1547043239437/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0229).1 (thetaFirstMode_refined_node_0229).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0120 :
    (-1544118923500118761735787114851/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (16759748134830393/111391385333532160:ℝ) ∧ thetaFirstModeFirst (16759748134830393/111391385333532160:ℝ) ≤ (-1235293051978227346567271/5000000000000000000000000:ℝ) := by
  have hlo : (4244593655967/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(16759748134830393/111391385333532160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(16759748134830393/111391385333532160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(16759748134830393/111391385333532160:ℝ)) ≤ (168887050577/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(16759748134830393/111391385333532160:ℝ)) (by norm_num : 2*(16759748134830393/111391385333532160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(16759748134830393/111391385333532160:ℝ)) ≤ (530574375883349161/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (16759748134830393/111391385333532160:ℝ) (4244593655967/1000000000000:ℝ) (530574375883349161/125000000000000000:ℝ) (309241229113/10000000000000:ℝ) (3092416469291/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0233).1 (thetaFirstMode_refined_node_0233).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0121 :
    (-61083719677945524088057453319/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (39/256:ℝ) ∧ thetaFirstModeFirst (39/256:ℝ) ≤ (-1527090404511010918841721/6250000000000000000000000:ℝ) := by
  have hlo : (4260630601321/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(39/256:ℝ)) ≤ (169525140491/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(39/256:ℝ)) (by norm_num : 2*(39/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(39/256:ℝ)) ≤ (532578994690542163/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (39/256:ℝ) (4260630601321/1000000000000:ℝ) (532578994690542163/125000000000000000:ℝ) (380760672401/12500000000000:ℝ) (121843580413/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0234).1 (thetaFirstMode_refined_node_0234).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0122 :
    (-18869459807369896341370713753/78125000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (79/512:ℝ) ∧ thetaFirstModeFirst (79/512:ℝ) ≤ (-3019108437952439639708251/12500000000000000000000000:ℝ) := by
  have hlo : (2138653119003/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(79/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(79/512:ℝ)) ≤ (1361509145047/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(79/512:ℝ)) (by norm_num : 2*(79/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(79/512:ℝ)) ≤ (4277307599515639871/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (79/512:ℝ) (2138653119003/500000000000:ℝ) (4277307599515639871/1000000000000000000:ℝ) (1499319028417/50000000000000:ℝ) (4685378343/156250000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0235).1 (thetaFirstMode_refined_node_0235).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0123 :
    (-6035868455077975671958567201281/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21108185233275591/136744035433576960:ℝ) ∧ thetaFirstModeFirst (21108185233275591/136744035433576960:ℝ) ≤ (-603585819556297752511029/2500000000000000000000000:ℝ) := by
  have hlo : (1069467450643/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(21108185233275591/136744035433576960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21108185233275591/136744035433576960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21108185233275591/136744035433576960:ℝ)) ≤ (680844266629/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21108185233275591/136744035433576960:ℝ)) (by norm_num : 2*(21108185233275591/136744035433576960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21108185233275591/136744035433576960:ℝ)) ≤ (2138935582131799997/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21108185233275591/136744035433576960:ℝ) (1069467450643/250000000000:ℝ) (2138935582131799997/500000000000000000:ℝ) (599409463703/20000000000000:ℝ) (2997051399573/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0239).1 (thetaFirstMode_refined_node_0239).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0124 :
    (-5968492248843275032829280057421/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/32:ℝ) ∧ thetaFirstModeFirst (5/32:ℝ) ≤ (-93257532399889340404537/390625000000000000000000:ℝ) := by
  have hlo : (536755892661/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/32:ℝ)) ≤ (683418970587/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/32:ℝ)) (by norm_num : 2*(5/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/32:ℝ)) ≤ (2147024254063325091/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/32:ℝ) (536755892661/125000000000:ℝ) (2147024254063325091/500000000000000000:ℝ) (184483571317/6250000000000:ℝ) (2951741175631/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0240).1 (thetaFirstMode_refined_node_0240).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0125 :
    (-589917027331784601213058127053/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (81/512:ℝ) ∧ thetaFirstModeFirst (81/512:ℝ) ≤ (-2949580092583559481467759/12500000000000000000000000:ℝ) := by
  have hlo : (1077713391653/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(81/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(81/512:ℝ)) ≤ (68609379681/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(81/512:ℝ)) (by norm_num : 2*(81/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(81/512:ℝ)) ≤ (215542746940171833/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (81/512:ℝ) (1077713391653/250000000000:ℝ) (215542746940171833/50000000000000000:ℝ) (2905379417603/100000000000000:ℝ) (2905383404341/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0241).1 (thetaFirstMode_refined_node_0241).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0126 :
    (-23034753518307205617771900509/97656250000000000000000000000:ℝ) ≤ thetaFirstModeFirst (26432093791371609/167009112048540160:ℝ) ∧ thetaFirstModeFirst (26432093791371609/167009112048540160:ℝ) ≤ (-11793773630800013323581909/50000000000000000000000000:ℝ) := by
  have hlo : (4311407548249/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(26432093791371609/167009112048540160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(26432093791371609/167009112048540160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(26432093791371609/167009112048540160:ℝ)) ≤ (42886372859/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(26432093791371609/167009112048540160:ℝ)) (by norm_num : 2*(26432093791371609/167009112048540160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(26432093791371609/167009112048540160:ℝ)) ≤ (134731528769224387/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (26432093791371609/167009112048540160:ℝ) (4311407548249/1000000000000:ℝ) (134731528769224387/31250000000000000:ℝ) (2903863621341/100000000000000:ℝ) (181491725407/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0245).1 (thetaFirstMode_refined_node_0245).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0127 :
    (-2915132057808324045787876744147/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (41/256:ℝ) ∧ thetaFirstModeFirst (41/256:ℝ) ≤ (-364390882154194560059549/1562500000000000000000000:ℝ) := by
  have hlo : (2163862885213/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(41/256:ℝ)) ≤ (344389546003/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(41/256:ℝ)) (by norm_num : 2*(41/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(41/256:ℝ)) ≤ (1081931786996202779/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (41/256:ℝ) (2163862885213/500000000000:ℝ) (1081931786996202779/250000000000000000:ℝ) (178722603073/6250000000000:ℝ) (2859565588393/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0246).1 (thetaFirstMode_refined_node_0246).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

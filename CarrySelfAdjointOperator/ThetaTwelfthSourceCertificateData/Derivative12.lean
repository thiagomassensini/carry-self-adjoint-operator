import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0384 :
    (-226422603241849660277050912761/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (746687107677957320457/1511019264768615708160:ℝ) ∧ thetaFirstModeFirst (746687107677957320457/1511019264768615708160:ℝ) ≤ (-452843841259648162916163/50000000000000000000000000:ℝ) := by
  have hlo : (8440589035421/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(746687107677957320457/1511019264768615708160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(746687107677957320457/1511019264768615708160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(746687107677957320457/1511019264768615708160:ℝ)) ≤ (1343361747073/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(746687107677957320457/1511019264768615708160:ℝ)) (by norm_num : 2*(746687107677957320457/1511019264768615708160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(746687107677957320457/1511019264768615708160:ℝ)) ≤ (4220295861072307289/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (746687107677957320457/1511019264768615708160:ℝ) (8440589035421/1000000000000:ℝ) (4220295861072307289/500000000000000000:ℝ) (55288311903/100000000000000:ℝ) (55288460449/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0761).1 (thetaFirstMode_refined_node_0761).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0385 :
    (-110114243309089027794124816047/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (127/256:ℝ) ∧ thetaFirstModeFirst (127/256:ℝ) ≤ (-3441059693723920490943/390625000000000000000000:ℝ) := by
  have hlo : (132394933139/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(127/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(127/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(127/256:ℝ)) ≤ (674281997861/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(127/256:ℝ)) (by norm_num : 2*(127/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(127/256:ℝ)) ≤ (2118319604506132573/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (127/256:ℝ) (132394933139/15625000000:ℝ) (2118319604506132573/250000000000000000:ℝ) (26781033237/50000000000000:ℝ) (53562210939/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0762).1 (thetaFirstMode_refined_node_0762).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0386 :
    (-53528225168314324767547733369/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (255/512:ℝ) ∧ thetaFirstModeFirst (255/512:ℝ) ≤ (-428224501401092725678359/50000000000000000000000000:ℝ) := by
  have hlo : (8506439184401/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(255/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(255/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(255/512:ℝ)) ≤ (1353842125967/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(255/512:ℝ)) (by norm_num : 2*(255/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(255/512:ℝ)) ≤ (4253220946043045431/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (255/512:ℝ) (8506439184401/1000000000000:ℝ) (4253220946043045431/500000000000000000:ℝ) (51865518759/100000000000000:ℝ) (12966414799/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0763).1 (thetaFirstMode_refined_node_0763).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0387 :
    (-428099420546085749331760911113/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (160303981759231989195/321852051581633495552:ℝ) ∧ thetaFirstModeFirst (160303981759231989195/321852051581633495552:ℝ) ≤ (-107024530235055555136959/12500000000000000000000000:ℝ) := by
  have hlo : (8506786649329/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(160303981759231989195/321852051581633495552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(160303981759231989195/321852051581633495552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(160303981759231989195/321852051581633495552:ℝ)) ≤ (2707794853479/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(160303981759231989195/321852051581633495552:ℝ)) (by norm_num : 2*(160303981759231989195/321852051581633495552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(160303981759231989195/321852051581633495552:ℝ)) ≤ (8506789357125652047/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (160303981759231989195/321852051581633495552:ℝ) (8506786649329/1000000000000:ℝ) (8506789357125652047/1000000000000000000:ℝ) (12962007471/25000000000000:ℝ) (51848170279/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0767).1 (thetaFirstMode_refined_node_0767).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0388 :
    (-20814002309616788849570414031/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/2:ℝ) ∧ thetaFirstModeFirst (1/2:ℝ) ≤ (-13008711816146694139701/1562500000000000000000000:ℝ) := by
  have hlo : (533733277877/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(1/2:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/2:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/2:ℝ)) ≤ (135914091423/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/2:ℝ)) (by norm_num : 2*(1/2:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/2:ℝ)) ≤ (426986758215856839/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/2:ℝ) (533733277877/62500000000:ℝ) (426986758215856839/50000000000000000:ℝ) (25108094913/50000000000000:ℝ) (50216326329/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0768).1 (thetaFirstMode_refined_node_0768).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0389 :
    (-80922921981829579026486668391/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (257/512:ℝ) ∧ thetaFirstModeFirst (257/512:ℝ) ≤ (-80922674616230204865423/10000000000000000000000000:ℝ) := by
  have hlo : (1714631202761/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(257/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(257/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(257/512:ℝ)) ≤ (2728920882727/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(257/512:ℝ)) (by norm_num : 2*(257/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(257/512:ℝ)) ≤ (8573158742728964111/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (257/512:ℝ) (1714631202761/200000000000:ℝ) (8573158742728964111/1000000000000000000:ℝ) (48612974743/100000000000000:ℝ) (9722621481/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0769).1 (thetaFirstMode_refined_node_0769).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0390 :
    (-80899005738204708052923487899/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (859903185597392841993/1713045360379148700160:ℝ) ∧ thetaFirstModeFirst (859903185597392841993/1713045360379148700160:ℝ) ≤ (-25280862011307407378219/3125000000000000000000000:ℝ) := by
  have hlo : (8573503479089/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(859903185597392841993/1713045360379148700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(859903185597392841993/1713045360379148700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(859903185597392841993/1713045360379148700160:ℝ)) ≤ (545806296877/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(859903185597392841993/1713045360379148700160:ℝ)) (by norm_num : 2*(859903185597392841993/1713045360379148700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(859903185597392841993/1713045360379148700160:ℝ)) ≤ (1714701241624705061/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (859903185597392841993/1713045360379148700160:ℝ) (8573503479089/1000000000000:ℝ) (1714701241624705061/200000000000000000:ℝ) (3037286171/6250000000000:ℝ) (48596711359/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0773).1 (thetaFirstMode_refined_node_0773).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0391 :
    (-15728977823405558655240299919/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (129/256:ℝ) ∧ thetaFirstModeFirst (129/256:ℝ) ≤ (-393223239393011792438247/50000000000000000000000000:ℝ) := by
  have hlo : (8606710397723/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(129/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(129/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(129/256:ℝ)) ≤ (109584063083/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(129/256:ℝ)) (by norm_num : 2*(129/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(129/256:ℝ)) ≤ (344268525493111219/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (129/256:ℝ) (8606710397723/1000000000000:ℝ) (344268525493111219/40000000000000000:ℝ) (47054788389/100000000000000:ℝ) (47054917301/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0774).1 (thetaFirstMode_refined_node_0774).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0392 :
    (-382104557752330964505476709017/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (259/512:ℝ) ∧ thetaFirstModeFirst (259/512:ℝ) ≤ (-191051690789112102990023/25000000000000000000000000:ℝ) := by
  have hlo : (8640396109787/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(259/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(259/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(259/512:ℝ)) ≤ (2750324074479/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(259/512:ℝ)) (by norm_num : 2*(259/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(259/512:ℝ)) ≤ (8640398860114705047/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (259/512:ℝ) (8640396109787/1000000000000:ℝ) (8640398860114705047/1000000000000000000:ℝ) (22770282629/50000000000000:ℝ) (45540690511/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0775).1 (thetaFirstMode_refined_node_0775).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0393 :
    (-190995732180727575413904541487/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (922036494355905427191/1822640620152625231360:ℝ) ∧ thetaFirstModeFirst (922036494355905427191/1822640620152625231360:ℝ) ≤ (-47748786062492146122023/6250000000000000000000000:ℝ) := by
  have hlo : (8640743596463/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(922036494355905427191/1822640620152625231360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(922036494355905427191/1822640620152625231360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(922036494355905427191/1822640620152625231360:ℝ)) ≤ (1375217341473/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(922036494355905427191/1822640620152625231360:ℝ)) (by norm_num : 2*(922036494355905427191/1822640620152625231360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(922036494355905427191/1822640620152625231360:ℝ)) ≤ (4320373173450186489/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (922036494355905427191/1822640620152625231360:ℝ) (8640743596463/1000000000000:ℝ) (4320373173450186489/500000000000000000:ℝ) (5690650121/12500000000000:ℝ) (45525326183/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0779).1 (thetaFirstMode_refined_node_0779).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0394 :
    (-371250002749962386403365926677/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (65/128:ℝ) ∧ thetaFirstModeFirst (65/128:ℝ) ≤ (-11601526750375822343/1562500000000000000000:ℝ) := by
  have hlo : (271069177/31250000:ℝ) ≤ Real.pi*Real.exp (2*(65/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(65/128:ℝ)) ≤ (2761088538551/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(65/128:ℝ)) (by norm_num : 2*(65/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(65/128:ℝ)) ≤ (8674216425092051743/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (65/128:ℝ) (271069177/31250000:ℝ) (8674216425092051743/1000000000000000000:ℝ) (44069259259/100000000000000:ℝ) (44069380939/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0780).1 (thetaFirstMode_refined_node_0780).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0395 :
    (-45081986143896401928044340249/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (261/512:ℝ) ∧ thetaFirstModeFirst (261/512:ℝ) ≤ (-180327385626682680938823/25000000000000000000000000:ℝ) := by
  have hlo : (4354081788189/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(261/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(261/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(261/512:ℝ)) ≤ (346486891693/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(261/512:ℝ)) (by norm_num : 2*(261/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(261/512:ℝ)) ≤ (1088520793534486949/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (261/512:ℝ) (4354081788189/500000000000:ℝ) (1088520793534486949/125000000000000000:ℝ) (42639843507/100000000000000:ℝ) (42639961701/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0781).1 (thetaFirstMode_refined_node_0781).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0396 :
    (-180274491621043331871067780681/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (988128929174544916209/1938322640485932981760:ℝ) ∧ thetaFirstModeFirst (988128929174544916209/1938322640485932981760:ℝ) ≤ (-360547865626019219851131/50000000000000000000000000:ℝ) := by
  have hlo : (8708511105161/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(988128929174544916209/1938322640485932981760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(988128929174544916209/1938322640485932981760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(988128929174544916209/1938322640485932981760:ℝ)) ≤ (1386002877707/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(988128929174544916209/1938322640485932981760:ℝ)) (by norm_num : 2*(988128929174544916209/1938322640485932981760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(988128929174544916209/1938322640485932981760:ℝ)) ≤ (4354256938584167251/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (988128929174544916209/1938322640485932981760:ℝ) (8708511105161/1000000000000:ℝ) (4354256938584167251/500000000000000000:ℝ) (42625452771/100000000000000:ℝ) (42625570931/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0785).1 (thetaFirstMode_refined_node_0785).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0397 :
    (-35031737807591648008498859663/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (131/256:ℝ) ∧ thetaFirstModeFirst (131/256:ℝ) ≤ (-43789536054153393610579/6250000000000000000000000:ℝ) := by
  have hlo : (2185561591239/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(131/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(131/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(131/256:ℝ)) ≤ (1391372012177/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(131/256:ℝ)) (by norm_num : 2*(131/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(131/256:ℝ)) ≤ (4371124573851177961/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (131/256:ℝ) (2185561591239/250000000000:ℝ) (4371124573851177961/500000000000000000:ℝ) (20625655061/50000000000000:ℝ) (8250284983/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0786).1 (thetaFirstMode_refined_node_0786).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0398 :
    (-340229683566364555221357199/50000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (263/512:ℝ) ∧ thetaFirstModeFirst (263/512:ℝ) ≤ (-13609144864202792869397/2000000000000000000000000:ℝ) := by
  have hlo : (8776462549797/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(263/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(263/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(263/512:ℝ)) ≤ (1396817688261/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(263/512:ℝ)) (by norm_num : 2*(263/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(263/512:ℝ)) ≤ (4388232671716939773/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (263/512:ℝ) (8776462549797/1000000000000:ℝ) (4388232671716939773/500000000000000000:ℝ) (1596106801/4000000000000:ℝ) (79805563/200000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0787).1 (thetaFirstMode_refined_node_0787).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0399 :
    (-170064337945951876666314350811/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1058399498889348955407/2060378912321919132160:ℝ) ∧ thetaFirstModeFirst (1058399498889348955407/2060378912321919132160:ℝ) ≤ (-170063807107511184771491/25000000000000000000000000:ℝ) := by
  have hlo : (4388405070547/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1058399498889348955407/2060378912321919132160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1058399498889348955407/2060378912321919132160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1058399498889348955407/2060378912321919132160:ℝ)) ≤ (2793746018291/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1058399498889348955407/2060378912321919132160:ℝ)) (by norm_num : 2*(1058399498889348955407/2060378912321919132160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1058399498889348955407/2060378912321919132160:ℝ)) ≤ (8776812934840877563/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1058399498889348955407/2060378912321919132160:ℝ) (4388405070547/500000000000:ℝ) (8776812934840877563/1000000000000000000:ℝ) (39889197553/100000000000000:ℝ) (19944654497/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0791).1 (thetaFirstMode_refined_node_0791).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0400 :
    (-41298509106952788516264014647/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (33/64:ℝ) ∧ thetaFirstModeFirst (33/64:ℝ) ≤ (-165193519006685821039/25000000000000000000000:ℝ) := by
  have hlo : (8810812653/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(33/64:ℝ)) ≤ (1402284678119/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(33/64:ℝ)) (by norm_num : 2*(33/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(33/64:ℝ)) ≤ (4405407728785903567/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (33/64:ℝ) (8810812653/1000000000:ℝ) (4405407728785903567/500000000000000000:ℝ) (19296476363/50000000000000:ℝ) (9648265241/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0792).1 (thetaFirstMode_refined_node_0792).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0401 :
    (-20049241668081830805981259/3125000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (265/512:ℝ) ∧ thetaFirstModeFirst (265/512:ℝ) ≤ (-20049178650430955229361/3125000000000000000000000:ℝ) := by
  have hlo : (552831074919/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(265/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(265/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(265/512:ℝ)) ≤ (140777306517/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(265/512:ℝ)) (by norm_num : 2*(265/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(265/512:ℝ)) ≤ (442265000712661581/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (265/512:ℝ) (552831074919/62500000000:ℝ) (442265000712661581/50000000000000000:ℝ) (37321206119/100000000000000:ℝ) (46651639/125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0793).1 (thetaFirstMode_refined_node_0793).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0402 :
    (-64138495771534099639337229171/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (226615503159325427085/437821630895601469952:ℝ) ∧ thetaFirstModeFirst (226615503159325427085/437821630895601469952:ℝ) ≤ (-4008643385456815903547/625000000000000000000000:ℝ) := by
  have hlo : (552852804539/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(226615503159325427085/437821630895601469952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(226615503159325427085/437821630895601469952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(226615503159325427085/437821630895601469952:ℝ)) ≤ (2815656798409/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(226615503159325427085/437821630895601469952:ℝ)) (by norm_num : 2*(226615503159325427085/437821630895601469952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(226615503159325427085/437821630895601469952:ℝ)) ≤ (8845647688284125537/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (226615503159325427085/437821630895601469952:ℝ) (552852804539/62500000000:ℝ) (8845647688284125537/1000000000000000000:ℝ) (7461719873/20000000000000:ℝ) (7461740883/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0797).1 (thetaFirstMode_refined_node_0797).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0403 :
    (-311424439556492252570717187369/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (133/256:ℝ) ∧ thetaFirstModeFirst (133/256:ℝ) ≤ (-62284691457300831866291/10000000000000000000000000:ℝ) := by
  have hlo : (1775983342621/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(133/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(133/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(133/256:ℝ)) ≤ (2826565866321/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(133/256:ℝ)) (by norm_num : 2*(133/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(133/256:ℝ)) ≤ (8879919539672989353/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (133/256:ℝ) (1775983342621/200000000000:ℝ) (8879919539672989353/1000000000000000000:ℝ) (36086496271/100000000000000:ℝ) (36086598273/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0798).1 (thetaFirstMode_refined_node_0798).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0404 :
    (-75573304986733278281958130641/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (267/512:ℝ) ∧ thetaFirstModeFirst (267/512:ℝ) ≤ (-37786532893148897920281/6250000000000000000000000:ℝ) := by
  have hlo : (4457335862227/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(267/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(267/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(267/512:ℝ)) ≤ (2837628732329/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(267/512:ℝ)) (by norm_num : 2*(267/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(267/512:ℝ)) ≤ (8914674562083660097/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (267/512:ℝ) (4457335862227/500000000000:ℝ) (8914674562083660097/1000000000000000000:ℝ) (8721976803/25000000000000:ℝ) (8722001553/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0799).1 (thetaFirstMode_refined_node_0799).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0405 :
    (-151101592043496668191229170167/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1212402996478512506943/2324820661745853468160:ℝ) ∧ thetaFirstModeFirst (1212402996478512506943/2324820661745853468160:ℝ) ≤ (-37775278442540116873461/6250000000000000000000000:ℝ) := by
  have hlo : (8915019500817/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1212402996478512506943/2324820661745853468160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1212402996478512506943/2324820661745853468160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1212402996478512506943/2324820661745853468160:ℝ)) ≤ (2837739433007/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1212402996478512506943/2324820661745853468160:ℝ)) (by norm_num : 2*(1212402996478512506943/2324820661745853468160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1212402996478512506943/2324820661745853468160:ℝ)) ≤ (8915022338558760151/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1212402996478512506943/2324820661745853468160:ℝ) (8915019500817/1000000000000:ℝ) (8915022338558760151/1000000000000000000:ℝ) (4359514533/12500000000000:ℝ) (17438107617/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0803).1 (thetaFirstMode_refined_node_0803).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0406 :
    (-293389690549900393466698630191/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (67/128:ℝ) ∧ thetaFirstModeFirst (67/128:ℝ) ≤ (-293388758675482340040333/50000000000000000000000000:ℝ) := by
  have hlo : (8949562763071/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(67/128:ℝ)) ≤ (2848734897171/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(67/128:ℝ)) (by norm_num : 2*(67/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(67/128:ℝ)) ≤ (8949565611808133403/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (67/128:ℝ) (8949562763071/1000000000000:ℝ) (8949565611808133403/1000000000000000000:ℝ) (33724540723/100000000000000:ℝ) (33724636797/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0804).1 (thetaFirstMode_refined_node_0804).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0407 :
    (-284709388444480625302142068323/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (269/512:ℝ) ∧ thetaFirstModeFirst (269/512:ℝ) ≤ (-17794280061090830197647/3125000000000000000000000:ℝ) := by
  have hlo : (1123073795169/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(269/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(269/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(269/512:ℝ)) ≤ (2859884530313/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(269/512:ℝ)) (by norm_num : 2*(269/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(269/512:ℝ)) ≤ (8984593221239608609/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (269/512:ℝ) (1123073795169/125000000000:ℝ) (8984593221239608609/1000000000000000000:ℝ) (16297758063/50000000000000:ℝ) (32595609347/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0805).1 (thetaFirstMode_refined_node_0805).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0408 :
    (-2846244469767174472472746191/500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1296627075007226251641/2467838661023287068160:ℝ) ∧ thetaFirstModeFirst (1296627075007226251641/2467838661023287068160:ℝ) ≤ (-142311769879255194544643/25000000000000000000000000:ℝ) := by
  have hlo : (4492469129851/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1296627075007226251641/2467838661023287068160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1296627075007226251641/2467838661023287068160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1296627075007226251641/2467838661023287068160:ℝ)) ≤ (142999763491/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1296627075007226251641/2467838661023287068160:ℝ)) (by norm_num : 2*(1296627075007226251641/2467838661023287068160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1296627075007226251641/2467838661023287068160:ℝ)) ≤ (449247055984981163/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1296627075007226251641/2467838661023287068160:ℝ) (4492469129851/500000000000:ℝ) (449247055984981163/50000000000000000:ℝ) (32584493593/100000000000000:ℝ) (6516917357/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0809).1 (thetaFirstMode_refined_node_0809).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0409 :
    (-5524958105821141429457854611/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (135/256:ℝ) ∧ thetaFirstModeFirst (135/256:ℝ) ≤ (-27624702171520674045439/5000000000000000000000000:ℝ) := by
  have hlo : (9019755053777/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(135/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(135/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(135/256:ℝ)) ≤ (574215560377/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(135/256:ℝ)) (by norm_num : 2*(135/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(135/256:ℝ)) ≤ (1803951584971460561/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (135/256:ℝ) (9019755053777/1000000000000:ℝ) (1803951584971460561/200000000000000000:ℝ) (3149997007/10000000000000:ℝ) (3150006051/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0810).1 (thetaFirstMode_refined_node_0810).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0410 :
    (-67000221856591676564060508209/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (271/512:ℝ) ∧ thetaFirstModeFirst (271/512:ℝ) ≤ (-33500003403649176955953/6250000000000000000000000:ℝ) := by
  have hlo : (2263764344229/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(271/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(271/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(271/512:ℝ)) ≤ (2882314882683/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(271/512:ℝ)) (by norm_num : 2*(271/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(271/512:ℝ)) ≤ (9055060259232734019/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (271/512:ℝ) (2263764344229/250000000000:ℝ) (9055060259232734019/1000000000000000000:ℝ) (15218528157/50000000000000:ℝ) (7609286011/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0811).1 (thetaFirstMode_refined_node_0811).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0411 :
    (-1339603963847844488296349709/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1386012428812593345159/2618496675601163368960:ℝ) ∧ thetaFirstModeFirst (1386012428812593345159/2618496675601163368960:ℝ) ≤ (-8372497899909949465901/1562500000000000000000000:ℝ) := by
  have hlo : (9055405416527/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1386012428812593345159/2618496675601163368960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1386012428812593345159/2618496675601163368960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1386012428812593345159/2618496675601163368960:ℝ)) ≤ (576485133431/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1386012428812593345159/2618496675601163368960:ℝ)) (by norm_num : 2*(1386012428812593345159/2618496675601163368960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1386012428812593345159/2618496675601163368960:ℝ)) ≤ (1811081659790895583/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1386012428812593345159/2618496675601163368960:ℝ) (9055405416527/1000000000000:ℝ) (1811081659790895583/200000000000000000:ℝ) (950836163/3125000000000:ℝ) (760671123/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0815).1 (thetaFirstMode_refined_node_0815).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0412 :
    (-6499100901141437094665873439/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17/32:ℝ) ∧ thetaFirstModeFirst (17/32:ℝ) ≤ (-1624769991990547029999/312500000000000000000000:ℝ) := by
  have hlo : (4545248934721/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17/32:ℝ)) ≤ (723398986043/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17/32:ℝ)) (by norm_num : 2*(17/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17/32:ℝ)) ≤ (2272625190759786499/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17/32:ℝ) (4545248934721/500000000000:ℝ) (2272625190759786499/250000000000000000:ℝ) (367574319/1250000000000:ℝ) (2940603061/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0816).1 (thetaFirstMode_refined_node_0816).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0413 :
    (-984894950204929308653148953/195312500000000000000000000000:ℝ) ≤ thetaFirstModeFirst (273/512:ℝ) ∧ thetaFirstModeFirst (273/512:ℝ) ≤ (-126066146149654497588761/25000000000000000000000000:ℝ) := by
  have hlo : (9126077072133/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(273/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(273/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(273/512:ℝ)) ≤ (363115144811/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(273/512:ℝ)) (by norm_num : 2*(273/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(273/512:ℝ)) ≤ (1140759997132223923/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (273/512:ℝ) (9126077072133/1000000000000:ℝ) (1140759997132223923/125000000000000000:ℝ) (14202912517/50000000000000:ℝ) (887684611/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0817).1 (thetaFirstMode_refined_node_0817).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0414 :
    (-126028810762700441259518644517/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1480833717501674392857/2777141897728678812160:ℝ) ∧ thetaFirstModeFirst (1480833717501674392857/2777141897728678812160:ℝ) ≤ (-252056806790288468012721/50000000000000000000000000:ℝ) := by
  have hlo : (9126425272021/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1480833717501674392857/2777141897728678812160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1480833717501674392857/2777141897728678812160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1480833717501674392857/2777141897728678812160:ℝ)) ≤ (2905031993977/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1480833717501674392857/2777141897728678812160:ℝ)) (by norm_num : 2*(1480833717501674392857/2777141897728678812160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1480833717501674392857/2777141897728678812160:ℝ)) ≤ (9126428177054185361/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1480833717501674392857/2777141897728678812160:ℝ) (9126425272021/1000000000000:ℝ) (9126428177054185361/1000000000000000000:ℝ) (28396206701/100000000000000:ℝ) (14198144597/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0821).1 (thetaFirstMode_refined_node_0821).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0415 :
    (-244503912141744493191631888341/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (137/256:ℝ) ∧ thetaFirstModeFirst (137/256:ℝ) ≤ (-244503119079778686738177/50000000000000000000000000:ℝ) := by
  have hlo : (9161795527887/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(137/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(137/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(137/256:ℝ)) ≤ (2916290698439/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(137/256:ℝ)) (by norm_num : 2*(137/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(137/256:ℝ)) ≤ (9161798444181073327/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (137/256:ℝ) (9161795527887/1000000000000:ℝ) (9161798444181073327/1000000000000000000:ℝ) (27435898671/100000000000000:ℝ) (27435978683/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0822).1 (thetaFirstMode_refined_node_0822).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

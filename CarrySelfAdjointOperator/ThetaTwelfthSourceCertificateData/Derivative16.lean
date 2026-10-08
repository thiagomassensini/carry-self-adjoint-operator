import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0512 :
    (-1195933264364626741403407083/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (339/512:ℝ) ∧ thetaFirstModeFirst (339/512:ℝ) ≤ (-5979641895920786498487/12500000000000000000000000:ℝ) := by
  have hlo : (2952505307407/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(339/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(339/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(339/512:ℝ)) ≤ (3759247295521/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(339/512:ℝ)) (by norm_num : 2*(339/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(339/512:ℝ)) ≤ (11810024988877704953/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (339/512:ℝ) (2952505307407/250000000000:ℝ) (11810024988877704953/1000000000000000000:ℝ) (2069076441/100000000000000:ℝ) (103454211/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1015).1 (thetaFirstMode_refined_node_1015).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0513 :
    (-747216294124166881302501399/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (10394777066482805050791/15699122035309073589760:ℝ) ∧ thetaFirstModeFirst (10394777066482805050791/15699122035309073589760:ℝ) ≤ (-583760345281898407/1220703125000000000000:ℝ) := by
  have hlo : (36907450353/3125000000:ℝ) ≤ Real.pi*Real.exp (2*(10394777066482805050791/15699122035309073589760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(10394777066482805050791/15699122035309073589760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(10394777066482805050791/15699122035309073589760:ℝ)) ≤ (3759362804897/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(10394777066482805050791/15699122035309073589760:ℝ)) (by norm_num : 2*(10394777066482805050791/15699122035309073589760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(10394777066482805050791/15699122035309073589760:ℝ)) ≤ (11810387872324780921/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (10394777066482805050791/15699122035309073589760:ℝ) (36907450353/3125000000:ℝ) (11810387872324780921/1000000000000000000:ℝ) (16158919/781250000000:ℝ) (64635919/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1019).1 (thetaFirstMode_refined_node_1019).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0514 :
    (-22951955363285474286510489193/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (85/128:ℝ) ∧ thetaFirstModeFirst (85/128:ℝ) ≤ (-5737965317767801239357/12500000000000000000000000:ℝ) := by
  have hlo : (2964061086451/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(85/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(85/128:ℝ)) ≤ (3773960573431/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(85/128:ℝ)) (by norm_num : 2*(85/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(85/128:ℝ)) ≤ (11856248119766815583/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (85/128:ℝ) (2964061086451/250000000000:ℝ) (11856248119766815583/1000000000000000000:ℝ) (1977544207/100000000000000:ℝ) (1977551671/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1020).1 (thetaFirstMode_refined_node_1020).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0515 :
    (-5505081257035697985691735847/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (341/512:ℝ) ∧ thetaFirstModeFirst (341/512:ℝ) ≤ (-11010117211927961486661/25000000000000000000000000:ℝ) := by
  have hlo : (5951324187071/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(341/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(341/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(341/512:ℝ)) ≤ (3788731437483/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(341/512:ℝ)) (by norm_num : 2*(341/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(341/512:ℝ)) ≤ (11902652162876530419/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (341/512:ℝ) (5951324187071/500000000000:ℝ) (11902652162876530419/1000000000000000000:ℝ) (1889719291/100000000000000:ℝ) (472431613/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1021).1 (thetaFirstMode_refined_node_1021).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0516 :
    (-2751646894917022496316655149/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (10959904662371742259809/16455549877310448463360:ℝ) ∧ thetaFirstModeFirst (10959904662371742259809/16455549877310448463360:ℝ) ≤ (-22013084589736488328911/50000000000000000000000000:ℝ) := by
  have hlo : (11903011958719/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(10959904662371742259809/16455549877310448463360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(10959904662371742259809/16455549877310448463360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(10959904662371742259809/16455549877310448463360:ℝ)) ≤ (473605896259/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(10959904662371742259809/16455549877310448463360:ℝ)) (by norm_num : 2*(10959904662371742259809/16455549877310448463360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(10959904662371742259809/16455549877310448463360:ℝ)) ≤ (1487876968446000587/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (10959904662371742259809/16455549877310448463360:ℝ) (11903011958719/1000000000000:ℝ) (1487876968446000587/125000000000000000:ℝ) (1889046769/100000000000000:ℝ) (1889053927/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1025).1 (thetaFirstMode_refined_node_1025).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0517 :
    (-5280666568894931310560870199/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (171/256:ℝ) ∧ thetaFirstModeFirst (171/256:ℝ) ≤ (-21122579046306815335107/50000000000000000000000000:ℝ) := by
  have hlo : (11949234022711/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(171/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(171/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(171/256:ℝ)) ≤ (1901780056531/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(171/256:ℝ)) (by norm_num : 2*(171/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(171/256:ℝ)) ≤ (5974618913137393883/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (171/256:ℝ) (11949234022711/1000000000000:ℝ) (5974618913137393883/500000000000000000:ℝ) (1805466837/100000000000000:ℝ) (902736853/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1026).1 (thetaFirstMode_refined_node_1026).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0518 :
    (-79132421295045439788872409/195312500000000000000000000000:ℝ) ≤ thetaFirstModeFirst (343/512:ℝ) ∧ thetaFirstModeFirst (343/512:ℝ) ≤ (-5064453976706091210187/12500000000000000000000000:ℝ) := by
  have hlo : (5998001001177/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(343/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(343/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(343/512:ℝ)) ≤ (954611706609/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(343/512:ℝ)) (by norm_num : 2*(343/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(343/512:ℝ)) ≤ (2999001455200888137/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (343/512:ℝ) (5998001001177/500000000000:ℝ) (2999001455200888137/250000000000000000:ℝ) (862328131/50000000000000:ℝ) (26947857/1562500000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1027).1 (thetaFirstMode_refined_node_1027).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0519 :
    (-10125651529677904809646813429/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11552179400427359855007/17243678709113286300160:ℝ) ∧ thetaFirstModeFirst (11552179400427359855007/17243678709113286300160:ℝ) ≤ (-20251219137892918757553/50000000000000000000000000:ℝ) := by
  have hlo : (11996366302061/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11552179400427359855007/17243678709113286300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11552179400427359855007/17243678709113286300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11552179400427359855007/17243678709113286300160:ℝ)) ≤ (1909281393329/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11552179400427359855007/17243678709113286300160:ℝ)) (by norm_num : 2*(11552179400427359855007/17243678709113286300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11552179400427359855007/17243678709113286300160:ℝ)) ≤ (5998185060312633097/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11552179400427359855007/17243678709113286300160:ℝ) (11996366302061/1000000000000:ℝ) (5998185060312633097/500000000000000000:ℝ) (1724041173/100000000000000:ℝ) (1724047757/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1031).1 (thetaFirstMode_refined_node_1031).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0520 :
    (-607030460935915500212139521/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (43/64:ℝ) ∧ thetaFirstModeFirst (43/64:ℝ) ≤ (-485622348785393486779/1250000000000000000000000:ℝ) := by
  have hlo : (6021476513347/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(43/64:ℝ)) ≤ (3833391804759/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(43/64:ℝ)) (by norm_num : 2*(43/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(43/64:ℝ)) ≤ (12042956860088241087/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (43/64:ℝ) (6021476513347/500000000000:ℝ) (12042956860088241087/1000000000000000000:ℝ) (82358057/5000000000000:ℝ) (51473983/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1032).1 (thetaFirstMode_refined_node_1032).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0521 :
    (-4655716904178961087720663521/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (345/512:ℝ) ∧ thetaFirstModeFirst (345/512:ℝ) ≤ (-9311394941907337555997/25000000000000000000000000:ℝ) := by
  have hlo : (12090087812147/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(345/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(345/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(345/512:ℝ)) ≤ (3848395276073/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(345/512:ℝ)) (by norm_num : 2*(345/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(345/512:ℝ)) ≤ (12090091660544004289/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (345/512:ℝ) (12090087812147/1000000000000:ℝ) (12090091660544004289/1000000000000000000:ℝ) (786429551/50000000000000:ℝ) (393216289/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1033).1 (thetaFirstMode_refined_node_1033).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0522 :
    (-9308392710025231478938235433/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2434547114057885834205/3612928108949549783552:ℝ) ∧ thetaFirstModeFirst (2434547114057885834205/3612928108949549783552:ℝ) ≤ (-3723341542120062130213/10000000000000000000000000:ℝ) := by
  have hlo : (12090452840799/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(2434547114057885834205/3612928108949549783552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2434547114057885834205/3612928108949549783552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2434547114057885834205/3612928108949549783552:ℝ)) ≤ (1924255734163/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2434547114057885834205/3612928108949549783552:ℝ)) (by norm_num : 2*(2434547114057885834205/3612928108949549783552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2434547114057885834205/3612928108949549783552:ℝ)) ≤ (6045228344656341659/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2434547114057885834205/3612928108949549783552:ℝ) (12090452840799/1000000000000:ℝ) (6045228344656341659/500000000000000000:ℝ) (314459387/20000000000000:ℝ) (1572302987/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1037).1 (thetaFirstMode_refined_node_1037).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0523 :
    (-111566139282853864069123869/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (173/256:ℝ) ∧ thetaFirstModeFirst (173/256:ℝ) ≤ (-1785050751300489394233/5000000000000000000000000:ℝ) := by
  have hlo : (2427481415587/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(173/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(173/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(173/256:ℝ)) ≤ (1931728734657/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(173/256:ℝ)) (by norm_num : 2*(173/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(173/256:ℝ)) ≤ (6068705470697288601/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (173/256:ℝ) (2427481415587/200000000000:ℝ) (6068705470697288601/500000000000000000:ℝ) (750815859/50000000000000:ℝ) (18770469/1250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1038).1 (thetaFirstMode_refined_node_1038).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0524 :
    (-53459841390205898707102373/156250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (347/512:ℝ) ∧ thetaFirstModeFirst (347/512:ℝ) ≤ (-42767693318296663223/125000000000000000000000:ℝ) := by
  have hlo : (12184911546093/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(347/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(347/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(347/512:ℝ)) ≤ (484822326789/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(347/512:ℝ)) (by norm_num : 2*(347/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(347/512:ℝ)) ≤ (1523114428084034877/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (347/512:ℝ) (12184911546093/1000000000000:ℝ) (1523114428084034877/125000000000000000:ℝ) (3583411/250000000000:ℝ) (35834249/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1039).1 (thetaFirstMode_refined_node_1039).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0525 :
    (-17101545515717541399376803969/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (12822747845328599226543/18919600885932177948160:ℝ) ∧ thetaFirstModeFirst (12822747845328599226543/18919600885932177948160:ℝ) ≤ (-855073681091539196287/2500000000000000000000000:ℝ) := by
  have hlo : (3046319329359/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(12822747845328599226543/18919600885932177948160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(12822747845328599226543/18919600885932177948160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(12822747845328599226543/18919600885932177948160:ℝ)) ≤ (3878695042971/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(12822747845328599226543/18919600885932177948160:ℝ)) (by norm_num : 2*(12822747845328599226543/18919600885932177948160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(12822747845328599226543/18919600885932177948160:ℝ)) ≤ (12185281196132392803/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (12822747845328599226543/18919600885932177948160:ℝ) (3046319329359/250000000000:ℝ) (12185281196132392803/1000000000000000000:ℝ) (286570193/20000000000000:ℝ) (1432856523/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1043).1 (thetaFirstMode_refined_node_1043).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0526 :
    (-8195812544053763035534074477/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (87/128:ℝ) ∧ thetaFirstModeFirst (87/128:ℝ) ≤ (-4097888979581876691927/12500000000000000000000000:ℝ) := by
  have hlo : (6116300970741/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(87/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(87/128:ℝ)) ≤ (3893758941799/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(87/128:ℝ)) (by norm_num : 2*(87/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(87/128:ℝ)) ≤ (12232605835243145807/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (87/128:ℝ) (6116300970741/500000000000:ℝ) (12232605835243145807/1000000000000000000:ℝ) (683973147/50000000000000:ℝ) (683975811/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1044).1 (thetaFirstMode_refined_node_1044).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0527 :
    (-15703092021091157500862314737/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (349/512:ℝ) ∧ thetaFirstModeFirst (349/512:ℝ) ≤ (-1962878190904528220173/6250000000000000000000000:ℝ) := by
  have hlo : (12280478991801/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(349/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(349/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(349/512:ℝ)) ≤ (3908998683407/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(349/512:ℝ)) (by norm_num : 2*(349/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(349/512:ℝ)) ≤ (12280482900800647351/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (349/512:ℝ) (12280478991801/1000000000000:ℝ) (12280482900800647351/1000000000000000000:ℝ) (163158773/12500000000000:ℝ) (1305275287/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1045).1 (thetaFirstMode_refined_node_1045).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0528 :
    (-3924483208224762998804737941/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13503432473757098003241/19809759509951338370560:ℝ) ∧ thetaFirstModeFirst (13503432473757098003241/19809759509951338370560:ℝ) ≤ (-98111664693020165733/312500000000000000000000:ℝ) := by
  have hlo : (76755284497/6250000000:ℝ) ≤ Real.pi*Real.exp (2*(13503432473757098003241/19809759509951338370560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13503432473757098003241/19809759509951338370560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13503432473757098003241/19809759509951338370560:ℝ)) ≤ (977278838207/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13503432473757098003241/19809759509951338370560:ℝ)) (by norm_num : 2*(13503432473757098003241/19809759509951338370560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13503432473757098003241/19809759509951338370560:ℝ)) ≤ (3070212357159243751/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13503432473757098003241/19809759509951338370560:ℝ) (76755284497/6250000000:ℝ) (3070212357159243751/250000000000000000:ℝ) (1304801589/100000000000000:ℝ) (1304806691/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1049).1 (thetaFirstMode_refined_node_1049).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0529 :
    (-3760164344589066833865008699/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (175/256:ℝ) ∧ thetaFirstModeFirst (175/256:ℝ) ≤ (-1880074181468748165507/6250000000000000000000000:ℝ) := by
  have hlo : (3082135856899/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(175/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(175/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(175/256:ℝ)) ≤ (1962149035839/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(175/256:ℝ)) (by norm_num : 2*(175/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(175/256:ℝ)) ≤ (6164273675948551527/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (175/256:ℝ) (3082135856899/250000000000:ℝ) (6164273675948551527/500000000000000000:ℝ) (622616193/50000000000000:ℝ) (622618637/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1050).1 (thetaFirstMode_refined_node_1050).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0530 :
    (-14403453069863602347600682647/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (351/512:ℝ) ∧ thetaFirstModeFirst (351/512:ℝ) ≤ (-288067832501024132739/1000000000000000000000000:ℝ) := by
  have hlo : (495071839291/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(351/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(351/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(351/512:ℝ)) ≤ (3939657340061/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(351/512:ℝ)) (by norm_num : 2*(351/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(351/512:ℝ)) ≤ (12376799921934257173/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (351/512:ℝ) (495071839291/40000000000:ℝ) (12376799921934257173/1000000000000000000:ℝ) (593866329/50000000000000:ℝ) (1187737339/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1051).1 (thetaFirstMode_refined_node_1051).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0531 :
    (-7199353298200506036368577071/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (14216048497680767340759/20736351271356306434560:ℝ) ∧ thetaFirstModeFirst (14216048497680767340759/20736351271356306434560:ℝ) ≤ (-179983064847434929419/625000000000000000000000:ℝ) := by
  have hlo : (2475432655999/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(14216048497680767340759/20736351271356306434560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(14216048497680767340759/20736351271356306434560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(14216048497680767340759/20736351271356306434560:ℝ)) ≤ (3939774254581/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(14216048497680767340759/20736351271356306434560:ℝ)) (by norm_num : 2*(14216048497680767340759/20736351271356306434560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(14216048497680767340759/20736351271356306434560:ℝ)) ≤ (12377167219771887533/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (14216048497680767340759/20736351271356306434560:ℝ) (2475432655999/200000000000:ℝ) (12377167219771887533/1000000000000000000:ℝ) (74206581/6250000000000:ℝ) (593654987/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1055).1 (thetaFirstMode_refined_node_1055).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0532 :
    (-6895317552322349053858834523/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11/16:ℝ) ∧ thetaFirstModeFirst (11/16:ℝ) ≤ (-13790576067573176765413/50000000000000000000000000:ℝ) := by
  have hlo : (12425237392113/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11/16:ℝ)) ≤ (3955076722921/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11/16:ℝ)) (by norm_num : 2*(11/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11/16:ℝ)) ≤ (12425241347191553153/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11/16:ℝ) (12425237392113/1000000000000:ℝ) (12425241347191553153/1000000000000000000:ℝ) (1132674101/100000000000000:ℝ) (566339291/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1056).1 (thetaFirstMode_refined_node_1056).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0533 :
    (-13201383083411064544375479331/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (353/512:ℝ) ∧ thetaFirstModeFirst (353/512:ℝ) ≤ (-412541448973948607661/1562500000000000000000000:ℝ) := by
  have hlo : (3118467099067/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(353/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(353/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(353/512:ℝ)) ≤ (3970556455539/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(353/512:ℝ)) (by norm_num : 2*(353/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(353/512:ℝ)) ≤ (12473872366826133627/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (353/512:ℝ) (3118467099067/250000000000:ℝ) (12473872366826133627/1000000000000000000:ℝ) (134995383/12500000000000:ℝ) (1079967353/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1057).1 (thetaFirstMode_refined_node_1057).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0534 :
    (-26394039053179386408577491/100000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (14961899000581170932457/21700646917646714268160:ℝ) ∧ thetaFirstModeFirst (14961899000581170932457/21700646917646714268160:ℝ) ≤ (-6598481411204608383099/25000000000000000000000000:ℝ) := by
  have hlo : (6237118238777/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(14961899000581170932457/21700646917646714268160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(14961899000581170932457/21700646917646714268160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(14961899000581170932457/21700646917646714268160:ℝ)) ≤ (992668404869/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(14961899000581170932457/21700646917646714268160:ℝ)) (by norm_num : 2*(14961899000581170932457/21700646917646714268160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(14961899000581170932457/21700646917646714268160:ℝ)) ≤ (3118560112057616317/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (14961899000581170932457/21700646917646714268160:ℝ) (6237118238777/500000000000:ℝ) (3118560112057616317/250000000000000000:ℝ) (1079573587/100000000000000:ℝ) (8636623/800000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1061).1 (thetaFirstMode_refined_node_1061).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0535 :
    (-1579362468182145371804977217/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (177/256:ℝ) ∧ thetaFirstModeFirst (177/256:ℝ) ≤ (-12634845262324719107787/50000000000000000000000000:ℝ) := by
  have hlo : (12522689736793/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(177/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(177/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(177/256:ℝ)) ≤ (1993048387059/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(177/256:ℝ)) (by norm_num : 2*(177/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(177/256:ℝ)) ≤ (6261346861445844987/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (177/256:ℝ) (12522689736793/1000000000000:ℝ) (6261346861445844987/500000000000000000:ℝ) (1029509059/100000000000000:ℝ) (257378291/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1062).1 (thetaFirstMode_refined_node_1062).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0536 :
    (-755650650712070660392291233/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (355/512:ℝ) ∧ thetaFirstModeFirst (355/512:ℝ) ≤ (-6045179042581997119453/25000000000000000000000000:ℝ) := by
  have hlo : (12571702158641/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(355/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(355/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(355/512:ℝ)) ≤ (500212239473/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(355/512:ℝ)) (by norm_num : 2*(355/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(355/512:ℝ)) ≤ (1571463270042700489/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (355/512:ℝ) (12571702158641/1000000000000:ℝ) (1571463270042700489/125000000000000000:ℝ) (490612333/50000000000000:ℝ) (490614297/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1063).1 (thetaFirstMode_refined_node_1063).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0537 :
    (-6043200912031275833817705091/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3148466476744436255595/4540790783819398487552:ℝ) ∧ thetaFirstModeFirst (3148466476744436255595/4540790783819398487552:ℝ) ≤ (-755396845145902928247/3125000000000000000000000:ℝ) := by
  have hlo : (6286035518501/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(3148466476744436255595/4540790783819398487552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3148466476744436255595/4540790783819398487552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3148466476744436255595/4540790783819398487552:ℝ)) ≤ (4001815333437/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3148466476744436255595/4540790783819398487552:ℝ)) (by norm_num : 2*(3148466476744436255595/4540790783819398487552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3148466476744436255595/4540790783819398487552:ℝ)) ≤ (12572075038818345141/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3148466476744436255595/4540790783819398487552:ℝ) (6286035518501/500000000000:ℝ) (12572075038818345141/1000000000000000000:ℝ) (122608747/12500000000000:ℝ) (490436951/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1067).1 (thetaFirstMode_refined_node_1067).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0538 :
    (-90368457453903301604068887/390625000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (89/128:ℝ) ∧ thetaFirstModeFirst (89/128:ℝ) ≤ (-2891778080062940012029/12500000000000000000000000:ℝ) := by
  have hlo : (3155226602421/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(89/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(89/128:ℝ)) ≤ (62771251853/15625000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(89/128:ℝ)) (by norm_num : 2*(89/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(89/128:ℝ)) ≤ (197201725422621829/15625000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (89/128:ℝ) (3155226602421/250000000000:ℝ) (197201725422621829/15625000000000000:ℝ) (935025449/100000000000000:ℝ) (467514603/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1068).1 (thetaFirstMode_refined_node_1068).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0539 :
    (-69152658143679185915844499/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (357/512:ℝ) ∧ thetaFirstModeFirst (357/512:ℝ) ≤ (-5532188542016024121987/25000000000000000000000000:ℝ) := by
  have hlo : (6335151620361/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(357/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(357/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(357/512:ℝ)) ≤ (504135452691/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(357/512:ℝ)) (by norm_num : 2*(357/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(357/512:ℝ)) ≤ (1583788409225876763/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (357/512:ℝ) (6335151620361/500000000000:ℝ) (1583788409225876763/125000000000000000:ℝ) (890829867/100000000000000:ℝ) (44541673/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1069).1 (thetaFirstMode_refined_node_1069).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0540 :
    (-2765186390685839135396358809/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (16558743671981150478993/23747617312889180700160:ℝ) ∧ thetaFirstModeFirst (16558743671981150478993/23747617312889180700160:ℝ) ≤ (-691293583978508610393/3125000000000000000000000:ℝ) := by
  have hlo : (791917058101/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(16558743671981150478993/23747617312889180700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(16558743671981150478993/23747617312889180700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(16558743671981150478993/23747617312889180700160:ℝ)) ≤ (2016600648591/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(16558743671981150478993/23747617312889180700160:ℝ)) (by norm_num : 2*(16558743671981150478993/23747617312889180700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(16558743671981150478993/23747617312889180700160:ℝ)) ≤ (6335338481408945463/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (16558743671981150478993/23747617312889180700160:ℝ) (791917058101/62500000000:ℝ) (6335338481408945463/500000000000000000:ℝ) (890507093/100000000000000:ℝ) (445255343/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1073).1 (thetaFirstMode_refined_node_1073).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0541 :
    (-211629779594034971468791977/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (179/256:ℝ) ∧ thetaFirstModeFirst (179/256:ℝ) ≤ (-10581442684957767610377/50000000000000000000000000:ℝ) := by
  have hlo : (12719893405489/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(179/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(179/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(179/256:ℝ)) ≤ (809773732903/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(179/256:ℝ)) (by norm_num : 2*(179/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(179/256:ℝ)) ≤ (2543979490871934479/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (179/256:ℝ) (12719893405489/1000000000000:ℝ) (2543979490871934479/200000000000000000:ℝ) (848559193/100000000000000:ℝ) (84856263/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1074).1 (thetaFirstMode_refined_node_1074).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0542 :
    (-126470807546592566047997931/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (359/512:ℝ) ∧ thetaFirstModeFirst (359/512:ℝ) ≤ (-2529405044801052267629/12500000000000000000000000:ℝ) := by
  have hlo : (6384838830337/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(359/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(359/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(359/512:ℝ)) ≤ (4064715488413/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(359/512:ℝ)) (by norm_num : 2*(359/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(359/512:ℝ)) ≤ (12769681725389861909/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (359/512:ℝ) (6384838830337/500000000000:ℝ) (12769681725389861909/1000000000000000000:ℝ) (404068717/50000000000000:ℝ) (10101759/1250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1075).1 (thetaFirstMode_refined_node_1075).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0543 :
    (-316071539289992232798263901/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17412575849610501454191/24833020561715806159360:ℝ) ∧ thetaFirstModeFirst (17412575849610501454191/24833020561715806159360:ℝ) ≤ (-632140302822233472837/3125000000000000000000000:ℝ) := by
  have hlo : (3192512043377/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(17412575849610501454191/24833020561715806159360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17412575849610501454191/24833020561715806159360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17412575849610501454191/24833020561715806159360:ℝ)) ≤ (127026044573/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17412575849610501454191/24833020561715806159360:ℝ)) (by norm_num : 2*(17412575849610501454191/24833020561715806159360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17412575849610501454191/24833020561715806159360:ℝ)) ≤ (399064132448224789/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17412575849610501454191/24833020561715806159360:ℝ) (3192512043377/250000000000:ℝ) (399064132448224789/31250000000000000:ℝ) (201960981/25000000000000:ℝ) (807847209/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1079).1 (thetaFirstMode_refined_node_1079).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

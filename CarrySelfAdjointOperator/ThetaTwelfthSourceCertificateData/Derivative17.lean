import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0544 :
    (-9672283467914261141631424257/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (45/64:ℝ) ∧ thetaFirstModeFirst (45/64:ℝ) ≤ (-1209030105825398637663/6250000000000000000000000:ℝ) := by
  have hlo : (3204914191481/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(45/64:ℝ)) ≤ (4080624335027/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(45/64:ℝ)) (by norm_num : 2*(45/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(45/64:ℝ)) ≤ (12819660846550478011/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (45/64:ℝ) (3204914191481/250000000000:ℝ) (12819660846550478011/1000000000000000000:ℝ) (384745623/50000000000000:ℝ) (769494387/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1080).1 (thetaFirstMode_refined_node_1080).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0545 :
    (-4622348329907813598133186869/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (361/512:ℝ) ∧ thetaFirstModeFirst (361/512:ℝ) ≤ (-9244655774106136325599/50000000000000000000000000:ℝ) := by
  have hlo : (12869831483861/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(361/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(361/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(361/512:ℝ)) ≤ (2048297723553/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(361/512:ℝ)) (by norm_num : 2*(361/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(361/512:ℝ)) ≤ (6434917790230039929/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (361/512:ℝ) (12869831483861/1000000000000:ℝ) (6434917790230039929/500000000000000000:ℝ) (732549859/100000000000000:ℝ) (732552861/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1081).1 (thetaFirstMode_refined_node_1081).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0546 :
    (-115520035896194767097871389/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (18305321226441340498209/25961586427017257013760:ℝ) ∧ thetaFirstModeFirst (18305321226441340498209/25961586427017257013760:ℝ) ≤ (-46207810055594070121/250000000000000000000000:ℝ) := by
  have hlo : (2574040566799/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(18305321226441340498209/25961586427017257013760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(18305321226441340498209/25961586427017257013760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(18305321226441340498209/25961586427017257013760:ℝ)) ≤ (4096713651549/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(18305321226441340498209/25961586427017257013760:ℝ)) (by norm_num : 2*(18305321226441340498209/25961586427017257013760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(18305321226441340498209/25961586427017257013760:ℝ)) ≤ (12870206930710777557/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (18305321226441340498209/25961586427017257013760:ℝ) (2574040566799/200000000000:ℝ) (12870206930710777557/1000000000000000000:ℝ) (18307079/2500000000000:ℝ) (9153577/1250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1085).1 (thetaFirstMode_refined_node_1085).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0547 :
    (-176685492325839229280298339/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (181/256:ℝ) ∧ thetaFirstModeFirst (181/256:ℝ) ≤ (-441711769897812327/2500000000000000000000:ℝ) := by
  have hlo : (3230050645023/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(181/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(181/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(181/256:ℝ)) ≤ (82252581367/20000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(181/256:ℝ)) (by norm_num : 2*(181/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(181/256:ℝ)) ≤ (258404133854497631/20000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (181/256:ℝ) (3230050645023/250000000000:ℝ) (258404133854497631/20000000000000000:ℝ) (139449/20000000000:ℝ) (697247869/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1086).1 (thetaFirstMode_refined_node_1086).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0548 :
    (-8440406661605188844452209131/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (363/512:ℝ) ∧ thetaFirstModeFirst (363/512:ℝ) ≤ (-422018453361300320859/2500000000000000000000000:ℝ) := by
  have hlo : (648538541161/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(363/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(363/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(363/512:ℝ)) ≤ (4128725443413/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(363/512:ℝ)) (by norm_num : 2*(363/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(363/512:ℝ)) ≤ (12970774951948176909/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (363/512:ℝ) (648538541161/50000000000:ℝ) (12970774951948176909/1000000000000000000:ℝ) (663510819/100000000000000:ℝ) (663513559/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1087).1 (thetaFirstMode_refined_node_1087).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0549 :
    (-1687514623963206965911636817/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19238522835046489117407/27134777857019009052160:ℝ) ∧ thetaFirstModeFirst (19238522835046489117407/27134777857019009052160:ℝ) ≤ (-1054691942257439008761/6250000000000000000000000:ℝ) := by
  have hlo : (12971143023967/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19238522835046489117407/27134777857019009052160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19238522835046489117407/27134777857019009052160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19238522835046489117407/27134777857019009052160:ℝ)) ≤ (825768783723/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19238522835046489117407/27134777857019009052160:ℝ)) (by norm_num : 2*(19238522835046489117407/27134777857019009052160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19238522835046489117407/27134777857019009052160:ℝ)) ≤ (2594229430562690739/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19238522835046489117407/27134777857019009052160:ℝ) (12971143023967/1000000000000:ℝ) (2594229430562690739/200000000000000000:ℝ) (82908583/12500000000000:ℝ) (663271403/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1091).1 (thetaFirstMode_refined_node_1091).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0550 :
    (-806250060539356585250390193/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (91/128:ℝ) ∧ thetaFirstModeFirst (91/128:ℝ) ≤ (-1612492913133957530423/10000000000000000000000000:ℝ) := by
  have hlo : (2604307396971/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(91/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(91/128:ℝ)) ≤ (4144884817907/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(91/128:ℝ)) (by norm_num : 2*(91/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(91/128:ℝ)) ≤ (13021541129742905851/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (91/128:ℝ) (2604307396971/200000000000:ℝ) (13021541129742905851/1000000000000000000:ℝ) (631283813/100000000000000:ℝ) (63128643/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1092).1 (thetaFirstMode_refined_node_1092).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0551 :
    (-962497784272460424007719197/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (365/512:ℝ) ∧ thetaFirstModeFirst (365/512:ℝ) ≤ (-7699947731979790036411/50000000000000000000000000:ℝ) := by
  have hlo : (13072501839629/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(365/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(365/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(365/512:ℝ)) ≤ (1040276859601/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(365/512:ℝ)) (by norm_num : 2*(365/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(365/512:ℝ)) ≤ (3268126500184484393/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (365/512:ℝ) (13072501839629/1000000000000:ℝ) (3268126500184484393/250000000000000000:ℝ) (600502759/100000000000000:ℝ) (300252629/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1093).1 (thetaFirstMode_refined_node_1093).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0552 :
    (-1924347272336788455977872753/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4042755171877232548485/5670819777946998205952:ℝ) ∧ thetaFirstModeFirst (4042755171877232548485/5670819777946998205952:ℝ) ≤ (-7697354547058375405877/50000000000000000000000000:ℝ) := by
  have hlo : (13072874904261/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(4042755171877232548485/5670819777946998205952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4042755171877232548485/5670819777946998205952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4042755171877232548485/5670819777946998205952:ℝ)) ≤ (4161226188589/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4042755171877232548485/5670819777946998205952:ℝ)) (by norm_num : 2*(4042755171877232548485/5670819777946998205952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4042755171877232548485/5670819777946998205952:ℝ)) ≤ (13072879065487882277/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4042755171877232548485/5670819777946998205952:ℝ) (13072874904261/1000000000000:ℝ) (13072879065487882277/1000000000000000000:ℝ) (600283057/100000000000000:ℝ) (150071389/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1097).1 (thetaFirstMode_refined_node_1097).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0553 :
    (-1838073775873858357444829143/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (183/256:ℝ) ∧ thetaFirstModeFirst (183/256:ℝ) ≤ (-1470452397659581807281/10000000000000000000000000:ℝ) := by
  have hlo : (2624733233041/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(183/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(183/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(183/256:ℝ)) ≤ (4177393552443/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(183/256:ℝ)) (by norm_num : 2*(183/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(183/256:ℝ)) ≤ (13123670342600061699/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (183/256:ℝ) (2624733233041/200000000000:ℝ) (13123670342600061699/1000000000000000000:ℝ) (571108641/100000000000000:ℝ) (142777757/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1098).1 (thetaFirstMode_refined_node_1098).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0554 :
    (-701889967617866300226323427/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (367/512:ℝ) ∧ thetaFirstModeFirst (367/512:ℝ) ≤ (-1403773591111714391013/10000000000000000000000000:ℝ) := by
  have hlo : (13175030742289/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(367/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(367/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(367/512:ℝ)) ≤ (419374340853/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(367/512:ℝ)) (by norm_num : 2*(367/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(367/512:ℝ)) ≤ (1317503493603398829/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (367/512:ℝ) (13175030742289/1000000000000:ℝ) (1317503493603398829/100000000000000000:ℝ) (108608917/20000000000000:ℝ) (543046863/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1099).1 (thetaFirstMode_refined_node_1099).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0555 :
    (-1403305657409059003242985869/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21232729095465386243943/29621095571104304028160:ℝ) ∧ thetaFirstModeFirst (21232729095465386243943/29621095571104304028160:ℝ) ≤ (-43853103620438066633/312500000000000000000000:ℝ) := by
  have hlo : (2635080936807/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(21232729095465386243943/29621095571104304028160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21232729095465386243943/29621095571104304028160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21232729095465386243943/29621095571104304028160:ℝ)) ≤ (4193862437909/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21232729095465386243943/29621095571104304028160:ℝ)) (by norm_num : 2*(21232729095465386243943/29621095571104304028160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21232729095465386243943/29621095571104304028160:ℝ)) ≤ (13175408877897849037/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21232729095465386243943/29621095571104304028160:ℝ) (2635080936807/200000000000:ℝ) (13175408877897849037/1000000000000000000:ℝ) (16963919/3125000000000:ℝ) (108569537/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1103).1 (thetaFirstMode_refined_node_1103).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0556 :
    (-104676146675398691099312967/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23/32:ℝ) ∧ thetaFirstModeFirst (23/32:ℝ) ≤ (-669924300257734213297/5000000000000000000000000:ℝ) := by
  have hlo : (13226596354643/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23/32:ℝ)) ≤ (263134828509/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23/32:ℝ)) (by norm_num : 2*(23/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23/32:ℝ)) ≤ (826662535300074837/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23/32:ℝ) (13226596354643/1000000000000:ℝ) (826662535300074837/62500000000000000:ℝ) (51625579/10000000000000:ℝ) (129064491/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1104).1 (thetaFirstMode_refined_node_1104).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0557 :
    (-1598227484817833207699808807/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (369/512:ℝ) ∧ thetaFirstModeFirst (369/512:ℝ) ≤ (-3196440415720571437187/25000000000000000000000000:ℝ) := by
  have hlo : (6639181894549/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(369/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(369/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(369/512:ℝ)) ≤ (2113317672871/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(369/512:ℝ)) (by norm_num : 2*(369/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(369/512:ℝ)) ≤ (6639184007867823503/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (369/512:ℝ) (6639181894549/500000000000:ℝ) (6639184007867823503/500000000000000000:ℝ) (490689463/100000000000000:ℝ) (245345769/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1105).1 (thetaFirstMode_refined_node_1105).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0558 :
    (-1278148615429148365234817053/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (22297086444538131163641/30937356888429438876160:ℝ) ∧ thetaFirstModeFirst (22297086444538131163641/30937356888429438876160:ℝ) ≤ (-6390713982270530356983/50000000000000000000000000:ℝ) := by
  have hlo : (13278738621151/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(22297086444538131163641/30937356888429438876160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(22297086444538131163641/30937356888429438876160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(22297086444538131163641/30937356888429438876160:ℝ)) ≤ (845350931703/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(22297086444538131163641/30937356888429438876160:ℝ)) (by norm_num : 2*(22297086444538131163641/30937356888429438876160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(22297086444538131163641/30937356888429438876160:ℝ)) ≤ (2655748569581622879/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (22297086444538131163641/30937356888429438876160:ℝ) (13278738621151/1000000000000:ℝ) (2655748569581622879/200000000000000000:ℝ) (490509033/100000000000000:ℝ) (490511107/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1109).1 (thetaFirstMode_refined_node_1109).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0559 :
    (-6099319017296422764511609467/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (185/256:ℝ) ∧ thetaFirstModeFirst (185/256:ℝ) ≤ (-3049645576367198110503/25000000000000000000000000:ℝ) := by
  have hlo : (13330333835563/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(185/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(185/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(185/256:ℝ)) ≤ (4243177928759/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(185/256:ℝ)) (by norm_num : 2*(185/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(185/256:ℝ)) ≤ (13330338078743773087/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (185/256:ℝ) (13330333835563/1000000000000:ℝ) (13330338078743773087/1000000000000000000:ℝ) (233147381/50000000000000:ℝ) (466296741/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1110).1 (thetaFirstMode_refined_node_1110).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0560 :
    (-290901291630916072061393267/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (371/512:ℝ) ∧ thetaFirstModeFirst (371/512:ℝ) ≤ (-1454499787813466918559/12500000000000000000000000:ℝ) := by
  have hlo : (13382507287039/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(371/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(371/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(371/512:ℝ)) ≤ (851957051523/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(371/512:ℝ)) (by norm_num : 2*(371/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(371/512:ℝ)) ≤ (2676502309365296139/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (371/512:ℝ) (13382507287039/1000000000000:ℝ) (2676502309365296139/200000000000000000:ℝ) (110755681/25000000000000:ℝ) (110756153/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1111).1 (thetaFirstMode_refined_node_1111).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0561 :
    (-1454011857400306647204846291/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23408608439399087217159/32304515719285064680960:ℝ) ∧ thetaFirstModeFirst (23408608439399087217159/32304515719285064680960:ℝ) ≤ (-1454005187042385034603/12500000000000000000000000:ℝ) := by
  have hlo : (13382883022553/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23408608439399087217159/32304515719285064680960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23408608439399087217159/32304515719285064680960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23408608439399087217159/32304515719285064680960:ℝ)) ≤ (4259904857969/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23408608439399087217159/32304515719285064680960:ℝ)) (by norm_num : 2*(23408608439399087217159/32304515719285064680960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23408608439399087217159/32304515719285064680960:ℝ)) ≤ (13382887282461404617/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23408608439399087217159/32304515719285064680960:ℝ) (13382883022553/1000000000000:ℝ) (13382887282461404617/1000000000000000000:ℝ) (110714851/25000000000000:ℝ) (110715323/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1115).1 (thetaFirstMode_refined_node_1115).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0562 :
    (-173392836562073364920061637/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (93/128:ℝ) ∧ thetaFirstModeFirst (93/128:ℝ) ≤ (-110970904487099928009/1000000000000000000000000:ℝ) := by
  have hlo : (1343488493963/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(93/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(93/128:ℝ)) ≤ (2138228792859/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(93/128:ℝ)) (by norm_num : 2*(93/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(93/128:ℝ)) ≤ (6717444608044284387/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (93/128:ℝ) (1343488493963/100000000000:ℝ) (6717444608044284387/500000000000000000:ℝ) (84165243/20000000000000:ℝ) (26301751/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1116).1 (thetaFirstMode_refined_node_1116).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0563 :
    (-5290508968778613887115759211/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (373/512:ℝ) ∧ thetaFirstModeFirst (373/512:ℝ) ≤ (-2645242262110336608681/25000000000000000000000000:ℝ) := by
  have hlo : (13487467592557/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(373/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(373/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(373/512:ℝ)) ≤ (4293195167469/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(373/512:ℝ)) (by norm_num : 2*(373/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(373/512:ℝ)) ≤ (13487471885754438117/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (373/512:ℝ) (13487467592557/1000000000000:ℝ) (13487471885754438117/1000000000000000000:ℝ) (199829933/50000000000000:ℝ) (399661583/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1117).1 (thetaFirstMode_refined_node_1117).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0564 :
    (-264435203008256743296270249/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (24569113804309940929857/33724249796067390492160:ℝ) ∧ thetaFirstModeFirst (24569113804309940929857/33724249796067390492160:ℝ) ≤ (-2644339814392344895377/25000000000000000000000000:ℝ) := by
  have hlo : (6743922122327/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(24569113804309940929857/33724249796067390492160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(24569113804309940929857/33724249796067390492160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(24569113804309940929857/33724249796067390492160:ℝ)) ≤ (214665752979/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(24569113804309940929857/33724249796067390492160:ℝ)) (by norm_num : 2*(24569113804309940929857/33724249796067390492160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(24569113804309940929857/33724249796067390492160:ℝ)) ≤ (674392426898555547/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (24569113804309940929857/33724249796067390492160:ℝ) (6743922122327/500000000000:ℝ) (674392426898555547/50000000000000000:ℝ) (399512151/100000000000000:ℝ) (399513867/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1121).1 (thetaFirstMode_refined_node_1121).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0565 :
    (-1260852495702064930398199841/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (187/256:ℝ) ∧ thetaFirstModeFirst (187/256:ℝ) ≤ (-5043386591093524938873/50000000000000000000000000:ℝ) := by
  have hlo : (13540256048169/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(187/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(187/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(187/256:ℝ)) ≤ (2154999129131/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(187/256:ℝ)) (by norm_num : 2*(187/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(187/256:ℝ)) ≤ (6770130179084045683/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (187/256:ℝ) (13540256048169/1000000000000:ℝ) (6770130179084045683/500000000000000000:ℝ) (379480017/100000000000000:ℝ) (189740827/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1122).1 (thetaFirstMode_refined_node_1122).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0566 :
    (-2403428687180375658017073033/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (375/512:ℝ) ∧ thetaFirstModeFirst (375/512:ℝ) ≤ (-300427188343343444591/3125000000000000000000000:ℝ) := by
  have hlo : (6796625555977/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(375/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(375/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(375/512:ℝ)) ≤ (2163433557247/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(375/512:ℝ)) (by norm_num : 2*(375/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(375/512:ℝ)) ≤ (6796627719412274471/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (375/512:ℝ) (6796625555977/500000000000:ℝ) (6796627719412274471/500000000000000000:ℝ) (45030583/12500000000000:ℝ) (360246223/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1123).1 (thetaFirstMode_refined_node_1123).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0567 :
    (-4805212075176561956723846719/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5156096209822605445875/7039656537271006218752:ℝ) ∧ thetaFirstModeFirst (5156096209822605445875/7039656537271006218752:ℝ) ≤ (-18770272321309624647/195312500000000000000000:ℝ) := by
  have hlo : (3398407173431/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(5156096209822605445875/7039656537271006218752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5156096209822605445875/7039656537271006218752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5156096209822605445875/7039656537271006218752:ℝ)) ≤ (4326987302529/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5156096209822605445875/7039656537271006218752:ℝ)) (by norm_num : 2*(5156096209822605445875/7039656537271006218752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5156096209822605445875/7039656537271006218752:ℝ)) ≤ (13593633020713988697/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5156096209822605445875/7039656537271006218752:ℝ) (3398407173431/250000000000:ℝ) (13593633020713988697/1000000000000000000:ℝ) (5626737/1562500000000:ℝ) (360112727/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1127).1 (thetaFirstMode_refined_node_1127).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0568 :
    (-1145112097028617429455255919/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (47/64:ℝ) ∧ thetaFirstModeFirst (47/64:ℝ) ≤ (-916085396475248228889/10000000000000000000000000:ℝ) := by
  have hlo : (2729290718511/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(47/64:ℝ)) ≤ (2171900996781/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(47/64:ℝ)) (by norm_num : 2*(47/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(47/64:ℝ)) ≤ (6823228968180212133/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (47/64:ℝ) (2729290718511/200000000000:ℝ) (6823228968180212133/500000000000000000:ℝ) (341913399/100000000000000:ℝ) (170957443/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1128).1 (thetaFirstMode_refined_node_1128).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0569 :
    (-136368547051086348347809971/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (377/512:ℝ) ∧ thetaFirstModeFirst (377/512:ℝ) ≤ (-2181886522884488384691/25000000000000000000000000:ℝ) := by
  have hlo : (13699864301777/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(377/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(377/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(377/512:ℝ)) ≤ (272550197117/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(377/512:ℝ)) (by norm_num : 2*(377/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(377/512:ℝ)) ≤ (856241791411387381/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (377/512:ℝ) (13699864301777/1000000000000:ℝ) (856241791411387381/62500000000000000:ℝ) (162223683/50000000000000:ℝ) (162224391/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1129).1 (thetaFirstMode_refined_node_1129).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0570 :
    (-545286864636167868801445357/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (27044650098091245441393/36728384789253236892160:ℝ) ∧ thetaFirstModeFirst (27044650098091245441393/36728384789253236892160:ℝ) ≤ (-2181137228587197425111/25000000000000000000000000:ℝ) := by
  have hlo : (13700242826279/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(27044650098091245441393/36728384789253236892160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27044650098091245441393/36728384789253236892160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(27044650098091245441393/36728384789253236892160:ℝ)) ≤ (1090230910497/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(27044650098091245441393/36728384789253236892160:ℝ)) (by norm_num : 2*(27044650098091245441393/36728384789253236892160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(27044650098091245441393/36728384789253236892160:ℝ)) ≤ (3425061796801001721/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (27044650098091245441393/36728384789253236892160:ℝ) (13700242826279/1000000000000:ℝ) (3425061796801001721/250000000000000000:ℝ) (162163409/50000000000000:ℝ) (162164117/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1133).1 (thetaFirstMode_refined_node_1133).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0571 :
    (-83130324026398652861857689/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (189/256:ℝ) ∧ thetaFirstModeFirst (189/256:ℝ) ≤ (-415649665106768947521/5000000000000000000000000:ℝ) := by
  have hlo : (2750696810921/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(189/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(189/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(189/256:ℝ)) ≤ (4377870854843/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(189/256:ℝ)) (by norm_num : 2*(189/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(189/256:ℝ)) ≤ (13753488432478784899/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (189/256:ℝ) (2750696810921/200000000000:ℝ) (13753488432478784899/1000000000000000000:ℝ) (153904601/50000000000000:ℝ) (6156211/2000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1134).1 (thetaFirstMode_refined_node_1134).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0572 :
    (-989563131501651995272479173/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (379/512:ℝ) ∧ thetaFirstModeFirst (379/512:ℝ) ≤ (-395823383523071450089/5000000000000000000000000:ℝ) := by
  have hlo : (13807313669211/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(379/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(379/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(379/512:ℝ)) ≤ (2197502678453/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(379/512:ℝ)) (by norm_num : 2*(379/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(379/512:ℝ)) ≤ (6903659032109195629/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (379/512:ℝ) (13807313669211/1000000000000:ℝ) (6903659032109195629/500000000000000000:ℝ) (29196299/10000000000000:ℝ) (145982137/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1135).1 (thetaFirstMode_refined_node_1135).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0573 :
    (-791377732703526067616334143/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (28363623954139189416591/38316374347894276840960:ℝ) ∧ thetaFirstModeFirst (28363623954139189416591/38316374347894276840960:ℝ) ≤ (-1978434993127669770947/25000000000000000000000000:ℝ) := by
  have hlo : (13807693149477/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(28363623954139189416591/38316374347894276840960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(28363623954139189416591/38316374347894276840960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(28363623954139189416591/38316374347894276840960:ℝ)) ≤ (4395126149251/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(28363623954139189416591/38316374347894276840960:ℝ)) (by norm_num : 2*(28363623954139189416591/38316374347894276840960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(28363623954139189416591/38316374347894276840960:ℝ)) ≤ (13807697544603896843/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (28363623954139189416591/38316374347894276840960:ℝ) (13807693149477/1000000000000:ℝ) (13807697544603896843/1000000000000000000:ℝ) (145927111/50000000000000:ℝ) (58371101/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1139).1 (thetaFirstMode_refined_node_1139).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0574 :
    (-942162689641245045442288017/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (95/128:ℝ) ∧ thetaFirstModeFirst (95/128:ℝ) ≤ (-235539556491152907879/3125000000000000000000000:ℝ) := by
  have hlo : (3465338491743/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(95/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(95/128:ℝ)) ≤ (2206103460757/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(95/128:ℝ)) (by norm_num : 2*(95/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(95/128:ℝ)) ≤ (6930679189589965901/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (95/128:ℝ) (3465338491743/250000000000:ℝ) (6930679189589965901/500000000000000000:ℝ) (69218553/25000000000000:ℝ) (138437717/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1140).1 (thetaFirstMode_refined_node_1140).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0575 :
    (-224210696325170555411066271/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (381/512:ℝ) ∧ thetaFirstModeFirst (381/512:ℝ) ≤ (-35873540716517305463/500000000000000000000000:ℝ) := by
  have hlo : (13915605772479/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(381/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(381/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(381/512:ℝ)) ≤ (4429475811143/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(381/512:ℝ)) (by norm_num : 2*(381/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(381/512:ℝ)) ≤ (13915610201956170799/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (381/512:ℝ) (13915605772479/1000000000000:ℝ) (13915610201956170799/1000000000000000000:ℝ) (2625097/1000000000000:ℝ) (16406929/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1141).1 (thetaFirstMode_refined_node_1141).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

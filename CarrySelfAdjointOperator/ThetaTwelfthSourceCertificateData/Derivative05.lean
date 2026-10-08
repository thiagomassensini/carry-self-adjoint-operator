import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0160 :
    (-4424502090121606102395453505377/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13/64:ℝ) ∧ thetaFirstModeFirst (13/64:ℝ) ≤ (-353959516875666219209879/2000000000000000000000000:ℝ) := by
  have hlo : (4716088167057/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13/64:ℝ)) ≤ (1501177800001/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13/64:ℝ)) (by norm_num : 2*(13/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13/64:ℝ)) ≤ (4716089668238541593/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13/64:ℝ) (4716088167057/1000000000000:ℝ) (4716089668238541593/1000000000000000000:ℝ) (79254932647/4000000000000:ℝ) (990688145289/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0312).1 (thetaFirstMode_refined_node_0312).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0161 :
    (-8731591951072328680779836995557/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (105/512:ℝ) ∧ thetaFirstModeFirst (105/512:ℝ) ≤ (-873157585778458523043039/5000000000000000000000000:ℝ) := by
  have hlo : (4734546414253/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(105/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(105/512:ℝ)) ≤ (1507053243787/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(105/512:ℝ)) (by norm_num : 2*(105/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(105/512:ℝ)) ≤ (4734547921308532691/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (105/512:ℝ) (4734546414253/1000000000000:ℝ) (4734547921308532691/1000000000000000000:ℝ) (194703656763/10000000000000:ℝ) (1947039501927/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0313).1 (thetaFirstMode_refined_node_0313).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0162 :
    (-4364311752639487618421290283097/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (54598255949620845/266167146581207552:ℝ) ∧ thetaFirstModeFirst (54598255949620845/266167146581207552:ℝ) ≤ (-8728607416177782707466217/50000000000000000000000000:ℝ) := by
  have hlo : (4735015916043/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(54598255949620845/266167146581207552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(54598255949620845/266167146581207552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(54598255949620845/266167146581207552:ℝ)) ≤ (1507202690879/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(54598255949620845/266167146581207552:ℝ)) (by norm_num : 2*(54598255949620845/266167146581207552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(54598255949620845/266167146581207552:ℝ)) ≤ (4735017423246630247/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (54598255949620845/266167146581207552:ℝ) (4735015916043/1000000000000:ℝ) (4735017423246630247/1000000000000000000:ℝ) (1946170889819/100000000000000:ℝ) (973086911551/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0317).1 (thetaFirstMode_refined_node_0317).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0163 :
    (-861510744997221884050428265839/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (53/256:ℝ) ∧ thetaFirstModeFirst (53/256:ℝ) ≤ (-53844322007449612020723/312500000000000000000000:ℝ) := by
  have hlo : (2376538452493/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(53/256:ℝ)) ≤ (151295168341/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(53/256:ℝ)) (by norm_num : 2*(53/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(53/256:ℝ)) ≤ (475307841793907213/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (53/256:ℝ) (2376538452493/500000000000:ℝ) (475307841793907213/100000000000000000:ℝ) (23914458111/1250000000000:ℝ) (1913159543403/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0318).1 (thetaFirstMode_refined_node_0318).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0164 :
    (-531222053484253879003990172197/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (107/512:ℝ) ∧ thetaFirstModeFirst (107/512:ℝ) ≤ (-8499537090908457057799183/50000000000000000000000000:ℝ) := by
  have hlo : (4771679922009/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(107/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(107/512:ℝ)) ≤ (1518873208873/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(107/512:ℝ)) (by norm_num : 2*(107/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(107/512:ℝ)) ≤ (4771681440882954689/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (107/512:ℝ) (4771679922009/1000000000000:ℝ) (4771681440882954689/1000000000000000000:ℝ) (1879729931687/100000000000000:ℝ) (117483299173/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0319).1 (thetaFirstMode_refined_node_0319).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0165 :
    (-8496686169668207224991266035167/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (323505440094667743/1547628340508700160:ℝ) ∧ thetaFirstModeFirst (323505440094667743/1547628340508700160:ℝ) ≤ (-4248335204453059795768539/25000000000000000000000000:ℝ) := by
  have hlo : (2386072134577/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(323505440094667743/1547628340508700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(323505440094667743/1547628340508700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(323505440094667743/1547628340508700160:ℝ)) ≤ (1519021015191/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(323505440094667743/1547628340508700160:ℝ)) (by norm_num : 2*(323505440094667743/1547628340508700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(323505440094667743/1547628340508700160:ℝ)) ≤ (4772145788176939263/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (323505440094667743/1547628340508700160:ℝ) (2386072134577/500000000000:ℝ) (4772145788176939263/1000000000000000000:ℝ) (1878902994507/100000000000000:ℝ) (1878905848609/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0323).1 (thetaFirstMode_refined_node_0323).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0166 :
    (-2096232550390949966932539197319/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (27/128:ℝ) ∧ thetaFirstModeFirst (27/128:ℝ) ≤ (-8384914600086585414273161/50000000000000000000000000:ℝ) := by
  have hlo : (4790355749181/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(27/128:ℝ)) ≤ (381204477633/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(27/128:ℝ)) (by norm_num : 2*(27/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(27/128:ℝ)) ≤ (1197589318500489369/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (27/128:ℝ) (4790355749181/1000000000000:ℝ) (1197589318500489369/250000000000000000:ℝ) (1846752779581/100000000000000:ℝ) (1846755595551/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0324).1 (thetaFirstMode_refined_node_0324).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0167 :
    (-1654248275061864446932194942879/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (109/512:ℝ) ∧ thetaFirstModeFirst (109/512:ℝ) ≤ (-330849037463883572510537/2000000000000000000000000:ℝ) := by
  have hlo : (192364186859/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(109/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(109/512:ℝ)) ≤ (306157175819/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(109/512:ℝ)) (by norm_num : 2*(109/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(109/512:ℝ)) ≤ (961821240452739667/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (109/512:ℝ) (192364186859/40000000000:ℝ) (961821240452739667/200000000000000000:ℝ) (1814221548443/100000000000000:ℝ) (1814224325637/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0325).1 (thetaFirstMode_refined_node_0325).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0168 :
    (-413423645529846024625133656701/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (382163785687980441/1794715319477839360:ℝ) ∧ thetaFirstModeFirst (382163785687980441/1794715319477839360:ℝ) ≤ (-516778592241247388149251/3125000000000000000000000:ℝ) := by
  have hlo : (4809564080659/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(382163785687980441/1794715319477839360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(382163785687980441/1794715319477839360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(382163785687980441/1794715319477839360:ℝ)) ≤ (153093211361/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(382163785687980441/1794715319477839360:ℝ)) (by norm_num : 2*(382163785687980441/1794715319477839360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(382163785687980441/1794715319477839360:ℝ)) ≤ (480956561159238073/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (382163785687980441/1794715319477839360:ℝ) (4809564080659/1000000000000:ℝ) (480956561159238073/100000000000000000:ℝ) (113339473489/6250000000000:ℝ) (906717176037/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0329).1 (thetaFirstMode_refined_node_0329).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0169 :
    (-4079244059912692827950150222181/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (55/256:ℝ) ∧ thetaFirstModeFirst (55/256:ℝ) ≤ (-796725863602122925919/4882812500000000000000:ℝ) := by
  have hlo : (9429544873/1953125000:ℝ) ≤ Real.pi*Real.exp (2*(55/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(55/256:ℝ)) ≤ (768388602813/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(55/256:ℝ)) (by norm_num : 2*(55/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(55/256:ℝ)) ≤ (2413964255877101109/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (55/256:ℝ) (9429544873/1953125000:ℝ) (2413964255877101109/500000000000000000:ℝ) (89106629353/5000000000000:ℝ) (1782135325809/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0330).1 (thetaFirstMode_refined_node_0330).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0170 :
    (-8046672033288088130459758812349/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (111/512:ℝ) ∧ thetaFirstModeFirst (111/512:ℝ) ≤ (-8046656918293625337524409/50000000000000000000000000:ℝ) := by
  have hlo : (4846822946889/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(111/512:ℝ)) ≤ (1542791981547/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(111/512:ℝ)) (by norm_num : 2*(111/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(111/512:ℝ)) ≤ (4846824489684184371/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (111/512:ℝ) (4846822946889/1000000000000:ℝ) (4846824489684184371/1000000000000000000:ℝ) (1750482237681/100000000000000:ℝ) (1750484938319/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0331).1 (thetaFirstMode_refined_node_0331).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0171 :
    (-2010999603662724551427961111221/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (450092942792761959/2075655332250933760:ℝ) ∧ thetaFirstModeFirst (450092942792761959/2075655332250933760:ℝ) ≤ (-804398330353034925731331/5000000000000000000000000:ℝ) := by
  have hlo : (2423638811659/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(450092942792761959/2075655332250933760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(450092942792761959/2075655332250933760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(450092942792761959/2075655332250933760:ℝ)) ≤ (1542936709579/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(450092942792761959/2075655332250933760:ℝ)) (by norm_num : 2*(450092942792761959/2075655332250933760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(450092942792761959/2075655332250933760:ℝ)) ≤ (4847279166256419347/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (450092942792761959/2075655332250933760:ℝ) (2423638811659/500000000000:ℝ) (4847279166256419347/1000000000000000000:ℝ) (349945509609/20000000000000:ℝ) (437432561943/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0335).1 (thetaFirstMode_refined_node_0335).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0172 :
    (-1587158913934684595296801966503/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/32:ℝ) ∧ thetaFirstModeFirst (7/32:ℝ) ≤ (-991972451949522304036269/6250000000000000000000000:ℝ) := by
  have hlo : (2432896437773/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/32:ℝ)) ≤ (309766059727/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/32:ℝ)) (by norm_num : 2*(7/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/32:ℝ)) ≤ (973158884875925111/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/32:ℝ) (2432896437773/500000000000:ℝ) (973158884875925111/200000000000000000:ℝ) (429816709153/25000000000000:ℝ) (1719269499473/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0336).1 (thetaFirstMode_refined_node_0336).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0173 :
    (-3912928519558651627419150130957/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (113/512:ℝ) ∧ thetaFirstModeFirst (113/512:ℝ) ≤ (-1956460561330618090902957/12500000000000000000000000:ℝ) := by
  have hlo : (1221209262601/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(113/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(113/512:ℝ)) ≤ (1554892249027/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(113/512:ℝ)) (by norm_num : 2*(113/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(113/512:ℝ)) ≤ (4884838605297480011/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (113/512:ℝ) (1221209262601/250000000000:ℝ) (4884838605297480011/1000000000000000000:ℝ) (1688482714757/100000000000000:ℝ) (844242670087/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0337).1 (thetaFirstMode_refined_node_0337).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0174 :
    (-7823275043007384070353665834951/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (528550581246993657/2394348818532252160:ℝ) ∧ thetaFirstModeFirst (528550581246993657/2394348818532252160:ℝ) ≤ (-7823260252983323143290211/50000000000000000000000000:ℝ) := by
  have hlo : (4885287188619/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(528550581246993657/2394348818532252160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(528550581246993657/2394348818532252160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(528550581246993657/2394348818532252160:ℝ)) ≤ (1555035532501/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(528550581246993657/2394348818532252160:ℝ)) (by norm_num : 2*(528550581246993657/2394348818532252160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(528550581246993657/2394348818532252160:ℝ)) ≤ (4885288743656414093/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (528550581246993657/2394348818532252160:ℝ) (4885287188619/1000000000000:ℝ) (4885288743656414093/1000000000000000000:ℝ) (1687761714569/100000000000000:ℝ) (1687764339107/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0341).1 (thetaFirstMode_refined_node_0341).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0175 :
    (-7716860608341322408476982267047/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (57/256:ℝ) ∧ thetaFirstModeFirst (57/256:ℝ) ≤ (-771684597416900647339113/5000000000000000000000000:ℝ) := by
  have hlo : (980791152411/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(57/256:ℝ)) ≤ (1560977925223/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(57/256:ℝ)) (by norm_num : 2*(57/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(57/256:ℝ)) ≤ (4903957323035100239/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (57/256:ℝ) (980791152411/200000000000:ℝ) (4903957323035100239/1000000000000000000:ℝ) (829063099083/50000000000000:ℝ) (1658128786473/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0342).1 (thetaFirstMode_refined_node_0342).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0176 :
    (-3804403150638035211679070565393/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (115/512:ℝ) ∧ thetaFirstModeFirst (115/512:ℝ) ≤ (-1902197956516511742082467/12500000000000000000000000:ℝ) := by
  have hlo : (1230787325557/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(115/512:ℝ)) ≤ (783543710041/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(115/512:ℝ)) (by norm_num : 2*(115/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(115/512:ℝ)) ≤ (2461575434658835313/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (115/512:ℝ) (1230787325557/250000000000:ℝ) (2461575434658835313/500000000000000000:ℝ) (1628193608631/100000000000000:ℝ) (1628196160161/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0343).1 (thetaFirstMode_refined_node_0343).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0177 :
    (-7606312845547518452462719694997/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (123787575796526235/551012753541565952:ℝ) ∧ thetaFirstModeFirst (123787575796526235/551012753541565952:ℝ) ≤ (-1857006438969079684601/12207031250000000000000:ℝ) := by
  have hlo : (4808198327/976562500:ℝ) ≤ Real.pi*Real.exp (2*(123787575796526235/551012753541565952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123787575796526235/551012753541565952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(123787575796526235/551012753541565952:ℝ)) ≤ (1567229317763/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(123787575796526235/551012753541565952:ℝ)) (by norm_num : 2*(123787575796526235/551012753541565952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(123787575796526235/551012753541565952:ℝ)) ≤ (4923596654079016459/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (123787575796526235/551012753541565952:ℝ) (4808198327/976562500:ℝ) (4923596654079016459/1000000000000000000:ℝ) (813752393251/50000000000000:ℝ) (1627507337183/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0347).1 (thetaFirstMode_refined_node_0347).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0178 :
    (-1875423749873723130045309540049/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29/128:ℝ) ∧ thetaFirstModeFirst (29/128:ℝ) ≤ (-1875420170641923020669029/12500000000000000000000000:ℝ) := by
  have hlo : (4942417963793/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29/128:ℝ)) ≤ (393305206707/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29/128:ℝ)) (by norm_num : 2*(29/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29/128:ℝ)) ≤ (1235604884254264251/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29/128:ℝ) (4942417963793/1000000000000:ℝ) (1235604884254264251/250000000000000000:ℝ) (399670316053/25000000000000:ℝ) (1598683779299/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0348).1 (thetaFirstMode_refined_node_0348).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0179 :
    (-1479105488565313057011857135149/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (117/512:ℝ) ∧ thetaFirstModeFirst (117/512:ℝ) ≤ (-902772617614741520607/6103515625000000000000:ℝ) := by
  have hlo : (77527531887/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(117/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(117/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(117/512:ℝ)) ≤ (1579378239049/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(117/512:ℝ)) (by norm_num : 2*(117/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(117/512:ℝ)) ≤ (4961763620148665057/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (117/512:ℝ) (77527531887/15625000000:ℝ) (4961763620148665057/1000000000000000000:ℝ) (12262386561/781250000000:ℝ) (313917591757/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0349).1 (thetaFirstMode_refined_node_0349).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0180 :
    (-1848279894301567142742243227311/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (722812917611120193/3162462922265628160:ℝ) ∧ thetaFirstModeFirst (722812917611120193/3162462922265628160:ℝ) ≤ (-11551727221037289852609/78125000000000000000000:ℝ) := by
  have hlo : (77534431987/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(722812917611120193/3162462922265628160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(722812917611120193/3162462922265628160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(722812917611120193/3162462922265628160:ℝ)) ≤ (1579518806761/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(722812917611120193/3162462922265628160:ℝ)) (by norm_num : 2*(722812917611120193/3162462922265628160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(722812917611120193/3162462922265628160:ℝ)) ≤ (4962205226688710273/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (722812917611120193/3162462922265628160:ℝ) (77534431987/15625000000:ℝ) (4962205226688710273/1000000000000000000:ℝ) (156892740107/10000000000000:ℝ) (392232469807/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0353).1 (thetaFirstMode_refined_node_0353).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0181 :
    (-72903042299312624648030487249/500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (59/256:ℝ) ∧ thetaFirstModeFirst (59/256:ℝ) ≤ (-1822572556875331102117991/12500000000000000000000000:ℝ) := by
  have hlo : (2490590914159/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(59/256:ℝ)) ≤ (15855597507/10000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(59/256:ℝ)) (by norm_num : 2*(59/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(59/256:ℝ)) ≤ (49811834138808651/10000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (59/256:ℝ) (2490590914159/500000000000:ℝ) (49811834138808651/10000000000000000:ℝ) (770451283849/50000000000000:ℝ) (1540905010899/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0354).1 (thetaFirstMode_refined_node_0354).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0182 :
    (-3593012909486386323726035763549/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (119/512:ℝ) ∧ thetaFirstModeFirst (119/512:ℝ) ≤ (-898251496591968160648747/6250000000000000000000000:ℝ) := by
  have hlo : (5000677622769/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(119/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(119/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(119/512:ℝ)) ≤ (1591765456103/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(119/512:ℝ)) (by norm_num : 2*(119/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(119/512:ℝ)) ≤ (5000679214534992079/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (119/512:ℝ) (5000677622769/1000000000000:ℝ) (5000679214534992079/1000000000000000000:ℝ) (189078604763/12500000000000:ℝ) (756315622931/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0355).1 (thetaFirstMode_refined_node_0355).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0183 :
    (-897962589555610564127376834331/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (841905060294227391/3621632464243356160:ℝ) ∧ thetaFirstModeFirst (841905060294227391/3621632464243356160:ℝ) ≤ (-897960859211800908692917/6250000000000000000000000:ℝ) := by
  have hlo : (2500557608851/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(841905060294227391/3621632464243356160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(841905060294227391/3621632464243356160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(841905060294227391/3621632464243356160:ℝ)) ≤ (795952373463/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(841905060294227391/3621632464243356160:ℝ)) (by norm_num : 2*(841905060294227391/3621632464243356160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(841905060294227391/3621632464243356160:ℝ)) ≤ (2500558404804746559/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (841905060294227391/3621632464243356160:ℝ) (2500557608851/500000000000:ℝ) (2500558404804746559/500000000000000000:ℝ) (378000034967/25000000000000:ℝ) (378000636709/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0359).1 (thetaFirstMode_refined_node_0359).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0184 :
    (-708269252823811056973420201491/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15/64:ℝ) ∧ thetaFirstModeFirst (15/64:ℝ) ≤ (-7082678837463234048273321/50000000000000000000000000:ℝ) := by
  have hlo : (5020249721601/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15/64:ℝ)) ≤ (1597995449951/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15/64:ℝ)) (by norm_num : 2*(15/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15/64:ℝ)) ≤ (5020251319597911943/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15/64:ℝ) (5020249721601/1000000000000:ℝ) (5020251319597911943/1000000000000000000:ℝ) (1484760599721/100000000000000:ℝ) (148476297237/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0360).1 (thetaFirstMode_refined_node_0360).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0185 :
    (-698030453691247456622886907467/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (121/512:ℝ) ∧ thetaFirstModeFirst (121/512:ℝ) ≤ (-1745072750218572632757533/12500000000000000000000000:ℝ) := by
  have hlo : (2519949211731/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(121/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(121/512:ℝ)) ≤ (320849965461/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(121/512:ℝ)) (by norm_num : 2*(121/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(121/512:ℝ)) ≤ (1007980005542519373/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (121/512:ℝ) (2519949211731/500000000000:ℝ) (1007980005542519373/200000000000000000:ℝ) (728647080143/50000000000000:ℝ) (728648249079/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0361).1 (thetaFirstMode_refined_node_0361).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0186 :
    (-1744514871464821679415714520549/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (978130364965943409/4138112237655400960:ℝ) ∧ thetaFirstModeFirst (978130364965943409/4138112237655400960:ℝ) ≤ (-697804595322383596253767/5000000000000000000000000:ℝ) := by
  have hlo : (504033216563/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(978130364965943409/4138112237655400960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(978130364965943409/4138112237655400960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(978130364965943409/4138112237655400960:ℝ)) ≤ (802193945877/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(978130364965943409/4138112237655400960:ℝ)) (by norm_num : 2*(978130364965943409/4138112237655400960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(978130364965943409/4138112237655400960:ℝ)) ≤ (2520166885009562061/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (978130364965943409/4138112237655400960:ℝ) (504033216563/100000000000:ℝ) (2520166885009562061/500000000000000000:ℝ) (1456693546909/100000000000000:ℝ) (728347942009/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0365).1 (thetaFirstMode_refined_node_0365).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0187 :
    (-171971547143478210791669890359/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (61/256:ℝ) ∧ thetaFirstModeFirst (61/256:ℝ) ≤ (-859856062961618016194453/6250000000000000000000000:ℝ) := by
  have hlo : (632453003521/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(61/256:ℝ)) ≤ (1610528683601/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(61/256:ℝ)) (by norm_num : 2*(61/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(61/256:ℝ)) ≤ (5059625638700116393/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (61/256:ℝ) (632453003521/125000000000:ℝ) (5059625638700116393/1000000000000000000:ℝ) (1430225827093/100000000000000:ℝ) (35755703263/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0366).1 (thetaFirstMode_refined_node_0366).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0188 :
    (-21182388993469662097696032303/156250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (123/512:ℝ) ∧ thetaFirstModeFirst (123/512:ℝ) ≤ (-338917562455355858244801/2500000000000000000000000:ℝ) := by
  have hlo : (1269856709177/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(123/512:ℝ)) ≤ (404208028661/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(123/512:ℝ)) (by norm_num : 2*(123/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(123/512:ℝ)) ≤ (1269857113385196973/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (123/512:ℝ) (1269856709177/250000000000:ℝ) (1269857113385196973/250000000000000000:ℝ) (280710381513/20000000000000:ℝ) (17544427211/1250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0367).1 (thetaFirstMode_refined_node_0367).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0189 :
    (-169404921870063426903633550137/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1133608087849118607/4717927560779292160:ℝ) ∧ thetaFirstModeFirst (1133608087849118607/4717927560779292160:ℝ) ≤ (-27104734597248377633553/200000000000000000000000:ℝ) := by
  have hlo : (1015971375457/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(1133608087849118607/4717927560779292160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1133608087849118607/4717927560779292160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1133608087849118607/4717927560779292160:ℝ)) ≤ (40424225021/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1133608087849118607/4717927560779292160:ℝ)) (by norm_num : 2*(1133608087849118607/4717927560779292160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1133608087849118607/4717927560779292160:ℝ)) ≤ (126996462356398453/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1133608087849118607/4717927560779292160:ℝ) (1015971375457/200000000000:ℝ) (126996462356398453/25000000000000000:ℝ) (28059562929/2000000000000:ℝ) (1402980415029/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0371).1 (thetaFirstMode_refined_node_0371).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0190 :
    (-130445548431422700513789529/976562500000000000000000000:ℝ) ≤ thetaFirstModeFirst (31/128:ℝ) ∧ thetaFirstModeFirst (31/128:ℝ) ≤ (-1335759800671582359044301/10000000000000000000000000:ℝ) := by
  have hlo : (5099307151249/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(31/128:ℝ)) ≤ (81158010831/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(31/128:ℝ)) (by norm_num : 2*(31/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(31/128:ℝ)) ≤ (254965438720593783/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (31/128:ℝ) (5099307151249/1000000000000:ℝ) (254965438720593783/50000000000000000:ℝ) (275453741949/20000000000000:ℝ) (537996463/39062500000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0372).1 (thetaFirstMode_refined_node_0372).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0191 :
    (-658020432144625345893465938507/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (125/512:ℝ) ∧ thetaFirstModeFirst (125/512:ℝ) ≤ (-6580191396819706755270939/50000000000000000000000000:ℝ) := by
  have hlo : (5119265275141/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(125/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(125/512:ℝ)) ≤ (814756543043/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(125/512:ℝ)) (by norm_num : 2*(125/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(125/512:ℝ)) ≤ (2559633452328087499/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (125/512:ℝ) (5119265275141/1000000000000:ℝ) (2559633452328087499/500000000000000000:ℝ) (1351372542879/100000000000000:ℝ) (270274948993/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0373).1 (thetaFirstMode_refined_node_0373).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

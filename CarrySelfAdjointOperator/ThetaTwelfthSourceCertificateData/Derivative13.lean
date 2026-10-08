import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0416 :
    (-118536158445612291899799451851/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (275/512:ℝ) ∧ thetaFirstModeFirst (275/512:ℝ) ≤ (-29633943154107415486181/6250000000000000000000000:ℝ) := by
  have hlo : (2299413445431/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(275/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(275/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(275/512:ℝ)) ≤ (2927704737511/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(275/512:ℝ)) (by norm_num : 2*(275/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(275/512:ℝ)) ≤ (9197656709431395023/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (275/512:ℝ) (2299413445431/250000000000:ℝ) (9197656709431395023/1000000000000000000:ℝ) (13247693251/50000000000000:ℝ) (13247732037/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0823).1 (thetaFirstMode_refined_node_0823).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0417 :
    (-237001211691605884081506846923/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (316275606984747764475/588826913916326538752:ℝ) ∧ thetaFirstModeFirst (316275606984747764475/588826913916326538752:ℝ) ≤ (-237000440244288953595923/50000000000000000000000000:ℝ) := by
  have hlo : (9198002160651/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(316275606984747764475/588826913916326538752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(316275606984747764475/588826913916326538752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(316275606984747764475/588826913916326538752:ℝ)) ≤ (2927815629991/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(316275606984747764475/588826913916326538752:ℝ)) (by norm_num : 2*(316275606984747764475/588826913916326538752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(316275606984747764475/588826913916326538752:ℝ)) ≤ (9198005088470315663/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (316275606984747764475/588826913916326538752:ℝ) (9198002160651/1000000000000:ℝ) (9198005088470315663/1000000000000000000:ℝ) (26486408473/100000000000000:ℝ) (26486486021/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0827).1 (thetaFirstMode_refined_node_0827).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0418 :
    (-45966848552307114275898296539/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (69/128:ℝ) ∧ thetaFirstModeFirst (69/128:ℝ) ≤ (-718229662629188424571/156250000000000000000000:ℝ) := by
  have hlo : (4616826190399/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(69/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(69/128:ℝ)) ≤ (2939163449869/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(69/128:ℝ)) (by norm_num : 2*(69/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(69/128:ℝ)) ≤ (9233655319964301317/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (69/128:ℝ) (4616826190399/500000000000:ℝ) (9233655319964301317/1000000000000000000:ℝ) (159897029/625000000000:ℝ) (5116719967/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0828).1 (thetaFirstMode_refined_node_0828).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0419 :
    (-222785666120660253862695479187/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (277/512:ℝ) ∧ thetaFirstModeFirst (277/512:ℝ) ≤ (-2227849358687339713131/500000000000000000000000:ℝ) := by
  have hlo : (1853958374881/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(277/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(277/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(277/512:ℝ)) ≤ (2950667010359/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(277/512:ℝ)) (by norm_num : 2*(277/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(277/512:ℝ)) ≤ (9269794825074761887/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (277/512:ℝ) (1853958374881/200000000000:ℝ) (9269794825074761887/1000000000000000000:ℝ) (1234978251/5000000000000:ℝ) (24699637901/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0829).1 (thetaFirstMode_refined_node_0829).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0420 :
    (-4454374444447249812042543297/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1687945374778197279393/3119848372759046172160:ℝ) ∧ thetaFirstModeFirst (1687945374778197279393/3119848372759046172160:ℝ) ≤ (-13919874510341896852683/3125000000000000000000000:ℝ) := by
  have hlo : (579383778181/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(1687945374778197279393/3119848372759046172160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1687945374778197279393/3119848372759046172160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1687945374778197279393/3119848372759046172160:ℝ)) ≤ (118031118629/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1687945374778197279393/3119848372759046172160:ℝ)) (by norm_num : 2*(1687945374778197279393/3119848372759046172160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1687945374778197279393/3119848372759046172160:ℝ)) ≤ (370805736067035997/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1687945374778197279393/3119848372759046172160:ℝ) (579383778181/62500000000:ℝ) (370805736067035997/40000000000000000:ℝ) (24691188943/100000000000000:ℝ) (12345630901/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0833).1 (thetaFirstMode_refined_node_0833).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0421 :
    (-1686895456485791366063307927/390625000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (139/256:ℝ) ∧ thetaFirstModeFirst (139/256:ℝ) ≤ (-53980477047536488513827/12500000000000000000000000:ℝ) := by
  have hlo : (9306072813991/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(139/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(139/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(139/256:ℝ)) ≤ (185138474657/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(139/256:ℝ)) (by norm_num : 2*(139/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(139/256:ℝ)) ≤ (581629736013108601/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (139/256:ℝ) (9306072813991/1000000000000:ℝ) (581629736013108601/62500000000000000:ℝ) (5960693797/25000000000000:ℝ) (2980355727/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0834).1 (thetaFirstMode_refined_node_0834).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0422 :
    (-1046205931187596258176665731/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (279/512:ℝ) ∧ thetaFirstModeFirst (279/512:ℝ) ≤ (-1307753097178921545909/312500000000000000000000:ℝ) := by
  have hlo : (233562393829/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(279/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(279/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(279/512:ℝ)) ≤ (594761875709/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(279/512:ℝ)) (by norm_num : 2*(279/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(279/512:ℝ)) ≤ (1868499745394264437/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (279/512:ℝ) (233562393829/25000000000:ℝ) (1868499745394264437/200000000000000000:ℝ) (5753109521/25000000000000:ℝ) (575312663/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0835).1 (thetaFirstMode_refined_node_0835).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0423 :
    (-209178193349719400826863010881/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1800849110067536394591/3304670826434478952960:ℝ) ∧ thetaFirstModeFirst (1800849110067536394591/3304670826434478952960:ℝ) ≤ (-26147187856070551541157/6250000000000000000000000:ℝ) := by
  have hlo : (4671422272751/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1800849110067536394591/3304670826434478952960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1800849110067536394591/3304670826434478952960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1800849110067536394591/3304670826434478952960:ℝ)) ≤ (2973920402619/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1800849110067536394591/3304670826434478952960:ℝ)) (by norm_num : 2*(1800849110067536394591/3304670826434478952960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1800849110067536394591/3304670826434478952960:ℝ)) ≤ (9342847519425032067/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1800849110067536394591/3304670826434478952960:ℝ) (4671422272751/500000000000:ℝ) (9342847519425032067/1000000000000000000:ℝ) (5751156907/25000000000000:ℝ) (23004696043/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0839).1 (thetaFirstMode_refined_node_0839).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0424 :
    (-101368755551022874061675919489/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (35/64:ℝ) ∧ thetaFirstModeFirst (35/64:ℝ) ≤ (-20273683953549457910623/5000000000000000000000000:ℝ) := by
  have hlo : (9379061247681/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(35/64:ℝ)) ≤ (1492724269683/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(35/64:ℝ)) (by norm_num : 2*(35/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(35/64:ℝ)) ≤ (4689532116566225019/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (35/64:ℝ) (9379061247681/1000000000000:ℝ) (4689532116566225019/500000000000000000:ℝ) (2220785183/10000000000000:ℝ) (22207918131/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0840).1 (thetaFirstMode_refined_node_0840).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0425 :
    (-98203894776773001478309587003/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (281/512:ℝ) ∧ thetaFirstModeFirst (281/512:ℝ) ≤ (-24550892082273800344127/6250000000000000000000000:ℝ) := by
  have hlo : (4707884927751/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(281/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(281/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(281/512:ℝ)) ≤ (1498566627287/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(281/512:ℝ)) (by norm_num : 2*(281/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(281/512:ℝ)) ≤ (4707886426318448191/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (281/512:ℝ) (4707884927751/500000000000:ℝ) (4707886426318448191/500000000000000000:ℝ) (5357082377/25000000000000:ℝ) (21428393733/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0841).1 (thetaFirstMode_refined_node_0841).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0426 :
    (-4908713650861315539022996177/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1920416486701757070609/3499003694289312924160:ℝ) ∧ thetaFirstModeFirst (1920416486701757070609/3499003694289312924160:ℝ) ≤ (-98173946659717973664693/25000000000000000000000000:ℝ) := by
  have hlo : (4708059440879/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1920416486701757070609/3499003694289312924160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1920416486701757070609/3499003694289312924160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1920416486701757070609/3499003694289312924160:ℝ)) ≤ (599448870621/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1920416486701757070609/3499003694289312924160:ℝ)) (by norm_num : 2*(1920416486701757070609/3499003694289312924160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1920416486701757070609/3499003694289312924160:ℝ)) ≤ (1883224375800839253/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1920416486701757070609/3499003694289312924160:ℝ) (4708059440879/500000000000:ℝ) (1883224375800839253/200000000000000000:ℝ) (21421050267/100000000000000:ℝ) (2677639309/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0845).1 (thetaFirstMode_refined_node_0845).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0427 :
    (-38049654596748787736749519491/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (141/256:ℝ) ∧ thetaFirstModeFirst (141/256:ℝ) ≤ (-2378095479259516418677/625000000000000000000000:ℝ) := by
  have hlo : (590788883547/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(141/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(141/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(141/256:ℝ)) ≤ (601772740493/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(141/256:ℝ)) (by norm_num : 2*(141/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(141/256:ℝ)) ≤ (1890525029123625349/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (141/256:ℝ) (590788883547/62500000000:ℝ) (1890525029123625349/200000000000000000:ℝ) (4134639791/20000000000000:ℝ) (20673261159/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0846).1 (thetaFirstMode_refined_node_0846).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0428 :
    (-184255267542203104984155878591/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (283/512:ℝ) ∧ thetaFirstModeFirst (283/512:ℝ) ≤ (-184254650728803337278867/50000000000000000000000000:ℝ) := by
  have hlo : (9489618653753/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(283/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(283/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(283/512:ℝ)) ≤ (3020640062031/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(283/512:ℝ)) (by norm_num : 2*(283/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(283/512:ℝ)) ≤ (9489621674396155383/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (283/512:ℝ) (9489618653753/1000000000000:ℝ) (9489621674396155383/1000000000000000000:ℝ) (19941802539/100000000000000:ℝ) (19941862777/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0847).1 (thetaFirstMode_refined_node_0847).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0429 :
    (-18419958018692515473673247019/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2046989131565308077807/3703263400356200988160:ℝ) ∧ thetaFirstModeFirst (2046989131565308077807/3703263400356200988160:ℝ) ≤ (-3683979270741424945713/1000000000000000000000000:ℝ) := by
  have hlo : (9489967931767/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(2046989131565308077807/3703263400356200988160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2046989131565308077807/3703263400356200988160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2046989131565308077807/3703263400356200988160:ℝ)) ≤ (3020751240699/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2046989131565308077807/3703263400356200988160:ℝ)) (by norm_num : 2*(2046989131565308077807/3703263400356200988160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2046989131565308077807/3703263400356200988160:ℝ)) ≤ (9489970952521293507/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2046989131565308077807/3703263400356200988160:ℝ) (9489967931767/1000000000000:ℝ) (9489970952521293507/1000000000000000000:ℝ) (398700439/2000000000000:ℝ) (1993508217/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0851).1 (thetaFirstMode_refined_node_0851).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0430 :
    (-44606283514090664598901058553/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (71/128:ℝ) ∧ thetaFirstModeFirst (71/128:ℝ) ≤ (-35684906931002738544557/10000000000000000000000000:ℝ) := by
  have hlo : (9526759971027/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(71/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(71/128:ℝ)) ≤ (758115628241/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(71/128:ℝ)) (by norm_num : 2*(71/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(71/128:ℝ)) ≤ (2381690750872527913/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (71/128:ℝ) (9526759971027/1000000000000:ℝ) (2381690750872527913/250000000000000000:ℝ) (3846699391/20000000000000:ℝ) (19233555281/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0852).1 (thetaFirstMode_refined_node_0852).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0431 :
    (-172754287827381820760413606889/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (285/512:ℝ) ∧ thetaFirstModeFirst (285/512:ℝ) ≤ (-21594213178210310429903/6250000000000000000000000:ℝ) := by
  have hlo : (4782023327653/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(285/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(285/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(285/512:ℝ)) ≤ (3044331235663/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(285/512:ℝ)) (by norm_num : 2*(285/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(285/512:ℝ)) ≤ (9564049699640231159/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (285/512:ℝ) (4782023327653/500000000000:ℝ) (9564049699640231159/1000000000000000000:ℝ) (4636913251/25000000000000:ℝ) (18547709471/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0853).1 (thetaFirstMode_refined_node_0853).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0432 :
    (-172701971547548303234881112397/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (436184715072406009365/783576290780361661952:ℝ) ∧ thetaFirstModeFirst (436184715072406009365/783576290780361661952:ℝ) ≤ (-1079383683193344542407/312500000000000000000000:ℝ) := by
  have hlo : (1195549525339/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(436184715072406009365/783576290780361661952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(436184715072406009365/783576290780361661952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(436184715072406009365/783576290780361661952:ℝ)) ≤ (3044442500081/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(436184715072406009365/783576290780361661952:ℝ)) (by norm_num : 2*(436184715072406009365/783576290780361661952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(436184715072406009365/783576290780361661952:ℝ)) ≤ (9564399247156969033/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (436184715072406009365/783576290780361661952:ℝ) (1195549525339/125000000000:ℝ) (9564399247156969033/1000000000000000000:ℝ) (927067013/5000000000000:ℝ) (18541396709/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0857).1 (thetaFirstMode_refined_node_0857).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0433 :
    (-41809799623488027101866026693/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (143/256:ℝ) ∧ thetaFirstModeFirst (143/256:ℝ) ≤ (-16723863270376258709367/5000000000000000000000000:ℝ) := by
  have hlo : (4800739637771/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(143/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(143/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(143/256:ℝ)) ≤ (764061602807/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(143/256:ℝ)) (by norm_num : 2*(143/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(143/256:ℝ)) ≤ (2400370582947251551/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (143/256:ℝ) (4800739637771/500000000000:ℝ) (2400370582947251551/250000000000000000:ℝ) (3576731077/20000000000000:ℝ) (17883710043/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0858).1 (thetaFirstMode_refined_node_0858).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0434 :
    (-8093819494184600861601353041/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (287/512:ℝ) ∧ thetaFirstModeFirst (287/512:ℝ) ≤ (-2023448003795163738991/625000000000000000000000:ℝ) := by
  have hlo : (9639058402911/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(287/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(287/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(287/512:ℝ)) ≤ (3068208221473/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(287/512:ℝ)) (by norm_num : 2*(287/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(287/512:ℝ)) ≤ (9639061471122026489/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (287/512:ℝ) (9639058402911/1000000000000:ℝ) (9639061471122026489/1000000000000000000:ℝ) (215511281/1250000000000:ℝ) (862047769/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0859).1 (thetaFirstMode_refined_node_0859).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0435 :
    (-32365453507474057315971426559/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2322591790558180904343/4143304883478902172160:ℝ) ∧ thetaFirstModeFirst (2322591790558180904343/4143304883478902172160:ℝ) ≤ (-80913359052563592406619/25000000000000000000000000:ℝ) := by
  have hlo : (4819704118569/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(2322591790558180904343/4143304883478902172160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2322591790558180904343/4143304883478902172160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2322591790558180904343/4143304883478902172160:ℝ)) ≤ (3068319577189/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2322591790558180904343/4143304883478902172160:ℝ)) (by norm_num : 2*(2322591790558180904343/4143304883478902172160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2322591790558180904343/4143304883478902172160:ℝ)) ≤ (9639411305459922077/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2322591790558180904343/4143304883478902172160:ℝ) (4819704118569/500000000000:ℝ) (9639411305459922077/1000000000000000000:ℝ) (17235028451/100000000000000:ℝ) (3447016267/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0863).1 (thetaFirstMode_refined_node_0863).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0436 :
    (-19582804971781764829843209489/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/16:ℝ) ∧ thetaFirstModeFirst (9/16:ℝ) ≤ (-39165476506853336734149/12500000000000000000000000:ℝ) := by
  have hlo : (4838392305413/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/16:ℝ)) ≤ (3080216848919/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/16:ℝ)) (by norm_num : 2*(9/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/16:ℝ)) ≤ (9676787691045987967/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/16:ℝ) (4838392305413/500000000000:ℝ) (9676787691045987967/1000000000000000000:ℝ) (8309403073/50000000000000:ℝ) (2077357167/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0864).1 (thetaFirstMode_refined_node_0864).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0437 :
    (-151593979734329484391987521549/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (289/512:ℝ) ∧ thetaFirstModeFirst (289/512:ℝ) ≤ (-75796730715399661167193/25000000000000000000000000:ℝ) := by
  have hlo : (9714658474943/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(289/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(289/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(289/512:ℝ)) ≤ (3092272476803/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(289/512:ℝ)) (by norm_num : 2*(289/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(289/512:ℝ)) ≤ (9714661567216967179/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (289/512:ℝ) (9714658474943/1000000000000:ℝ) (9714661567216967179/1000000000000000000:ℝ) (8008395751/50000000000000:ℝ) (16016841031/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0865).1 (thetaFirstMode_refined_node_0865).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0438 :
    (-37886970455235311976951301697/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2472381744748202416041/4379996680278775605760:ℝ) ∧ thetaFirstModeFirst (2472381744748202416041/4379996680278775605760:ℝ) ≤ (-37886840914290572907677/12500000000000000000000000:ℝ) := by
  have hlo : (4857504306613/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(2472381744748202416041/4379996680278775605760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2472381744748202416041/4379996680278775605760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2472381744748202416041/4379996680278775605760:ℝ)) ≤ (3092383929303/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2472381744748202416041/4379996680278775605760:ℝ)) (by norm_num : 2*(2472381744748202416041/4379996680278775605760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2472381744748202416041/4379996680278775605760:ℝ)) ≤ (9715011705610799679/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2472381744748202416041/4379996680278775605760:ℝ) (4857504306613/500000000000:ℝ) (9715011705610799679/1000000000000000000:ℝ) (8005664329/50000000000000:ℝ) (4002844543/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0869).1 (thetaFirstMode_refined_node_0869).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0439 :
    (-14666769483674202449357448651/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (145/256:ℝ) ∧ thetaFirstModeFirst (145/256:ℝ) ≤ (-916669947510919926183/312500000000000000000000:ℝ) := by
  have hlo : (4876340286587/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(145/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(145/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(145/256:ℝ)) ≤ (1552187644541/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(145/256:ℝ)) (by norm_num : 2*(145/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(145/256:ℝ)) ≤ (4876341838776493813/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (145/256:ℝ) (4876340286587/500000000000:ℝ) (4876341838776493813/500000000000000000:ℝ) (192928709/1250000000000:ℝ) (3086868927/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0870).1 (thetaFirstMode_refined_node_0870).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0440 :
    (-7094016173457326134443446183/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (291/512:ℝ) ∧ thetaFirstModeFirst (291/512:ℝ) ≤ (-14187983494351461946011/5000000000000000000000000:ℝ) := by
  have hlo : (979085148569/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(291/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(291/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(291/512:ℝ)) ≤ (779131367607/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(291/512:ℝ)) (by norm_num : 2*(291/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(291/512:ℝ)) ≤ (2447713650554577951/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (291/512:ℝ) (979085148569/100000000000:ℝ) (2447713650554577951/250000000000000000:ℝ) (14870772819/100000000000000:ℝ) (2974163833/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0871).1 (thetaFirstMode_refined_node_0871).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0441 :
    (-1772963598784072678930509591/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2630697969772508777559/4628436250915918927360:ℝ) ∧ thetaFirstModeFirst (2630697969772508777559/4628436250915918927360:ℝ) ≤ (-14183659950862127124571/5000000000000000000000000:ℝ) := by
  have hlo : (979120194507/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(2630697969772508777559/4628436250915918927360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2630697969772508777559/4628436250915918927360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2630697969772508777559/4628436250915918927360:ℝ)) ≤ (194789814071/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2630697969772508777559/4628436250915918927360:ℝ)) (by norm_num : 2*(2630697969772508777559/4628436250915918927360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2630697969772508777559/4628436250915918927360:ℝ)) ≤ (611950316356755103/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2630697969772508777559/4628436250915918927360:ℝ) (979120194507/100000000000:ℝ) (611950316356755103/62500000000000000:ℝ) (14865695153/100000000000000:ℝ) (2973148297/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0875).1 (thetaFirstMode_refined_node_0875).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0442 :
    (-137228657035860008945981908471/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (73/128:ℝ) ∧ thetaFirstModeFirst (73/128:ℝ) ≤ (-137228182856957643753783/50000000000000000000000000:ℝ) := by
  have hlo : (9829171794933/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(73/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(73/128:ℝ)) ≤ (3128723206239/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(73/128:ℝ)) (by norm_num : 2*(73/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(73/128:ℝ)) ≤ (9829174923657998727/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (73/128:ℝ) (9829171794933/1000000000000:ℝ) (9829174923657998727/1000000000000000000:ℝ) (14325683451/100000000000000:ℝ) (14325728273/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0876).1 (thetaFirstMode_refined_node_0876).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0443 :
    (-33177384932339611001601442197/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (293/512:ℝ) ∧ thetaFirstModeFirst (293/512:ℝ) ≤ (-33177269885165861903363/12500000000000000000000000:ℝ) := by
  have hlo : (4933821042813/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(293/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(293/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(293/512:ℝ)) ≤ (3140968682639/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(293/512:ℝ)) (by norm_num : 2*(293/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(293/512:ℝ)) ≤ (9867645226597903927/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (293/512:ℝ) (4933821042813/500000000000:ℝ) (9867645226597903927/1000000000000000000:ℝ) (6899252351/50000000000000:ℝ) (3449637011/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0877).1 (thetaFirstMode_refined_node_0877).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0444 :
    (-6633450580908118564124625927/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2797962146921232130257/4889119879777782300160:ℝ) ∧ thetaFirstModeFirst (2797962146921232130257/4889119879777782300160:ℝ) ≤ (-66334275781109419701253/25000000000000000000000000:ℝ) := by
  have hlo : (9867992882963/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(2797962146921232130257/4889119879777782300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2797962146921232130257/4889119879777782300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2797962146921232130257/4889119879777782300160:ℝ)) ≤ (1570540172461/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2797962146921232130257/4889119879777782300160:ℝ)) (by norm_num : 2*(2797962146921232130257/4889119879777782300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2797962146921232130257/4889119879777782300160:ℝ)) ≤ (4933998012022270373/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2797962146921232130257/4889119879777782300160:ℝ) (9867992882963/1000000000000:ℝ) (4933998012022270373/500000000000000000:ℝ) (6896893831/50000000000000:ℝ) (1379383099/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0881).1 (thetaFirstMode_refined_node_0881).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0445 :
    (-32079967050118488968082953711/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (147/256:ℝ) ∧ thetaFirstModeFirst (147/256:ℝ) ≤ (-3207985541535814450399/1250000000000000000000000:ℝ) := by
  have hlo : (495313147239/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(147/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(147/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(147/256:ℝ)) ≤ (1576631043239/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(147/256:ℝ)) (by norm_num : 2*(147/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(147/256:ℝ)) ≤ (4953133049022339727/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (147/256:ℝ) (495313147239/50000000000:ℝ) (4953133049022339727/500000000000000000:ℝ) (6644362441/50000000000000:ℝ) (6644383393/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0882).1 (thetaFirstMode_refined_node_0882).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0446 :
    (-124056591270403924868270545329/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (295/512:ℝ) ∧ thetaFirstModeFirst (295/512:ℝ) ≤ (-387675493896549856977/156250000000000000000000:ℝ) := by
  have hlo : (4972517480851/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(295/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(295/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(295/512:ℝ)) ≤ (3165603605339/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(295/512:ℝ)) (by norm_num : 2*(295/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(295/512:ℝ)) ≤ (9945038127307765027/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (295/512:ℝ) (4972517480851/500000000000:ℝ) (9945038127307765027/1000000000000000000:ℝ) (79974027/625000000000:ℝ) (12795884827/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0883).1 (thetaFirstMode_refined_node_0883).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0447 :
    (-7751163915930783169895100477/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (594922741712509294755/1032512240214680279552:ℝ) ∧ thetaFirstModeFirst (594922741712509294755/1032512240214680279552:ℝ) ≤ (-62009094772965032958987/25000000000000000000000000:ℝ) := by
  have hlo : (4972693056839/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(594922741712509294755/1032512240214680279552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(594922741712509294755/1032512240214680279552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(594922741712509294755/1032512240214680279552:ℝ)) ≤ (791428845127/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(594922741712509294755/1032512240214680279552:ℝ)) (by norm_num : 2*(594922741712509294755/1032512240214680279552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(594922741712509294755/1032512240214680279552:ℝ)) ≤ (2486347319849067311/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (594922741712509294755/1032512240214680279552:ℝ) (4972693056839/500000000000:ℝ) (2486347319849067311/250000000000000000:ℝ) (12791464733/100000000000000:ℝ) (3197876307/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0887).1 (thetaFirstMode_refined_node_0887).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0320 :
    (-6580391700091246395847067647/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (211/512:ℝ) ∧ thetaFirstModeFirst (211/512:ℝ) ≤ (-131607490515433995560369/5000000000000000000000000:ℝ) := by
  have hlo : (3581569983813/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(211/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(211/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(211/512:ℝ)) ≤ (91203949687/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(211/512:ℝ)) (by norm_num : 2*(211/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(211/512:ℝ)) ≤ (286525689909031391/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (211/512:ℝ) (3581569983813/500000000000:ℝ) (286525689909031391/40000000000000000:ℝ) (38074591613/20000000000000:ℝ) (23796674017/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0631).1 (thetaFirstMode_refined_node_0631).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0321 :
    (-657848293661949787266058245451/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (145757762788870993959/353665902141891765760:ℝ) ∧ thetaFirstModeFirst (145757762788870993959/353665902141891765760:ℝ) ≤ (-657846576655471720843251/25000000000000000000000000:ℝ) := by
  have hlo : (7163493566113/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(145757762788870993959/353665902141891765760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(145757762788870993959/353665902141891765760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(145757762788870993959/353665902141891765760:ℝ)) ≤ (2280211296093/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(145757762788870993959/353665902141891765760:ℝ)) (by norm_num : 2*(145757762788870993959/353665902141891765760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(145757762788870993959/353665902141891765760:ℝ)) ≤ (7163495846326696149/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (145757762788870993959/353665902141891765760:ℝ) (7163493566113/1000000000000:ℝ) (7163495846326696149/1000000000000000000:ℝ) (95154001427/50000000000000:ℝ) (95154218399/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0635).1 (thetaFirstMode_refined_node_0635).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0322 :
    (-643069310016350191327931928339/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (53/128:ℝ) ∧ thetaFirstModeFirst (53/128:ℝ) ≤ (-25722705037740885353191/1000000000000000000000000:ℝ) := by
  have hlo : (3595587852387/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(53/128:ℝ)) ≤ (2289022796333/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(53/128:ℝ)) (by norm_num : 2*(53/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(53/128:ℝ)) ≤ (7191177993800178469/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (53/128:ℝ) (3595587852387/500000000000:ℝ) (7191177993800178469/1000000000000000000:ℝ) (7411627693/4000000000000:ℝ) (92645558231/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0636).1 (thetaFirstMode_refined_node_0636).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0323 :
    (-628370690310001932066161928609/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (213/512:ℝ) ∧ thetaFirstModeFirst (213/512:ℝ) ≤ (-125673807826113142827569/5000000000000000000000000:ℝ) := by
  have hlo : (1443864234139/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(213/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(213/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(213/512:ℝ)) ≤ (2297981778251/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(213/512:ℝ)) (by norm_num : 2*(213/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(213/512:ℝ)) ≤ (7219323468680893843/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (213/512:ℝ) (1443864234139/200000000000:ℝ) (7219323468680893843/1000000000000000000:ℝ) (90162158371/50000000000000:ℝ) (90162365563/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0637).1 (thetaFirstMode_refined_node_0637).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0324 :
    (-628188395966882458476796945611/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (158673294672040530657/381389448748703772160:ℝ) ∧ thetaFirstModeFirst (158673294672040530657/381389448748703772160:ℝ) ≤ (-125637349039345358836027/5000000000000000000000000:ℝ) := by
  have hlo : (1443934839391/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(158673294672040530657/381389448748703772160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(158673294672040530657/381389448748703772160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(158673294672040530657/381389448748703772160:ℝ)) ≤ (1149047075011/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(158673294672040530657/381389448748703772160:ℝ)) (by norm_num : 2*(158673294672040530657/381389448748703772160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(158673294672040530657/381389448748703772160:ℝ)) ≤ (3609838247525032523/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (158673294672040530657/381389448748703772160:ℝ) (1443934839391/200000000000:ℝ) (3609838247525032523/500000000000000000:ℝ) (90131436197/50000000000000:ℝ) (180263286657/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0641).1 (thetaFirstMode_refined_node_0641).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0325 :
    (-15348501354658158059784474213/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (107/256:ℝ) ∧ thetaFirstModeFirst (107/256:ℝ) ≤ (-153484608858300541738503/6250000000000000000000000:ℝ) := by
  have hlo : (905947099357/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(107/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(107/256:ℝ)) ≤ (288371978079/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(107/256:ℝ)) (by norm_num : 2*(107/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(107/256:ℝ)) ≤ (905947387729139847/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (107/256:ℝ) (905947099357/125000000000:ℝ) (905947387729139847/125000000000000000:ℝ) (175471724979/100000000000000:ℝ) (17547212979/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0642).1 (thetaFirstMode_refined_node_0642).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0326 :
    (-14994353724613330857792764819/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (215/512:ℝ) ∧ thetaFirstModeFirst (215/512:ℝ) ≤ (-149943140548005677139231/6250000000000000000000000:ℝ) := by
  have hlo : (3637971504201/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(215/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(215/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(215/512:ℝ)) ≤ (579001268179/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(215/512:ℝ)) (by norm_num : 2*(215/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(215/512:ℝ)) ≤ (1818986331102269147/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (215/512:ℝ) (3637971504201/500000000000:ℝ) (1818986331102269147/250000000000000000:ℝ) (42682709031/25000000000000:ℝ) (8536561577/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0643).1 (thetaFirstMode_refined_node_0643).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0327 :
    (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (34519255196979847635/82199252318350141952:ℝ) ∧ thetaFirstModeFirst (34519255196979847635/82199252318350141952:ℝ) ≤ (-1199197058361699310408581/50000000000000000000000000:ℝ) := by
  have hlo : (7276295494417/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(34519255196979847635/82199252318350141952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(34519255196979847635/82199252318350141952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(34519255196979847635/82199252318350141952:ℝ)) ≤ (2316117272523/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(34519255196979847635/82199252318350141952:ℝ)) (by norm_num : 2*(34519255196979847635/82199252318350141952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(34519255196979847635/82199252318350141952:ℝ)) ≤ (7276297810537349139/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (34519255196979847635/82199252318350141952:ℝ) (7276295494417/1000000000000:ℝ) (7276297810537349139/1000000000000000000:ℝ) (170672733493/100000000000000:ℝ) (170673128793/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0647).1 (thetaFirstMode_refined_node_0647).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0328 :
    (-73233715856324238905342175189/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (27/64:ℝ) ∧ thetaFirstModeFirst (27/64:ℝ) ≤ (-1171736343124823548781709/50000000000000000000000000:ℝ) := by
  have hlo : (7304420244169/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(27/64:ℝ)) ≤ (1162534830139/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(27/64:ℝ)) (by norm_num : 2*(27/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(27/64:ℝ)) ≤ (3652211284620871427/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (27/64:ℝ) (7304420244169/1000000000000:ℝ) (3652211284620871427/500000000000000000:ℝ) (166099594661/100000000000000:ℝ) (20762497607/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0648).1 (thetaFirstMode_refined_node_0648).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0329 :
    (-17881985796305212669408737807/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (217/512:ℝ) ∧ thetaFirstModeFirst (217/512:ℝ) ≤ (-114444404248090926647781/5000000000000000000000000:ℝ) := by
  have hlo : (1466601787337/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(217/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(217/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(217/512:ℝ)) ≤ (36471401963/15625000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(217/512:ℝ)) (by norm_num : 2*(217/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(217/512:ℝ)) ≤ (114578301107147059/15625000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (217/512:ℝ) (1466601787337/200000000000:ℝ) (114578301107147059/15625000000000000:ℝ) (80787985213/50000000000000:ℝ) (161576347573/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0649).1 (thetaFirstMode_refined_node_0649).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0330 :
    (-22882298452005075002291703247/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (187594809587397482193/442594949984965788160:ℝ) ∧ thetaFirstModeFirst (187594809587397482193/442594949984965788160:ℝ) ≤ (-572055937433509458801357/25000000000000000000000000:ℝ) := by
  have hlo : (3666680456861/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(187594809587397482193/442594949984965788160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(187594809587397482193/442594949984965788160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(187594809587397482193/442594949984965788160:ℝ)) ≤ (1167140881713/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(187594809587397482193/442594949984965788160:ℝ)) (by norm_num : 2*(187594809587397482193/442594949984965788160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(187594809587397482193/442594949984965788160:ℝ)) ≤ (3666681624003388809/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (187594809587397482193/442594949984965788160:ℝ) (3666680456861/500000000000:ℝ) (3666681624003388809/500000000000000000:ℝ) (161521047537/100000000000000:ℝ) (6460856983/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0653).1 (thetaFirstMode_refined_node_0653).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0331 :
    (-223532947536861015202605822641/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (109/256:ℝ) ∧ thetaFirstModeFirst (109/256:ℝ) ≤ (-6985385939860493742621/312500000000000000000000:ℝ) := by
  have hlo : (7361709522181/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(109/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(109/256:ℝ)) ≤ (468661081527/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(109/256:ℝ)) (by norm_num : 2*(109/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(109/256:ℝ)) ≤ (1472342373097652511/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (109/256:ℝ) (7361709522181/1000000000000:ℝ) (1472342373097652511/200000000000000000:ℝ) (982237241/625000000000:ℝ) (157158326831/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0654).1 (thetaFirstMode_refined_node_0654).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0332 :
    (-545692967879201670044909165677/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (219/512:ℝ) ∧ thetaFirstModeFirst (219/512:ℝ) ≤ (-54569150436434823947043/2500000000000000000000000:ℝ) := by
  have hlo : (7390522438591/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(219/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(219/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(219/512:ℝ)) ≤ (1176238422843/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(219/512:ℝ)) (by norm_num : 2*(219/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(219/512:ℝ)) ≤ (3695262395534608899/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (219/512:ℝ) (7390522438591/1000000000000:ℝ) (3695262395534608899/500000000000000000:ℝ) (7642178973/5000000000000:ℝ) (152843939023/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0655).1 (thetaFirstMode_refined_node_0655).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0333 :
    (-681918162937633043325755199/31250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (203740906957094489391/476299293587687964160:ℝ) ∧ thetaFirstModeFirst (203740906957094489391/476299293587687964160:ℝ) ≤ (-43642645375945873763849/2000000000000000000000000:ℝ) := by
  have hlo : (295634957489/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(203740906957094489391/476299293587687964160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(203740906957094489391/476299293587687964160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(203740906957094489391/476299293587687964160:ℝ)) ≤ (1470367957/625000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(203740906957094489391/476299293587687964160:ℝ)) (by norm_num : 2*(203740906957094489391/476299293587687964160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(203740906957094489391/476299293587687964160:ℝ)) ≤ (4619297681135501/625000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (203740906957094489391/476299293587687964160:ℝ) (295634957489/40000000000:ℝ) (4619297681135501/625000000000000:ℝ) (152791681241/100000000000000:ℝ) (152792040699/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0659).1 (thetaFirstMode_refined_node_0659).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0334 :
    (-1065604242487721865710918355903/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (55/128:ℝ) ∧ thetaFirstModeFirst (55/128:ℝ) ≤ (-416250537047178660153/19531250000000000000000:ℝ) := by
  have hlo : (7419448125569/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(55/128:ℝ)) ≤ (2361684179731/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(55/128:ℝ)) (by norm_num : 2*(55/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(55/128:ℝ)) ≤ (7419450487253651483/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (55/128:ℝ) (7419448125569/1000000000000:ℝ) (7419450487253651483/1000000000000000000:ℝ) (58058937/39062500000:ℝ) (148631229741/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0660).1 (thetaFirstMode_refined_node_0660).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0335 :
    (-65019576997832747582045306863/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (221/512:ℝ) ∧ thetaFirstModeFirst (221/512:ℝ) ≤ (-65019401425270190145807/3125000000000000000000000:ℝ) := by
  have hlo : (1862121756121/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(221/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(221/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(221/512:ℝ)) ≤ (2370927550263/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(221/512:ℝ)) (by norm_num : 2*(221/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(221/512:ℝ)) ≤ (7448489395413388959/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (221/512:ℝ) (1862121756121/250000000000:ℝ) (7448489395413388959/1000000000000000000:ℝ) (36129481767/25000000000000:ℝ) (9032391857/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0661).1 (thetaFirstMode_refined_node_0661).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0336 :
    (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (221110673372114090409/512228437469441512960:ℝ) ∧ thetaFirstModeFirst (221110673372114090409/512228437469441512960:ℝ) ≤ (-4160033018129928440171/200000000000000000000000:ℝ) := by
  have hlo : (59590704597/8000000000:ℝ) ≤ Real.pi*Real.exp (2*(221110673372114090409/512228437469441512960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(221110673372114090409/512228437469441512960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(221110673372114090409/512228437469441512960:ℝ)) ≤ (2371039293017/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(221110673372114090409/512228437469441512960:ℝ)) (by norm_num : 2*(221110673372114090409/512228437469441512960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(221110673372114090409/512228437469441512960:ℝ)) ≤ (7448840445667156081/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (221110673372114090409/512228437469441512960:ℝ) (59590704597/8000000000:ℝ) (7448840445667156081/1000000000000000000:ℝ) (72234452543/50000000000000:ℝ) (144469247629/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0665).1 (thetaFirstMode_refined_node_0665).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0337 :
    (-31734578013565063304325910753/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (111/256:ℝ) ∧ thetaFirstModeFirst (111/256:ℝ) ≤ (-2538759362205402657627/125000000000000000000000:ℝ) := by
  have hlo : (1869409894609/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(111/256:ℝ)) ≤ (595051774581/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(111/256:ℝ)) (by norm_num : 2*(111/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(111/256:ℝ)) ≤ (1869410489661247533/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (111/256:ℝ) (1869409894609/250000000000:ℝ) (1869410489661247533/250000000000000000:ℝ) (1405028203/1000000000000:ℝ) (17562894341/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0666).1 (thetaFirstMode_refined_node_0666).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0338 :
    (-495588823823762242047718237719/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (223/512:ℝ) ∧ thetaFirstModeFirst (223/512:ℝ) ≤ (-247793738206430294024529/12500000000000000000000000:ℝ) := by
  have hlo : (3753453116129/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(223/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(223/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(223/512:ℝ)) ≤ (2389522965509/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(223/512:ℝ)) (by norm_num : 2*(223/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(223/512:ℝ)) ≤ (7506908621782315837/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (223/512:ℝ) (3753453116129/500000000000:ℝ) (7506908621782315837/1000000000000000000:ℝ) (68291839601/50000000000000:ℝ) (68292002787/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0667).1 (thetaFirstMode_refined_node_0667).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0339 :
    (-99088961506408080648845019957/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (239784500047674155607/550507092643036572160:ℝ) ∧ thetaFirstModeFirst (239784500047674155607/550507092643036572160:ℝ) ≤ (-247721730229918107488423/12500000000000000000000000:ℝ) := by
  have hlo : (3753628431589/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(239784500047674155607/550507092643036572160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(239784500047674155607/550507092643036572160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(239784500047674155607/550507092643036572160:ℝ)) ≤ (2389634574821/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(239784500047674155607/550507092643036572160:ℝ)) (by norm_num : 2*(239784500047674155607/550507092643036572160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(239784500047674155607/550507092643036572160:ℝ)) ≤ (7507259252815629853/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (239784500047674155607/550507092643036572160:ℝ) (3753628431589/500000000000:ℝ) (7507259252815629853/1000000000000000000:ℝ) (68268695707/50000000000000:ℝ) (13653771769/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0671).1 (thetaFirstMode_refined_node_0671).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0340 :
    (-60457519887145650152732491861/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/16:ℝ) ∧ thetaFirstModeFirst (7/16:ℝ) ≤ (-9673176792285514305249/500000000000000000000000:ℝ) := by
  have hlo : (1884071858131/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/16:ℝ)) ≤ (149929705873/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/16:ℝ)) (by norm_num : 2*(7/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/16:ℝ)) ≤ (471018114462675689/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/16:ℝ) (1884071858131/250000000000:ℝ) (471018114462675689/62500000000000000:ℝ) (5310345979/4000000000000:ℝ) (132758967949/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0672).1 (thetaFirstMode_refined_node_0672).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0341 :
    (-94392816279954414217718770903/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (225/512:ℝ) ∧ thetaFirstModeFirst (225/512:ℝ) ≤ (-943925578829165495396607/50000000000000000000000000:ℝ) := by
  have hlo : (7565783627557/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(225/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(225/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(225/512:ℝ)) ≤ (481652845281/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(225/512:ℝ)) (by norm_num : 2*(225/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(225/512:ℝ)) ≤ (1513157207164872633/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (225/512:ℝ) (7565783627557/1000000000000:ℝ) (1513157207164872633/200000000000000000:ℝ) (129025901651/100000000000000:ℝ) (64513106191/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0673).1 (thetaFirstMode_refined_node_0673).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0342 :
    (-94365371407892756058245556247/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (51969452684042517525/118253148433449738752:ℝ) ∧ thetaFirstModeFirst (51969452684042517525/118253148433449738752:ℝ) ≤ (-58978195672288704246609/3125000000000000000000000:ℝ) := by
  have hlo : (945766733489/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(51969452684042517525/118253148433449738752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51969452684042517525/118253148433449738752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(51969452684042517525/118253148433449738752:ℝ)) ≤ (481675142279/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(51969452684042517525/118253148433449738752:ℝ)) (by norm_num : 2*(51969452684042517525/118253148433449738752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(51969452684042517525/118253148433449738752:ℝ)) ≤ (1513227255257710447/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (51969452684042517525/118253148433449738752:ℝ) (945766733489/125000000000:ℝ) (1513227255257710447/200000000000000000:ℝ) (64491106081/50000000000000:ℝ) (64491261401/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0677).1 (thetaFirstMode_refined_node_0677).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0343 :
    (-115124357449800737986177245663/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (113/256:ℝ) ∧ thetaFirstModeFirst (113/256:ℝ) ≤ (-460496164887828189878933/25000000000000000000000000:ℝ) := by
  have hlo : (7595395267433/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(113/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(113/256:ℝ)) ≤ (604422476521/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(113/256:ℝ)) (by norm_num : 2*(113/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(113/256:ℝ)) ≤ (1898849421281037953/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (113/256:ℝ) (7595395267433/1000000000000:ℝ) (1898849421281037953/250000000000000000:ℝ) (62691815501/50000000000000:ℝ) (62691967071/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0678).1 (thetaFirstMode_refined_node_0678).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0344 :
    (-898514111413737042262114371101/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (227/512:ℝ) ∧ thetaFirstModeFirst (227/512:ℝ) ≤ (-179702326974830601052599/10000000000000000000000000:ℝ) := by
  have hlo : (7625122803991/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(227/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(227/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(227/512:ℝ)) ≤ (2427152476831/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(227/512:ℝ)) (by norm_num : 2*(227/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(227/512:ℝ)) ≤ (7625125231144931783/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (227/512:ℝ) (7625122803991/1000000000000:ℝ) (7625125231144931783/1000000000000000000:ℝ) (24366011489/20000000000000:ℝ) (121830353147/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0679).1 (thetaFirstMode_refined_node_0679).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0345 :
    (-17965054216304165945756025099/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (281388531776708917143/634640852921264412160:ℝ) ∧ thetaFirstModeFirst (281388531776708917143/634640852921264412160:ℝ) ≤ (-224562558723175546520451/12500000000000000000000000:ℝ) := by
  have hlo : (3812736340923/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(281388531776708917143/634640852921264412160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(281388531776708917143/634640852921264412160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(281388531776708917143/634640852921264412160:ℝ)) ≤ (485452769287/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(281388531776708917143/634640852921264412160:ℝ)) (by norm_num : 2*(281388531776708917143/634640852921264412160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(281388531776708917143/634640852921264412160:ℝ)) ≤ (1525095021822654191/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (281388531776708917143/634640852921264412160:ℝ) (3812736340923/500000000000:ℝ) (1525095021822654191/200000000000000000:ℝ) (60894418137/50000000000000:ℝ) (12178913189/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0683).1 (thetaFirstMode_refined_node_0683).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0346 :
    (-43823982347429205657163122317/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (57/128:ℝ) ∧ thetaFirstModeFirst (57/128:ℝ) ≤ (-876477222848403547529139/50000000000000000000000000:ℝ) := by
  have hlo : (7654966690837/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(57/128:ℝ)) ≤ (2436652083033/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(57/128:ℝ)) (by norm_num : 2*(57/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(57/128:ℝ)) ≤ (7654969127491891569/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (57/128:ℝ) (7654966690837/1000000000000:ℝ) (7654969127491891569/1000000000000000000:ℝ) (118363425447/100000000000000:ℝ) (5918185693/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0684).1 (thetaFirstMode_refined_node_0684).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0347 :
    (-427442611017920735033022586923/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (229/512:ℝ) ∧ thetaFirstModeFirst (229/512:ℝ) ≤ (-213720712388148706378597/12500000000000000000000000:ℝ) := by
  have hlo : (3842463691677/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(229/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(229/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(229/512:ℝ)) ≤ (1223094434821/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(229/512:ℝ)) (by norm_num : 2*(229/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(229/512:ℝ)) ≤ (3842464914772609853/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (229/512:ℝ) (3842463691677/500000000000:ℝ) (3842464914772609853/500000000000000000:ℝ) (57491001961/50000000000000:ℝ) (114982285191/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0685).1 (thetaFirstMode_refined_node_0685).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0348 :
    (-85463635028459610616058971189/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (304502779430409389841/680775093154008808960:ℝ) ∧ thetaFirstModeFirst (304502779430409389841/680775093154008808960:ℝ) ≤ (-427316989197575510334083/25000000000000000000000000:ℝ) := by
  have hlo : (3842638463101/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(304502779430409389841/680775093154008808960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(304502779430409389841/680775093154008808960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(304502779430409389841/680775093154008808960:ℝ)) ≤ (2446300132609/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(304502779430409389841/680775093154008808960:ℝ)) (by norm_num : 2*(304502779430409389841/680775093154008808960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(304502779430409389841/680775093154008808960:ℝ)) ≤ (7685279372503506137/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (304502779430409389841/680775093154008808960:ℝ) (3842638463101/500000000000:ℝ) (7685279372503506137/1000000000000000000:ℝ) (114943126783/100000000000000:ℝ) (11494340797/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0689).1 (thetaFirstMode_refined_node_0689).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0349 :
    (-416862310404649482099641688699/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (115/256:ℝ) ∧ thetaFirstModeFirst (115/256:ℝ) ≤ (-41686114955216448395989/2500000000000000000000000:ℝ) := by
  have hlo : (1543001067741/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(115/256:ℝ)) ≤ (1227881491089/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(115/256:ℝ)) (by norm_num : 2*(115/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(115/256:ℝ)) ≤ (3857503897234764777/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (115/256:ℝ) (1543001067741/200000000000:ℝ) (3857503897234764777/500000000000000000:ℝ) (27921021529/25000000000000:ℝ) (111684360387/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0690).1 (thetaFirstMode_refined_node_0690).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0350 :
    (-50811978552439047444801229351/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (231/512:ℝ) ∧ thetaFirstModeFirst (231/512:ℝ) ≤ (-812989385087173261617/50000000000000000000000:ℝ) := by
  have hlo : (3872600507923/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(231/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(231/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(231/512:ℝ)) ≤ (616343641683/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(231/512:ℝ)) (by norm_num : 2*(231/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(231/512:ℝ)) ≤ (1936300870305821019/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (231/512:ℝ) (3872600507923/500000000000:ℝ) (1936300870305821019/250000000000000000:ℝ) (216935979/200000000000:ℝ) (27117064229/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0691).1 (thetaFirstMode_refined_node_0691).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0351 :
    (-4063774053669450540689679429/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (329289608647804933359/729817555912400028160:ℝ) ∧ thetaFirstModeFirst (329289608647804933359/729817555912400028160:ℝ) ≤ (-50797033722446306240581/3125000000000000000000000:ℝ) := by
  have hlo : (968193781329/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(329289608647804933359/729817555912400028160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(329289608647804933359/729817555912400028160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(329289608647804933359/729817555912400028160:ℝ)) ≤ (61637143291/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(329289608647804933359/729817555912400028160:ℝ)) (by norm_num : 2*(329289608647804933359/729817555912400028160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(329289608647804933359/729817555912400028160:ℝ)) ≤ (193638817903002563/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (329289608647804933359/729817555912400028160:ℝ) (968193781329/125000000000:ℝ) (193638817903002563/25000000000000000:ℝ) (54215668789/50000000000000:ℝ) (21686320983/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0695).1 (thetaFirstMode_refined_node_0695).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0448 :
    (-59958354818369143003536440439/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (37/64:ℝ) ∧ thetaFirstModeFirst (37/64:ℝ) ≤ (-7494768086359679308581/3125000000000000000000000:ℝ) := by
  have hlo : (1247994841001/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(37/64:ℝ)) ≤ (3177993427539/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(37/64:ℝ)) (by norm_num : 2*(37/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(37/64:ℝ)) ≤ (9983961906002529627/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (37/64:ℝ) (1247994841001/125000000000:ℝ) (9983961906002529627/1000000000000000000:ℝ) (6159687581/50000000000000:ℝ) (6159707157/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0888).1 (thetaFirstMode_refined_node_0888).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0449 :
    (-115897275525153140937654391821/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (297/512:ℝ) ∧ thetaFirstModeFirst (297/512:ℝ) ≤ (-28974216979406574014411/12500000000000000000000000:ℝ) := by
  have hlo : (2505758709407/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(297/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(297/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(297/512:ℝ)) ≤ (3190431742133/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(297/512:ℝ)) (by norm_num : 2*(297/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(297/512:ℝ)) ≤ (10023038028062837869/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (297/512:ℝ) (2505758709407/250000000000:ℝ) (10023038028062837869/1000000000000000000:ℝ) (11858841173/100000000000000:ℝ) (11858879009/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0889).1 (thetaFirstMode_refined_node_0889).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0450 :
    (-5793086257565909963694339053/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3161110456538910701793/5449291680715587228160:ℝ) ∧ thetaFirstModeFirst (3161110456538910701793/5449291680715587228160:ℝ) ≤ (-57930658829709115090529/25000000000000000000000000:ℝ) := by
  have hlo : (10023386360753/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3161110456538910701793/5449291680715587228160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3161110456538910701793/5449291680715587228160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3161110456538910701793/5449291680715587228160:ℝ)) ≤ (1595271817721/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3161110456538910701793/5449291680715587228160:ℝ)) (by norm_num : 2*(3161110456538910701793/5449291680715587228160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3161110456538910701793/5449291680715587228160:ℝ)) ≤ (5011694775649569553/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3161110456538910701793/5449291680715587228160:ℝ) (10023386360753/1000000000000:ℝ) (5011694775649569553/500000000000000000:ℝ) (5927388593/50000000000000:ℝ) (1185481501/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0893).1 (thetaFirstMode_refined_node_0893).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0451 :
    (-55997696162222382523411024587/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (149/256:ℝ) ∧ thetaFirstModeFirst (149/256:ℝ) ≤ (-13999374631269726256047/6250000000000000000000000:ℝ) := by
  have hlo : (10062263886817/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(149/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(149/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(149/256:ℝ)) ≤ (3202918738913/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(149/256:ℝ)) (by norm_num : 2*(149/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(149/256:ℝ)) ≤ (10062267089737908409/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (149/256:ℝ) (10062263886817/1000000000000:ℝ) (10062267089737908409/1000000000000000000:ℝ) (1426722191/12500000000000:ℝ) (5706907043/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0894).1 (thetaFirstMode_refined_node_0894).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0452 :
    (-54104107146981444852184886289/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (299/512:ℝ) ∧ thetaFirstModeFirst (299/512:ℝ) ≤ (-5410391551783959098553/2500000000000000000000000:ℝ) := by
  have hlo : (10101646474163/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(299/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(299/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(299/512:ℝ)) ≤ (3215454608417/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(299/512:ℝ)) (by norm_num : 2*(299/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(299/512:ℝ)) ≤ (10101649689620588281/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (299/512:ℝ) (10101646474163/1000000000000:ℝ) (10101649689620588281/1000000000000000000:ℝ) (549186531/5000000000000:ℝ) (5491882969/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0895).1 (thetaFirstMode_refined_node_0895).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0453 :
    (-540874737123784668989891397/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3357929197679323400991/5749861108172310146560:ℝ) ∧ thetaFirstModeFirst (3357929197679323400991/5749861108172310146560:ℝ) ≤ (-3380455133232603520183/1562500000000000000000000:ℝ) := by
  have hlo : (10101998384783/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3357929197679323400991/5749861108172310146560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3357929197679323400991/5749861108172310146560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3357929197679323400991/5749861108172310146560:ℝ)) ≤ (321556662507/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3357929197679323400991/5749861108172310146560:ℝ)) (by norm_num : 2*(3357929197679323400991/5749861108172310146560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3357929197679323400991/5749861108172310146560:ℝ)) ≤ (1010200160035353651/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3357929197679323400991/5749861108172310146560:ℝ) (10101998384783/1000000000000:ℝ) (1010200160035353651/100000000000000000:ℝ) (343123801/3125000000000:ℝ) (548999847/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0899).1 (thetaFirstMode_refined_node_0899).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0454 :
    (-52266473073572570376767899757/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (75/128:ℝ) ∧ thetaFirstModeFirst (75/128:ℝ) ≤ (-26133143646159350949771/12500000000000000000000000:ℝ) := by
  have hlo : (5070591600299/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(75/128:ℝ)) ≤ (3228039541927/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(75/128:ℝ)) (by norm_num : 2*(75/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(75/128:ℝ)) ≤ (10141186428641069711/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (75/128:ℝ) (5070591600299/500000000000:ℝ) (10141186428641069711/1000000000000000000:ℝ) (5284128929/50000000000000:ℝ) (5284145987/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0900).1 (thetaFirstMode_refined_node_0900).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0455 :
    (-6310427667961600329424519173/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (301/512:ℝ) ∧ thetaFirstModeFirst (301/512:ℝ) ≤ (-807731860217241891219/400000000000000000000000:ℝ) := by
  have hlo : (2036174933881/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(301/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(301/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(301/512:ℝ)) ≤ (1620336865737/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(301/512:ℝ)) (by norm_num : 2*(301/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(301/512:ℝ)) ≤ (5090438955041299041/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (301/512:ℝ) (2036174933881/200000000000:ℝ) (5090438955041299041/500000000000000000:ℝ) (406677099/4000000000000:ℝ) (1270870053/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0901).1 (thetaFirstMode_refined_node_0901).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0456 :
    (-10093573080502129060895716469/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3565566396780466626009/6064838098423837058560:ℝ) ∧ thetaFirstModeFirst (3565566396780466626009/6064838098423837058560:ℝ) ≤ (-50467685376309742074681/25000000000000000000000000:ℝ) := by
  have hlo : (5090613491853/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(3565566396780466626009/6064838098423837058560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3565566396780466626009/6064838098423837058560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3565566396780466626009/6064838098423837058560:ℝ)) ≤ (1620392938311/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3565566396780466626009/6064838098423837058560:ℝ)) (by norm_num : 2*(3565566396780466626009/6064838098423837058560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3565566396780466626009/6064838098423837058560:ℝ)) ≤ (5090615112247269423/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3565566396780466626009/6064838098423837058560:ℝ) (5090613491853/500000000000:ℝ) (5090615112247269423/500000000000000000:ℝ) (10163434077/100000000000000:ℝ) (2032693403/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0905).1 (thetaFirstMode_refined_node_0905).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0457 :
    (-9522188322057800345059447/4882812500000000000000000000:ℝ) ≤ thetaFirstModeFirst (151/256:ℝ) ∧ thetaFirstModeFirst (151/256:ℝ) ≤ (-97506859363691937818883/50000000000000000000000000:ℝ) := by
  have hlo : (10220721486229/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(151/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(151/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(151/256:ℝ)) ≤ (40666967123/12500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(151/256:ℝ)) (by norm_num : 2*(151/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(151/256:ℝ)) ≤ (127759059244846939/12500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (151/256:ℝ) (10220721486229/1000000000000:ℝ) (127759059244846939/12500000000000000:ℝ) (9779318327/100000000000000:ℝ) (76401173/781250000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0906).1 (thetaFirstMode_refined_node_0906).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0458 :
    (-23537849286301647001621018799/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (303/512:ℝ) ∧ thetaFirstModeFirst (303/512:ℝ) ≤ (-2942220590874869405973/1562500000000000000000000:ℝ) := by
  have hlo : (2565181064771/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(303/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(303/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(303/512:ℝ)) ≤ (816522662641/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(303/512:ℝ)) (by norm_num : 2*(303/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(303/512:ℝ)) ≤ (2565181881294327113/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (303/512:ℝ) (2565181064771/250000000000:ℝ) (2565181881294327113/250000000000000000:ℝ) (1175627463/12500000000000:ℝ) (9405050423/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0907).1 (thetaFirstMode_refined_node_0907).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0459 :
    (-94122317810661185087674224321/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3784538847414433095207/6394810604163109788160:ℝ) ∧ thetaFirstModeFirst (3784538847414433095207/6394810604163109788160:ℝ) ≤ (-11765247457776949363529/6250000000000000000000000:ℝ) := by
  have hlo : (1282634624137/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(3784538847414433095207/6394810604163109788160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3784538847414433095207/6394810604163109788160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3784538847414433095207/6394810604163109788160:ℝ)) ≤ (3266202929311/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3784538847414433095207/6394810604163109788160:ℝ)) (by norm_num : 2*(3784538847414433095207/6394810604163109788160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3784538847414433095207/6394810604163109788160:ℝ)) ≤ (10261080259302932423/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3784538847414433095207/6394810604163109788160:ℝ) (1282634624137/125000000000:ℝ) (10261080259302932423/1000000000000000000:ℝ) (9401783617/100000000000000:ℝ) (9401814327/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0911).1 (thetaFirstMode_refined_node_0911).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0460 :
    (-90896811566478934093329200157/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19/32:ℝ) ∧ thetaFirstModeFirst (19/32:ℝ) ≤ (-18179296772907263258201/10000000000000000000000000:ℝ) := by
  have hlo : (2060176719673/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19/32:ℝ)) ≤ (3278873767939/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19/32:ℝ)) (by norm_num : 2*(19/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19/32:ℝ)) ≤ (10300886877240786827/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19/32:ℝ) (2060176719673/200000000000:ℝ) (10300886877240786827/1000000000000000000:ℝ) (9043631137/100000000000000:ℝ) (9043660791/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0912).1 (thetaFirstMode_refined_node_0912).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0461 :
    (-87740902870544773887710820443/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (305/512:ℝ) ∧ thetaFirstModeFirst (305/512:ℝ) ≤ (-87740585419504627457113/50000000000000000000000000:ℝ) := by
  have hlo : (10341200116857/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(305/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(305/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(305/512:ℝ)) ≤ (3291706917021/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(305/512:ℝ)) (by norm_num : 2*(305/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(305/512:ℝ)) ≤ (10341203408564754453/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (305/512:ℝ) (10341200116857/1000000000000:ℝ) (10341203408564754453/1000000000000000000:ℝ) (8694762209/100000000000000:ℝ) (8694790831/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0913).1 (thetaFirstMode_refined_node_0913).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0462 :
    (-8771373944516178740516536187/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (803076872185116228645/1348077287675556311552:ℝ) ∧ thetaFirstModeFirst (803076872185116228645/1348077287675556311552:ℝ) ≤ (-10964177760463465764677/6250000000000000000000000:ℝ) := by
  have hlo : (10341553286463/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(803076872185116228645/1348077287675556311552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(803076872185116228645/1348077287675556311552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(803076872185116228645/1348077287675556311552:ℝ)) ≤ (1645909667211/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(803076872185116228645/1348077287675556311552:ℝ)) (by norm_num : 2*(803076872185116228645/1348077287675556311552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(803076872185116228645/1348077287675556311552:ℝ)) ≤ (5170778289142407123/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (803076872185116228645/1348077287675556311552:ℝ) (10341553286463/1000000000000:ℝ) (5170778289142407123/500000000000000000:ℝ) (1086470779/12500000000000:ℝ) (1738358969/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0917).1 (thetaFirstMode_refined_node_0917).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0463 :
    (-5292573140131928158266302753/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (153/256:ℝ) ∧ thetaFirstModeFirst (153/256:ℝ) ≤ (-4234043138757324483781/2500000000000000000000000:ℝ) := by
  have hlo : (519083721487/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(153/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(153/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(153/256:ℝ)) ≤ (3304590293629/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(153/256:ℝ)) (by norm_num : 2*(153/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(153/256:ℝ)) ≤ (10381677734332810997/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (153/256:ℝ) (519083721487/50000000000:ℝ) (10381677734332810997/1000000000000000000:ℝ) (8358032363/100000000000000:ℝ) (522378749/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0918).1 (thetaFirstMode_refined_node_0918).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0464 :
    (-81715160510678331988221327041/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (307/512:ℝ) ∧ thetaFirstModeFirst (307/512:ℝ) ≤ (-25535894612032480833/15625000000000000000000:ℝ) := by
  have hlo : (2084461430921/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(307/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(307/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(307/512:ℝ)) ≤ (3317524094347/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(307/512:ℝ)) (by norm_num : 2*(307/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(307/512:ℝ)) ≤ (10422310472131874771/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (307/512:ℝ) (2084461430921/200000000000:ℝ) (10422310472131874771/1000000000000000000:ℝ) (12551673/156250000000:ℝ) (8033097371/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0919).1 (thetaFirstMode_refined_node_0919).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0465 :
    (-20422450499662123467388661867/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4258662473983944316743/7102193807453257500160:ℝ) ∧ thetaFirstModeFirst (4258662473983944316743/7102193807453257500160:ℝ) ≤ (-10211188040841266756639/6250000000000000000000000:ℝ) := by
  have hlo : (1302832596943/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(4258662473983944316743/7102193807453257500160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4258662473983944316743/7102193807453257500160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4258662473983944316743/7102193807453257500160:ℝ)) ≤ (3317636655411/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4258662473983944316743/7102193807453257500160:ℝ)) (by norm_num : 2*(4258662473983944316743/7102193807453257500160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4258662473983944316743/7102193807453257500160:ℝ)) ≤ (10422664093182609723/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4258662473983944316743/7102193807453257500160:ℝ) (1302832596943/125000000000:ℝ) (10422664093182609723/1000000000000000000:ℝ) (8030298673/100000000000000:ℝ) (2007581329/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0923).1 (thetaFirstMode_refined_node_0923).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0466 :
    (-78840467632137500341712385897/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (77/128:ℝ) ∧ thetaFirstModeFirst (77/128:ℝ) ≤ (-3942008966657086703381/2500000000000000000000000:ℝ) := by
  have hlo : (5231549455729/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(77/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(77/128:ℝ)) ≤ (3330508516529/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(77/128:ℝ)) (by norm_num : 2*(77/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(77/128:ℝ)) ≤ (10463102241967890697/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (77/128:ℝ) (5231549455729/500000000000:ℝ) (10463102241967890697/1000000000000000000:ℝ) (771951589/10000000000000:ℝ) (7719541601/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0924).1 (thetaFirstMode_refined_node_0924).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0467 :
    (-7605473225482518240826420061/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (309/512:ℝ) ∧ thetaFirstModeFirst (309/512:ℝ) ≤ (-3802722657758633698493/2500000000000000000000000:ℝ) := by
  have hlo : (5252025161367/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(309/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(309/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(309/512:ℝ)) ≤ (3343543758303/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(309/512:ℝ)) (by norm_num : 2*(309/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(309/512:ℝ)) ≤ (10504053666278396679/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (309/512:ℝ) (5252025161367/500000000000:ℝ) (10504053666278396679/1000000000000000000:ℝ) (741701579/10000000000000:ℝ) (741704059/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0925).1 (thetaFirstMode_refined_node_0925).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0468 :
    (-15206214611497358587433543671/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4514955175067537709441/7480881854937014095360:ℝ) ∧ thetaFirstModeFirst (4514955175067537709441/7480881854937014095360:ℝ) ≤ (-38015397014284365032217/25000000000000000000000000:ℝ) := by
  have hlo : (10504404410607/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(4514955175067537709441/7480881854937014095360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4514955175067537709441/7480881854937014095360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4514955175067537709441/7480881854937014095360:ℝ)) ≤ (3343656467997/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4514955175067537709441/7480881854937014095360:ℝ)) (by norm_num : 2*(4514955175067537709441/7480881854937014095360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4514955175067537709441/7480881854937014095360:ℝ)) ≤ (10504407754264099221/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4514955175067537709441/7480881854937014095360:ℝ) (10504404410607/1000000000000:ℝ) (10504407754264099221/1000000000000000000:ℝ) (3707226231/50000000000000:ℝ) (1482895451/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0929).1 (thetaFirstMode_refined_node_0929).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0469 :
    (-73355641290325420418955892949/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (155/256:ℝ) ∧ thetaFirstModeFirst (155/256:ℝ) ≤ (-14671074226759396102393/10000000000000000000000000:ℝ) := by
  have hlo : (10545162013301/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(155/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(155/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(155/256:ℝ)) ≤ (3356630018571/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(155/256:ℝ)) (by norm_num : 2*(155/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(155/256:ℝ)) ≤ (10545165369932523603/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (155/256:ℝ) (10545162013301/1000000000000:ℝ) (10545165369932523603/1000000000000000000:ℝ) (1425045493/20000000000000:ℝ) (7125251383/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0930).1 (thetaFirstMode_refined_node_0930).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0470 :
    (-17685231838823176649492941933/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (311/512:ℝ) ∧ thetaFirstModeFirst (311/512:ℝ) ≤ (-17685166475982467418957/12500000000000000000000000:ℝ) := by
  have hlo : (2646608652619/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(311/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(311/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(311/512:ℝ)) ≤ (1684883748507/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(311/512:ℝ)) (by norm_num : 2*(311/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(311/512:ℝ)) ≤ (5293218990123351651/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (311/512:ℝ) (2646608652619/250000000000:ℝ) (5293218990123351651/500000000000000000:ℝ) (6843816903/100000000000000:ℝ) (3421919983/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0931).1 (thetaFirstMode_refined_node_0931).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0471 :
    (-1767971676692178932262396061/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4784867650250851000959/7877121216105401397760:ℝ) ∧ thetaFirstModeFirst (4784867650250851000959/7877121216105401397760:ℝ) ≤ (-35359302843865231456749/25000000000000000000000000:ℝ) := by
  have hlo : (10586789180749/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(4784867650250851000959/7877121216105401397760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4784867650250851000959/7877121216105401397760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4784867650250851000959/7877121216105401397760:ℝ)) ≤ (168494018013/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4784867650250851000959/7877121216105401397760:ℝ)) (by norm_num : 2*(4784867650250851000959/7877121216105401397760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4784867650250851000959/7877121216105401397760:ℝ)) ≤ (529339627531514709/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4784867650250851000959/7877121216105401397760:ℝ) (10586789180749/1000000000000:ℝ) (529339627531514709/50000000000000000:ℝ) (3420724001/50000000000000:ℝ) (3420735529/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0935).1 (thetaFirstMode_refined_node_0935).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0472 :
    (-68208368381710565753727253453/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (39/64:ℝ) ∧ thetaFirstModeFirst (39/64:ℝ) ≤ (-34104057697683105317499/25000000000000000000000000:ℝ) := by
  have hlo : (10627868744029/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(39/64:ℝ)) ≤ (3382956394093/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(39/64:ℝ)) (by norm_num : 2*(39/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(39/64:ℝ)) ≤ (10627872126987810149/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (39/64:ℝ) (10627868744029/1000000000000:ℝ) (10627872126987810149/1000000000000000000:ℝ) (3286229431/50000000000000:ℝ) (6572481097/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0936).1 (thetaFirstMode_refined_node_0936).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0473 :
    (-2054868346509062787964488819/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (313/512:ℝ) ∧ thetaFirstModeFirst (313/512:ℝ) ≤ (-4109721395284074488977/3125000000000000000000000:ℝ) := by
  have hlo : (2667366261549/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(313/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(313/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(313/512:ℝ)) ≤ (212262306941/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(313/512:ℝ)) (by norm_num : 2*(313/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(313/512:ℝ)) ≤ (666841777649697013/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (313/512:ℝ) (2667366261549/250000000000:ℝ) (666841777649697013/62500000000000000:ℝ) (1577709173/25000000000000:ℝ) (3155429063/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0937).1 (thetaFirstMode_refined_node_0937).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0474 :
    (-2629409213222150471003489169/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5069029048681798692657/8291604583475060892160:ℝ) ∧ thetaFirstModeFirst (5069029048681798692657/8291604583475060892160:ℝ) ≤ (-16433746409715476156097/12500000000000000000000000:ℝ) := by
  have hlo : (5334910057103/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5069029048681798692657/8291604583475060892160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5069029048681798692657/8291604583475060892160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5069029048681798692657/8291604583475060892160:ℝ)) ≤ (3396309932737/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5069029048681798692657/8291604583475060892160:ℝ)) (by norm_num : 2*(5069029048681798692657/8291604583475060892160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5069029048681798692657/8291604583475060892160:ℝ)) ≤ (10669823510517030041/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5069029048681798692657/8291604583475060892160:ℝ) (5334910057103/500000000000:ℝ) (10669823510517030041/1000000000000000000:ℝ) (3154324399/50000000000000:ℝ) (252346809/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0941).1 (thetaFirstMode_refined_node_0941).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0475 :
    (-3169052523823218126140532381/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (157/256:ℝ) ∧ thetaFirstModeFirst (157/256:ℝ) ≤ (-15845203427884370746283/12500000000000000000000000:ℝ) := by
  have hlo : (5355612075843/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(157/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(157/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(157/256:ℝ)) ≤ (3409489249937/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(157/256:ℝ)) (by norm_num : 2*(157/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(157/256:ℝ)) ≤ (10711227561177329641/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (157/256:ℝ) (5355612075843/500000000000:ℝ) (10711227561177329641/1000000000000000000:ℝ) (3029321081/50000000000000:ℝ) (302933141/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0942).1 (thetaFirstMode_refined_node_0942).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0476 :
    (-30541034676158972132213766669/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (315/512:ℝ) ∧ thetaFirstModeFirst (315/512:ℝ) ≤ (-15270460090085434897621/12500000000000000000000000:ℝ) := by
  have hlo : (5376573348847/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(315/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(315/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(315/512:ℝ)) ≤ (1711416806781/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(315/512:ℝ)) (by norm_num : 2*(315/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(315/512:ℝ)) ≤ (5376575060265542133/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (315/512:ℝ) (5376573348847/500000000000:ℝ) (5376575060265542133/500000000000000000:ℝ) (2907787643/50000000000000:ℝ) (5815595193/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0943).1 (thetaFirstMode_refined_node_0943).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0477 :
    (-190821642355199244379493817/156250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1073618653626882244035/1745009456680404157952:ℝ) ∧ thetaFirstModeFirst (1073618653626882244035/1745009456680404157952:ℝ) ≤ (-15265674158597593363003/12500000000000000000000000:ℝ) := by
  have hlo : (10753502278653/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1073618653626882244035/1745009456680404157952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1073618653626882244035/1745009456680404157952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1073618653626882244035/1745009456680404157952:ℝ)) ≤ (85573669963/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1073618653626882244035/1745009456680404157952:ℝ)) (by norm_num : 2*(1073618653626882244035/1745009456680404157952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1073618653626882244035/1745009456680404157952:ℝ)) ≤ (268837642540071059/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1073618653626882244035/1745009456680404157952:ℝ) (10753502278653/1000000000000:ℝ) (268837642540071059/25000000000000000:ℝ) (1453388951/25000000000000:ℝ) (726696963/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0947).1 (thetaFirstMode_refined_node_0947).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0478 :
    (-29428398900700801003275121519/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (79/128:ℝ) ∧ thetaFirstModeFirst (79/128:ℝ) ≤ (-2942828818775256877887/2500000000000000000000000:ℝ) := by
  have hlo : (2698808330977/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(79/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(79/128:ℝ)) ≤ (3436230205549/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(79/128:ℝ)) (by norm_num : 2*(79/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(79/128:ℝ)) ≤ (10795236760141299557/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (79/128:ℝ) (2698808330977/250000000000:ℝ) (10795236760141299557/1000000000000000000:ℝ) (1116268831/20000000000000:ℝ) (2790681667/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0948).1 (thetaFirstMode_refined_node_0948).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0479 :
    (-7087904091514345268270176911/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (317/512:ℝ) ∧ thetaFirstModeFirst (317/512:ℝ) ≤ (-56703018631762541438073/50000000000000000000000000:ℝ) := by
  have hlo : (10837484672519/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(317/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(317/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(317/512:ℝ)) ≤ (1724839615157/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(317/512:ℝ)) (by norm_num : 2*(317/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(317/512:ℝ)) ≤ (5418744061099925101/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (317/512:ℝ) (10837484672519/1000000000000:ℝ) (5418744061099925101/500000000000000000:ℝ) (5355664767/100000000000000:ℝ) (1338920811/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0949).1 (thetaFirstMode_refined_node_0949).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

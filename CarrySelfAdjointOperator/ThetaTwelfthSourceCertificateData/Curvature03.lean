import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_096 :
    ∀ u ∈ Set.Icc (3/16:ℝ) (97/512:ℝ), (79542980257604461978243/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (917775946973/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(97/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/16:ℝ) (97/512:ℝ) (917775946973/200000000000:ℝ) (1117412285759/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0289).1
  intro u hu
  exact (show (79542980257604461978243/62500000000000000000000:ℝ) ≤ (1/4-6*(917775946973/200000000000:ℝ)+4*(917775946973/200000000000:ℝ)^2)*(1117412285759/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_097 :
    ∀ u ∈ Set.Icc (97/512:ℝ) (49/256:ℝ), (631701378085954983459/500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2303420051167/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (97/512:ℝ) (49/256:ℝ) (2303420051167/500000000000:ℝ) (439437846891/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0294).1
  intro u hu
  exact (show (631701378085954983459/500000000000000000000:ℝ) ≤ (1/4-6*(2303420051167/500000000000:ℝ)+4*(2303420051167/500000000000:ℝ)^2)*(439437846891/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_098 :
    ∀ u ∈ Set.Icc (49/256:ℝ) (99/512:ℝ), (250816855496097153114469/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2312435382347/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(99/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (49/256:ℝ) (99/512:ℝ) (2312435382347/500000000000:ℝ) (540008961651/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0295).1
  intro u hu
  exact (show (250816855496097153114469/200000000000000000000000:ℝ) ≤ (1/4-6*(2312435382347/500000000000:ℝ)+4*(2312435382347/500000000000:ℝ)^2)*(540008961651/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_099 :
    ∀ u ∈ Set.Icc (99/512:ℝ) (25/128:ℝ), (311183437377524429533721/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4642971997071/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (99/512:ℝ) (25/128:ℝ) (4642971997071/1000000000000:ℝ) (1061680426651/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0300).1
  intro u hu
  exact (show (311183437377524429533721/250000000000000000000000:ℝ) ≤ (1/4-6*(4642971997071/1000000000000:ℝ)+4*(4642971997071/1000000000000:ℝ)^2)*(1061680426651/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_100 :
    ∀ u ∈ Set.Icc (25/128:ℝ) (101/512:ℝ), (1235352673532054159865149/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4661144075669/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(101/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (25/128:ℝ) (101/512:ℝ) (4661144075669/1000000000000:ℝ) (2087160687639/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0301).1
  intro u hu
  exact (show (1235352673532054159865149/1000000000000000000000000:ℝ) ≤ (1/4-6*(4661144075669/1000000000000:ℝ)+4*(4661144075669/1000000000000:ℝ)^2)*(2087160687639/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_101 :
    ∀ u ∈ Set.Icc (101/512:ℝ) (51/256:ℝ), (1225942550278573731374667/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4679387277771/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (101/512:ℝ) (51/256:ℝ) (4679387277771/1000000000000:ℝ) (2051431771071/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0306).1
  intro u hu
  exact (show (1225942550278573731374667/1000000000000000000000000:ℝ) ≤ (1/4-6*(4679387277771/1000000000000:ℝ)+4*(4679387277771/1000000000000:ℝ)^2)*(2051431771071/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_102 :
    ∀ u ∈ Set.Icc (51/256:ℝ) (103/512:ℝ), (608252439780117264523113/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1174425470437/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(103/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (51/256:ℝ) (103/512:ℝ) (1174425470437/250000000000:ℝ) (504042628491/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0307).1
  intro u hu
  exact (show (608252439780117264523113/500000000000000000000000:ℝ) ≤ (1/4-6*(1174425470437/250000000000:ℝ)+4*(1174425470437/250000000000:ℝ)^2)*(504042628491/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_103 :
    ∀ u ∈ Set.Icc (103/512:ℝ) (13/64:ℝ), (603520579949104592553451/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4716088167057/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (103/512:ℝ) (13/64:ℝ) (4716088167057/1000000000000:ℝ) (79254932647/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0312).1
  intro u hu
  exact (show (603520579949104592553451/500000000000000000000000:ℝ) ≤ (1/4-6*(4716088167057/1000000000000:ℝ)+4*(4716088167057/1000000000000:ℝ)^2)*(79254932647/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_104 :
    ∀ u ∈ Set.Icc (13/64:ℝ) (105/512:ℝ), (1197552888164553565647723/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4734546414253/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(105/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (13/64:ℝ) (105/512:ℝ) (4734546414253/1000000000000:ℝ) (194703656763/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0313).1
  intro u hu
  exact (show (1197552888164553565647723/1000000000000000000000000:ℝ) ≤ (1/4-6*(4734546414253/1000000000000:ℝ)+4*(4734546414253/1000000000000:ℝ)^2)*(194703656763/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_105 :
    ∀ u ∈ Set.Icc (105/512:ℝ) (53/256:ℝ), (237608311840065476240513/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2376538452493/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (105/512:ℝ) (53/256:ℝ) (2376538452493/500000000000:ℝ) (23914458111/1250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0318).1
  intro u hu
  exact (show (237608311840065476240513/200000000000000000000000:ℝ) ≤ (1/4-6*(2376538452493/500000000000:ℝ)+4*(2376538452493/500000000000:ℝ)^2)*(23914458111/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_106 :
    ∀ u ∈ Set.Icc (53/256:ℝ) (107/512:ℝ), (4714034661840215647083/4000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4771679922009/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(107/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (53/256:ℝ) (107/512:ℝ) (4771679922009/1000000000000:ℝ) (1879729931687/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0319).1
  intro u hu
  exact (show (4714034661840215647083/4000000000000000000000:ℝ) ≤ (1/4-6*(4771679922009/1000000000000:ℝ)+4*(4771679922009/1000000000000:ℝ)^2)*(1879729931687/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_107 :
    ∀ u ∈ Set.Icc (107/512:ℝ) (27/128:ℝ), (73059731039782495279543/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4790355749181/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (107/512:ℝ) (27/128:ℝ) (4790355749181/1000000000000:ℝ) (1846752779581/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0324).1
  intro u hu
  exact (show (73059731039782495279543/62500000000000000000000:ℝ) ≤ (1/4-6*(4790355749181/1000000000000:ℝ)+4*(4790355749181/1000000000000:ℝ)^2)*(1846752779581/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_108 :
    ∀ u ∈ Set.Icc (27/128:ℝ) (109/512:ℝ), (289846034826571327379441/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (192364186859/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(109/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (27/128:ℝ) (109/512:ℝ) (192364186859/40000000000:ℝ) (1814221548443/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0325).1
  intro u hu
  exact (show (289846034826571327379441/250000000000000000000000:ℝ) ≤ (1/4-6*(192364186859/40000000000:ℝ)+4*(192364186859/40000000000:ℝ)^2)*(1814221548443/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_109 :
    ∀ u ∈ Set.Icc (109/512:ℝ) (55/256:ℝ), (574897738276723779980301/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9429544873/1953125000:ℝ) ≤ Real.pi*Real.exp (2*(55/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (109/512:ℝ) (55/256:ℝ) (9429544873/1953125000:ℝ) (89106629353/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0330).1
  intro u hu
  exact (show (574897738276723779980301/500000000000000000000000:ℝ) ≤ (1/4-6*(9429544873/1953125000:ℝ)+4*(9429544873/1953125000:ℝ)^2)*(89106629353/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_110 :
    ∀ u ∈ Set.Icc (55/256:ℝ) (111/512:ℝ), (142523898450206933899489/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4846822946889/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (55/256:ℝ) (111/512:ℝ) (4846822946889/1000000000000:ℝ) (1750482237681/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0331).1
  intro u hu
  exact (show (142523898450206933899489/125000000000000000000000:ℝ) ≤ (1/4-6*(4846822946889/1000000000000:ℝ)+4*(4846822946889/1000000000000:ℝ)^2)*(1750482237681/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_111 :
    ∀ u ∈ Set.Icc (111/512:ℝ) (7/32:ℝ), (282643186868228365228189/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2432896437773/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (111/512:ℝ) (7/32:ℝ) (2432896437773/500000000000:ℝ) (429816709153/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0336).1
  intro u hu
  exact (show (282643186868228365228189/250000000000000000000000:ℝ) ≤ (1/4-6*(2432896437773/500000000000:ℝ)+4*(2432896437773/500000000000:ℝ)^2)*(429816709153/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_112 :
    ∀ u ∈ Set.Icc (7/32:ℝ) (113/512:ℝ), (70058851663064255029919/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1221209262601/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(113/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/32:ℝ) (113/512:ℝ) (1221209262601/250000000000:ℝ) (1688482714757/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0337).1
  intro u hu
  exact (show (70058851663064255029919/62500000000000000000000:ℝ) ≤ (1/4-6*(1221209262601/250000000000:ℝ)+4*(1221209262601/250000000000:ℝ)^2)*(1688482714757/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_113 :
    ∀ u ∈ Set.Icc (113/512:ℝ) (57/256:ℝ), (277824822626642708938421/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (980791152411/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (113/512:ℝ) (57/256:ℝ) (980791152411/200000000000:ℝ) (829063099083/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0342).1
  intro u hu
  exact (show (277824822626642708938421/250000000000000000000000:ℝ) ≤ (1/4-6*(980791152411/200000000000:ℝ)+4*(980791152411/200000000000:ℝ)^2)*(829063099083/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_114 :
    ∀ u ∈ Set.Icc (57/256:ℝ) (115/512:ℝ), (44065887975287776582341/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1230787325557/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (57/256:ℝ) (115/512:ℝ) (1230787325557/250000000000:ℝ) (1628193608631/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0343).1
  intro u hu
  exact (show (44065887975287776582341/40000000000000000000000:ℝ) ≤ (1/4-6*(1230787325557/250000000000:ℝ)+4*(1230787325557/250000000000:ℝ)^2)*(1628193608631/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_115 :
    ∀ u ∈ Set.Icc (115/512:ℝ) (29/128:ℝ), (545993403897977599816047/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4942417963793/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (115/512:ℝ) (29/128:ℝ) (4942417963793/1000000000000:ℝ) (399670316053/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0348).1
  intro u hu
  exact (show (545993403897977599816047/500000000000000000000000:ℝ) ≤ (1/4-6*(4942417963793/1000000000000:ℝ)+4*(4942417963793/1000000000000:ℝ)^2)*(399670316053/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_116 :
    ∀ u ∈ Set.Icc (29/128:ℝ) (117/512:ℝ), (541159782154773469745817/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (77527531887/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(117/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(117/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (29/128:ℝ) (117/512:ℝ) (77527531887/15625000000:ℝ) (12262386561/781250000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0349).1
  intro u hu
  exact (show (541159782154773469745817/500000000000000000000000:ℝ) ≤ (1/4-6*(77527531887/15625000000:ℝ)+4*(77527531887/15625000000:ℝ)^2)*(12262386561/781250000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_117 :
    ∀ u ∈ Set.Icc (117/512:ℝ) (59/256:ℝ), (536323455561854795423377/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2490590914159/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (117/512:ℝ) (59/256:ℝ) (2490590914159/500000000000:ℝ) (770451283849/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0354).1
  intro u hu
  exact (show (536323455561854795423377/500000000000000000000000:ℝ) ≤ (1/4-6*(2490590914159/500000000000:ℝ)+4*(2490590914159/500000000000:ℝ)^2)*(770451283849/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_118 :
    ∀ u ∈ Set.Icc (59/256:ℝ) (119/512:ℝ), (1062970283742563086707513/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5000677622769/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(119/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(119/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (59/256:ℝ) (119/512:ℝ) (5000677622769/1000000000000:ℝ) (189078604763/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0355).1
  intro u hu
  exact (show (1062970283742563086707513/1000000000000000000000000:ℝ) ≤ (1/4-6*(5000677622769/1000000000000:ℝ)+4*(5000677622769/1000000000000:ℝ)^2)*(189078604763/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_119 :
    ∀ u ∈ Set.Icc (119/512:ℝ) (15/64:ℝ), (1053291110608192099983023/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5020249721601/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (119/512:ℝ) (15/64:ℝ) (5020249721601/1000000000000:ℝ) (1484760599721/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0360).1
  intro u hu
  exact (show (1053291110608192099983023/1000000000000000000000000:ℝ) ≤ (1/4-6*(5020249721601/1000000000000:ℝ)+4*(5020249721601/1000000000000:ℝ)^2)*(1484760599721/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_120 :
    ∀ u ∈ Set.Icc (15/64:ℝ) (121/512:ℝ), (521805406388959194943977/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2519949211731/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(121/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (15/64:ℝ) (121/512:ℝ) (2519949211731/500000000000:ℝ) (728647080143/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0361).1
  intro u hu
  exact (show (521805406388959194943977/500000000000000000000000:ℝ) ≤ (1/4-6*(2519949211731/500000000000:ℝ)+4*(2519949211731/500000000000:ℝ)^2)*(728647080143/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_121 :
    ∀ u ∈ Set.Icc (121/512:ℝ) (61/256:ℝ), (516965401780457664772741/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (632453003521/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (121/512:ℝ) (61/256:ℝ) (632453003521/125000000000:ℝ) (1430225827093/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0366).1
  intro u hu
  exact (show (516965401780457664772741/500000000000000000000000:ℝ) ≤ (1/4-6*(632453003521/125000000000:ℝ)+4*(632453003521/125000000000:ℝ)^2)*(1430225827093/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_122 :
    ∀ u ∈ Set.Icc (61/256:ℝ) (123/512:ℝ), (40970099528116381110747/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1269856709177/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (61/256:ℝ) (123/512:ℝ) (1269856709177/250000000000:ℝ) (280710381513/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0367).1
  intro u hu
  exact (show (40970099528116381110747/40000000000000000000000:ℝ) ≤ (1/4-6*(1269856709177/250000000000:ℝ)+4*(1269856709177/250000000000:ℝ)^2)*(280710381513/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_123 :
    ∀ u ∈ Set.Icc (123/512:ℝ) (31/128:ℝ), (50728863175888107675219/50000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5099307151249/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (123/512:ℝ) (31/128:ℝ) (5099307151249/1000000000000:ℝ) (275453741949/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0372).1
  intro u hu
  exact (show (50728863175888107675219/50000000000000000000000:ℝ) ≤ (1/4-6*(5099307151249/1000000000000:ℝ)+4*(5099307151249/1000000000000:ℝ)^2)*(275453741949/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_124 :
    ∀ u ∈ Set.Icc (31/128:ℝ) (125/512:ℝ), (1004906517591051750832173/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5119265275141/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(125/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (31/128:ℝ) (125/512:ℝ) (5119265275141/1000000000000:ℝ) (1351372542879/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0373).1
  intro u hu
  exact (show (1004906517591051750832173/1000000000000000000000000:ℝ) ≤ (1/4-6*(5119265275141/1000000000000:ℝ)+4*(5119265275141/1000000000000:ℝ)^2)*(1351372542879/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_125 :
    ∀ u ∈ Set.Icc (125/512:ℝ) (63/256:ℝ), (248810407355786208215281/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2569650756461/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (125/512:ℝ) (63/256:ℝ) (2569650756461/500000000000:ℝ) (331464929477/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0378).1
  intro u hu
  exact (show (248810407355786208215281/250000000000000000000000:ℝ) ≤ (1/4-6*(2569650756461/500000000000:ℝ)+4*(2569650756461/500000000000:ℝ)^2)*(331464929477/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_126 :
    ∀ u ∈ Set.Icc (63/256:ℝ) (127/512:ℝ), (492791984305824218247837/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (64492702129/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(127/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(127/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (63/256:ℝ) (127/512:ℝ) (64492702129/12500000000:ℝ) (162590818501/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0379).1
  intro u hu
  exact (show (492791984305824218247837/500000000000000000000000:ℝ) ≤ (1/4-6*(64492702129/12500000000:ℝ)+4*(64492702129/12500000000:ℝ)^2)*(162590818501/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_127 :
    ∀ u ∈ Set.Icc (127/512:ℝ) (1/4:ℝ), (975934895029726802729679/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5179609554261/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/4:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/4:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (127/512:ℝ) (1/4:ℝ) (5179609554261/1000000000000:ℝ) (159496168639/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0384).1
  intro u hu
  exact (show (975934895029726802729679/1000000000000000000000000:ℝ) ≤ (1/4-6*(5179609554261/1000000000000:ℝ)+4*(5179609554261/1000000000000:ℝ)^2)*(159496168639/12500000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

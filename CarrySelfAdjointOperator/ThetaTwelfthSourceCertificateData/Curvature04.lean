import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_128 :
    ∀ u ∈ Set.Icc (1/4:ℝ) (129/512:ℝ), (966295758513919120153063/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (649985246609/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(129/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(129/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/4:ℝ) (129/512:ℝ) (649985246609/125000000000:ℝ) (1251584440439/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0385).1
  intro u hu
  exact (show (966295758513919120153063/1000000000000000000000000:ℝ) ≤ (1/4-6*(649985246609/125000000000:ℝ)+4*(649985246609/125000000000:ℝ)^2)*(1251584440439/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_129 :
    ∀ u ∈ Set.Icc (129/512:ℝ) (65/256:ℝ), (478333949264452833596727/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2610116867743/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(65/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (129/512:ℝ) (65/256:ℝ) (2610116867743/500000000000:ℝ) (1227568144983/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0390).1
  intro u hu
  exact (show (478333949264452833596727/500000000000000000000000:ℝ) ≤ (1/4-6*(2610116867743/500000000000:ℝ)+4*(2610116867743/500000000000:ℝ)^2)*(1227568144983/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_130 :
    ∀ u ∈ Set.Icc (65/256:ℝ) (131/512:ℝ), (947052643874298212119509/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5240665152647/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(131/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(131/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (65/256:ℝ) (131/512:ℝ) (5240665152647/1000000000000:ℝ) (37622399689/3125000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0391).1
  intro u hu
  exact (show (947052643874298212119509/1000000000000000000000000:ℝ) ≤ (1/4-6*(5240665152647/1000000000000:ℝ)+4*(5240665152647/1000000000000:ℝ)^2)*(37622399689/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_131 :
    ∀ u ∈ Set.Icc (131/512:ℝ) (33/128:ℝ), (93745131236830700098271/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2630588268057/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (131/512:ℝ) (33/128:ℝ) (2630588268057/500000000000:ℝ) (36894584617/3125000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0396).1
  intro u hu
  exact (show (93745131236830700098271/100000000000000000000000:ℝ) ≤ (1/4-6*(2630588268057/500000000000:ℝ)+4*(2630588268057/500000000000:ℝ)^2)*(36894584617/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_132 :
    ∀ u ∈ Set.Icc (33/128:ℝ) (133/512:ℝ), (927865210544466697500661/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2640884099433/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(133/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(133/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (33/128:ℝ) (133/512:ℝ) (2640884099433/500000000000:ℝ) (115769423549/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0397).1
  intro u hu
  exact (show (927865210544466697500661/1000000000000000000000000:ℝ) ≤ (1/4-6*(2640884099433/500000000000:ℝ)+4*(2640884099433/500000000000:ℝ)^2)*(115769423549/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_133 :
    ∀ u ∈ Set.Icc (133/512:ℝ) (67/256:ℝ), (918295633360136582510243/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5302440455107/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (133/512:ℝ) (67/256:ℝ) (5302440455107/1000000000000:ℝ) (567557858261/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0402).1
  intro u hu
  exact (show (918295633360136582510243/1000000000000000000000000:ℝ) ≤ (1/4-6*(5302440455107/1000000000000:ℝ)+4*(5302440455107/1000000000000:ℝ)^2)*(567557858261/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_134 :
    ∀ u ∈ Set.Icc (67/256:ℝ) (135/512:ℝ), (454371931943431231700863/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (332699601267/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(135/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(135/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (67/256:ℝ) (135/512:ℝ) (332699601267/62500000000:ℝ) (69555468773/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0403).1
  intro u hu
  exact (show (454371931943431231700863/500000000000000000000000:ℝ) ≤ (1/4-6*(332699601267/62500000000:ℝ)+4*(332699601267/62500000000:ℝ)^2)*(69555468773/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_135 :
    ∀ u ∈ Set.Icc (135/512:ℝ) (17/64:ℝ), (179842234606979033115729/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1336007002757/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (135/512:ℝ) (17/64:ℝ) (1336007002757/250000000000:ℝ) (545502971679/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0408).1
  intro u hu
  exact (show (179842234606979033115729/200000000000000000000000:ℝ) ≤ (1/4-6*(1336007002757/250000000000:ℝ)+4*(1336007002757/250000000000:ℝ)^2)*(545502971679/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_136 :
    ∀ u ∈ Set.Icc (17/64:ℝ) (137/512:ℝ), (889698819256701636650141/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1341235986321/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(137/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(137/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (17/64:ℝ) (137/512:ℝ) (1341235986321/250000000000:ℝ) (1069467409093/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0409).1
  intro u hu
  exact (show (889698819256701636650141/1000000000000000000000000:ℝ) ≤ (1/4-6*(1341235986321/250000000000:ℝ)+4*(1341235986321/250000000000:ℝ)^2)*(1069467409093/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_137 :
    ∀ u ∈ Set.Icc (137/512:ℝ) (69/256:ℝ), (880208048276601117164071/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (336621358887/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(69/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (137/512:ℝ) (69/256:ℝ) (336621358887/62500000000:ℝ) (52413413447/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0414).1
  intro u hu
  exact (show (880208048276601117164071/1000000000000000000000000:ℝ) ≤ (1/4-6*(336621358887/62500000000:ℝ)+4*(336621358887/62500000000:ℝ)^2)*(52413413447/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_138 :
    ∀ u ∈ Set.Icc (69/256:ℝ) (139/512:ℝ), (217685023200282580708467/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2703510861077/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(139/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(139/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (69/256:ℝ) (139/512:ℝ) (2703510861077/500000000000:ℝ) (102740490249/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0415).1
  intro u hu
  exact (show (217685023200282580708467/250000000000000000000000:ℝ) ≤ (1/4-6*(2703510861077/500000000000:ℝ)+4*(2703510861077/500000000000:ℝ)^2)*(102740490249/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_139 :
    ∀ u ∈ Set.Icc (139/512:ℝ) (35/128:ℝ), (861296172253319353622509/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (217127368273/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (139/512:ℝ) (35/128:ℝ) (217127368273/40000000000:ℝ) (251718424509/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0420).1
  intro u hu
  exact (show (861296172253319353622509/1000000000000000000000000:ℝ) ≤ (1/4-6*(217127368273/40000000000:ℝ)+4*(217127368273/40000000000:ℝ)^2)*(251718424509/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_140 :
    ∀ u ∈ Set.Icc (35/128:ℝ) (141/512:ℝ), (851877492518435817071201/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2724714759559/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(141/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(141/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (35/128:ℝ) (141/512:ℝ) (2724714759559/500000000000:ℝ) (246667763263/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0421).1
  intro u hu
  exact (show (851877492518435817071201/1000000000000000000000000:ℝ) ≤ (1/4-6*(2724714759559/500000000000:ℝ)+4*(2724714759559/500000000000:ℝ)^2)*(246667763263/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_141 :
    ∀ u ∈ Set.Icc (141/512:ℝ) (71/256:ℝ), (842485245662307302529057/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5470757983213/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(71/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (141/512:ℝ) (71/256:ℝ) (5470757983213/1000000000000:ℝ) (966793374627/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0426).1
  intro u hu
  exact (show (842485245662307302529057/1000000000000000000000000:ℝ) ≤ (1/4-6*(5470757983213/1000000000000:ℝ)+4*(5470757983213/1000000000000:ℝ)^2)*(966793374627/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_142 :
    ∀ u ∈ Set.Icc (71/256:ℝ) (143/512:ℝ), (208280152422305870594033/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5492169924557/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(143/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(143/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (71/256:ℝ) (143/512:ℝ) (5492169924557/1000000000000:ℝ) (473618539969/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0427).1
  intro u hu
  exact (show (208280152422305870594033/250000000000000000000000:ℝ) ≤ (1/4-6*(5492169924557/1000000000000:ℝ)+4*(5492169924557/1000000000000:ℝ)^2)*(473618539969/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_143 :
    ∀ u ∈ Set.Icc (143/512:ℝ) (9/32:ℝ), (102973093536103918447049/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5513665669869/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (143/512:ℝ) (9/32:ℝ) (5513665669869/1000000000000:ℝ) (115999824587/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0432).1
  intro u hu
  exact (show (102973093536103918447049/125000000000000000000000:ℝ) ≤ (1/4-6*(5513665669869/1000000000000:ℝ)+4*(5513665669869/1000000000000:ℝ)^2)*(115999824587/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_144 :
    ∀ u ∈ Set.Icc (9/32:ℝ) (145/512:ℝ), (20361970264686498177509/25000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5535245547149/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(145/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(145/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (9/32:ℝ) (145/512:ℝ) (5535245547149/1000000000000:ℝ) (14204286931/1562500000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0433).1
  intro u hu
  exact (show (20361970264686498177509/25000000000000000000000:ℝ) ≤ (1/4-6*(5535245547149/1000000000000:ℝ)+4*(5535245547149/1000000000000:ℝ)^2)*(14204286931/1562500000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_145 :
    ∀ u ∈ Set.Icc (145/512:ℝ) (73/256:ℝ), (80520393091388882743507/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5556909885681/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(73/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (145/512:ℝ) (73/256:ℝ) (5556909885681/1000000000000:ℝ) (445230415351/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0438).1
  intro u hu
  exact (show (80520393091388882743507/100000000000000000000000:ℝ) ≤ (1/4-6*(5556909885681/1000000000000:ℝ)+4*(5556909885681/1000000000000:ℝ)^2)*(445230415351/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_146 :
    ∀ u ∈ Set.Icc (73/256:ℝ) (147/512:ℝ), (99495153570601387524011/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5578659016037/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(147/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(147/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (73/256:ℝ) (147/512:ℝ) (5578659016037/1000000000000:ℝ) (872154459999/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0439).1
  intro u hu
  exact (show (99495153570601387524011/125000000000000000000000:ℝ) ≤ (1/4-6*(5578659016037/1000000000000:ℝ)+4*(5578659016037/1000000000000:ℝ)^2)*(872154459999/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_147 :
    ∀ u ∈ Set.Icc (147/512:ℝ) (37/128:ℝ), (393375903785310745672377/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2800246635041/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (147/512:ℝ) (37/128:ℝ) (2800246635041/500000000000:ℝ) (854151725693/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0444).1
  intro u hu
  exact (show (393375903785310745672377/500000000000000000000000:ℝ) ≤ (1/4-6*(2800246635041/500000000000:ℝ)+4*(2800246635041/500000000000:ℝ)^2)*(854151725693/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_148 :
    ∀ u ∈ Set.Icc (37/128:ℝ) (149/512:ℝ), (194394189120748864607043/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5622412980981/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(149/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(149/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (37/128:ℝ) (149/512:ℝ) (5622412980981/1000000000000:ℝ) (418224557351/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0445).1
  intro u hu
  exact (show (194394189120748864607043/250000000000000000000000:ℝ) ≤ (1/4-6*(5622412980981/1000000000000:ℝ)+4*(5622412980981/1000000000000:ℝ)^2)*(418224557351/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_149 :
    ∀ u ∈ Set.Icc (149/512:ℝ) (75/256:ℝ), (192109287038277537851283/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1411104620801/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (149/512:ℝ) (75/256:ℝ) (1411104620801/250000000000:ℝ) (819043127053/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0450).1
  intro u hu
  exact (show (192109287038277537851283/250000000000000000000000:ℝ) ≤ (1/4-6*(1411104620801/250000000000:ℝ)+4*(1411104620801/250000000000:ℝ)^2)*(819043127053/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_150 :
    ∀ u ∈ Set.Icc (75/256:ℝ) (151/512:ℝ), (759334039519671048511609/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2833255056263/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(151/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(151/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (75/256:ℝ) (151/512:ℝ) (2833255056263/500000000000:ℝ) (801930276291/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0451).1
  intro u hu
  exact (show (759334039519671048511609/1000000000000000000000000:ℝ) ≤ (1/4-6*(2833255056263/500000000000:ℝ)+4*(2833255056263/500000000000:ℝ)^2)*(801930276291/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_151 :
    ∀ u ∈ Set.Icc (151/512:ℝ) (19/64:ℝ), (375134235707624221016263/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5688688206041/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (151/512:ℝ) (19/64:ℝ) (5688688206041/1000000000000:ℝ) (78510708989/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0456).1
  intro u hu
  exact (show (375134235707624221016263/500000000000000000000000:ℝ) ≤ (1/4-6*(5688688206041/1000000000000:ℝ)+4*(5688688206041/1000000000000:ℝ)^2)*(78510708989/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_152 :
    ∀ u ∈ Set.Icc (19/64:ℝ) (153/512:ℝ), (370620734176972153163053/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (71386913777/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(153/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(153/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (19/64:ℝ) (153/512:ℝ) (71386913777/12500000000:ℝ) (768570109637/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0457).1
  intro u hu
  exact (show (370620734176972153163053/500000000000000000000000:ℝ) ≤ (1/4-6*(71386913777/12500000000:ℝ)+4*(71386913777/12500000000:ℝ)^2)*(768570109637/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_153 :
    ∀ u ∈ Set.Icc (153/512:ℝ) (77/256:ℝ), (732254038351135320149277/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2866652570309/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(77/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (153/512:ℝ) (77/256:ℝ) (2866652570309/500000000000:ℝ) (376157946017/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0462).1
  intro u hu
  exact (show (732254038351135320149277/1000000000000000000000000:ℝ) ≤ (1/4-6*(2866652570309/500000000000:ℝ)+4*(2866652570309/500000000000:ℝ)^2)*(376157946017/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_154 :
    ∀ u ∈ Set.Icc (77/256:ℝ) (155/512:ℝ), (361653586367971121122721/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2877872331241/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(155/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(155/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (77/256:ℝ) (155/512:ℝ) (2877872331241/500000000000:ℝ) (736341008679/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0463).1
  intro u hu
  exact (show (361653586367971121122721/500000000000000000000000:ℝ) ≤ (1/4-6*(2877872331241/500000000000:ℝ)+4*(2877872331241/500000000000:ℝ)^2)*(736341008679/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_155 :
    ∀ u ∈ Set.Icc (155/512:ℝ) (39/128:ℝ), (357200922982804769686459/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (115565440203/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (155/512:ℝ) (39/128:ℝ) (115565440203/20000000000:ℝ) (720642046639/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0468).1
  intro u hu
  exact (show (357200922982804769686459/500000000000000000000000:ℝ) ≤ (1/4-6*(115565440203/20000000000:ℝ)+4*(115565440203/20000000000:ℝ)^2)*(720642046639/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_156 :
    ∀ u ∈ Set.Icc (39/128:ℝ) (157/512:ℝ), (705539015461980504919239/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1160177505473/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(157/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(157/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (39/128:ℝ) (157/512:ℝ) (1160177505473/200000000000:ℝ) (176303902207/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0469).1
  intro u hu
  exact (show (705539015461980504919239/1000000000000000000000000:ℝ) ≤ (1/4-6*(1160177505473/200000000000:ℝ)+4*(1160177505473/200000000000:ℝ)^2)*(176303902207/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_157 :
    ∀ u ∈ Set.Icc (157/512:ℝ) (79/256:ℝ), (348359810723514749431253/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5823591559211/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(79/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (157/512:ℝ) (79/256:ℝ) (5823591559211/1000000000000:ℝ) (86257289297/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0474).1
  intro u hu
  exact (show (348359810723514749431253/500000000000000000000000:ℝ) ≤ (1/4-6*(5823591559211/1000000000000:ℝ)+4*(5823591559211/1000000000000:ℝ)^2)*(86257289297/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_158 :
    ∀ u ∈ Set.Icc (79/256:ℝ) (159/512:ℝ), (171986146693352966422757/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2923192226063/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(159/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(159/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (79/256:ℝ) (159/512:ℝ) (2923192226063/500000000000:ℝ) (27006671959/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0475).1
  intro u hu
  exact (show (171986146693352966422757/250000000000000000000000:ℝ) ≤ (1/4-6*(2923192226063/500000000000:ℝ)+4*(2923192226063/500000000000:ℝ)^2)*(27006671959/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_159 :
    ∀ u ∈ Set.Icc (159/512:ℝ) (5/16:ℝ), (339607408390625219458253/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5869266553901/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (159/512:ℝ) (5/16:ℝ) (5869266553901/1000000000000:ℝ) (330268857621/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0480).1
  intro u hu
  exact (show (339607408390625219458253/500000000000000000000000:ℝ) ≤ (1/4-6*(5869266553901/1000000000000:ℝ)+4*(5869266553901/1000000000000:ℝ)^2)*(330268857621/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

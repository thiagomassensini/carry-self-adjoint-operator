import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_384 :
    ∀ u ∈ Set.Icc (3/4:ℝ) (385/512:ℝ), (1512646200463755506153/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14134744676991/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(385/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(385/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/4:ℝ) (385/512:ℝ) (14134744676991/1000000000000:ℝ) (211675683/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1153).1
  intro u hu
  exact (show (1512646200463755506153/1000000000000000000000000:ℝ) ≤ (1/4-6*(14134744676991/1000000000000:ℝ)+4*(14134744676991/1000000000000:ℝ)^2)*(211675683/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_385 :
    ∀ u ∈ Set.Icc (385/512:ℝ) (193/256:ℝ), (1444535251539540222233/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7095033251741/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(193/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(193/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (385/512:ℝ) (193/256:ℝ) (7095033251741/500000000000:ℝ) (40095821/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1158).1
  intro u hu
  exact (show (1444535251539540222233/1000000000000000000000000:ℝ) ≤ (1/4-6*(7095033251741/500000000000:ℝ)+4*(7095033251741/500000000000:ℝ)^2)*(40095821/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_386 :
    ∀ u ∈ Set.Icc (193/256:ℝ) (387/512:ℝ), (43099680239324046491/31250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14245604853481/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(387/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(387/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (193/256:ℝ) (387/512:ℝ) (14245604853481/1000000000000:ℝ) (189833661/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1159).1
  intro u hu
  exact (show (43099680239324046491/31250000000000000000000:ℝ) ≤ (1/4-6*(14245604853481/1000000000000:ℝ)+4*(14245604853481/1000000000000:ℝ)^2)*(189833661/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_387 :
    ∀ u ∈ Set.Icc (387/512:ℝ) (97/128:ℝ), (1316511465572846673839/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2860272114887/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(97/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (387/512:ℝ) (97/128:ℝ) (2860272114887/200000000000:ℝ) (89857211/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1164).1
  intro u hu
  exact (show (1316511465572846673839/1000000000000000000000000:ℝ) ≤ (1/4-6*(2860272114887/200000000000:ℝ)+4*(2860272114887/200000000000:ℝ)^2)*(89857211/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_388 :
    ∀ u ∈ Set.Icc (97/128:ℝ) (389/512:ℝ), (125640493830125248933/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14357334517111/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(389/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(389/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (97/128:ℝ) (389/512:ℝ) (14357334517111/1000000000000:ℝ) (85048737/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1165).1
  intro u hu
  exact (show (125640493830125248933/100000000000000000000000:ℝ) ≤ (1/4-6*(14357334517111/1000000000000:ℝ)+4*(14357334517111/1000000000000:ℝ)^2)*(85048737/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_389 :
    ∀ u ∈ Set.Icc (389/512:ℝ) (195/256:ℝ), (599388808956942227249/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2882705507121/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(195/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(195/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (389/512:ℝ) (195/256:ℝ) (2882705507121/200000000000:ℝ) (32191977/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1170).1
  intro u hu
  exact (show (599388808956942227249/500000000000000000000000:ℝ) ≤ (1/4-6*(2882705507121/200000000000:ℝ)+4*(2882705507121/200000000000:ℝ)^2)*(32191977/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_390 :
    ∀ u ∈ Set.Icc (195/256:ℝ) (391/512:ℝ), (228707943376429807781/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7234970243677/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(391/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(391/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (195/256:ℝ) (391/512:ℝ) (7234970243677/500000000000:ℝ) (15227967/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1171).1
  intro u hu
  exact (show (228707943376429807781/200000000000000000000000:ℝ) ≤ (1/4-6*(7234970243677/500000000000:ℝ)+4*(7234970243677/500000000000:ℝ)^2)*(15227967/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_391 :
    ∀ u ∈ Set.Icc (391/512:ℝ) (49/64:ℝ), (545302077230300748787/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7263287116577/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (391/512:ℝ) (49/64:ℝ) (7263287116577/500000000000:ℝ) (28807151/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1176).1
  intro u hu
  exact (show (545302077230300748787/500000000000000000000000:ℝ) ≤ (1/4-6*(7263287116577/500000000000:ℝ)+4*(7263287116577/500000000000:ℝ)^2)*(28807151/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_392 :
    ∀ u ∈ Set.Icc (49/64:ℝ) (393/512:ℝ), (20797729653449226181/20000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (911464352323/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(393/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(393/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (49/64:ℝ) (393/512:ℝ) (911464352323/62500000000:ℝ) (68103971/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1177).1
  intro u hu
  exact (show (20797729653449226181/20000000000000000000000:ℝ) ≤ (1/4-6*(911464352323/62500000000:ℝ)+4*(911464352323/62500000000:ℝ)^2)*(68103971/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_393 :
    ∀ u ∈ Set.Icc (393/512:ℝ) (197/256:ℝ), (991304873654742215107/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7320253783471/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(197/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(197/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (393/512:ℝ) (197/256:ℝ) (7320253783471/500000000000:ℝ) (128776883/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1182).1
  intro u hu
  exact (show (991304873654742215107/1000000000000000000000000:ℝ) ≤ (1/4-6*(7320253783471/500000000000:ℝ)+4*(7320253783471/500000000000:ℝ)^2)*(128776883/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_394 :
    ∀ u ∈ Set.Icc (197/256:ℝ) (395/512:ℝ), (944780016879046322359/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1837226111677/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(395/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(395/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (197/256:ℝ) (395/512:ℝ) (1837226111677/125000000000:ℝ) (121724043/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1183).1
  intro u hu
  exact (show (944780016879046322359/1000000000000000000000000:ℝ) ≤ (1/4-6*(1837226111677/125000000000:ℝ)+4*(1837226111677/125000000000:ℝ)^2)*(121724043/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_395 :
    ∀ u ∈ Set.Icc (395/512:ℝ) (99/128:ℝ), (900235061987027897989/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14755334490941/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(99/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (395/512:ℝ) (99/128:ℝ) (14755334490941/1000000000000:ℝ) (11503167/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1188).1
  intro u hu
  exact (show (900235061987027897989/1000000000000000000000000:ℝ) ≤ (1/4-6*(14755334490941/1000000000000:ℝ)+4*(14755334490941/1000000000000:ℝ)^2)*(11503167/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_396 :
    ∀ u ∈ Set.Icc (99/128:ℝ) (397/512:ℝ), (428797801111739030787/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14813085237289/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(397/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(397/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (99/128:ℝ) (397/512:ℝ) (14813085237289/1000000000000:ℝ) (108682771/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1189).1
  intro u hu
  exact (show (428797801111739030787/500000000000000000000000:ℝ) ≤ (1/4-6*(14813085237289/1000000000000:ℝ)+4*(14813085237289/1000000000000:ℝ)^2)*(108682771/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_397 :
    ∀ u ∈ Set.Icc (397/512:ℝ) (199/256:ℝ), (816789565727244178923/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14871062013667/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(199/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(199/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (397/512:ℝ) (199/256:ℝ) (14871062013667/1000000000000:ℝ) (102661077/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1194).1
  intro u hu
  exact (show (816789565727244178923/1000000000000000000000000:ℝ) ≤ (1/4-6*(14871062013667/1000000000000:ℝ)+4*(14871062013667/1000000000000:ℝ)^2)*(102661077/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_398 :
    ∀ u ∈ Set.Icc (199/256:ℝ) (399/512:ℝ), (194436798485739133227/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3732316426183/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(399/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(399/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (199/256:ℝ) (399/512:ℝ) (3732316426183/250000000000:ℝ) (4847551/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1195).1
  intro u hu
  exact (show (194436798485739133227/250000000000000000000000:ℝ) ≤ (1/4-6*(3732316426183/250000000000:ℝ)+4*(3732316426183/250000000000:ℝ)^2)*(4847551/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_399 :
    ∀ u ∈ Set.Icc (399/512:ℝ) (25/32:ℝ), (370200483421154245411/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14987697198603/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (399/512:ℝ) (25/32:ℝ) (14987697198603/1000000000000:ℝ) (11442213/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1200).1
  intro u hu
  exact (show (370200483421154245411/500000000000000000000000:ℝ) ≤ (1/4-6*(14987697198603/1000000000000:ℝ)+4*(14987697198603/1000000000000:ℝ)^2)*(11442213/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_400 :
    ∀ u ∈ Set.Icc (25/32:ℝ) (401/512:ℝ), (704685553528594139707/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (24074171819/1600000000:ℝ) ≤ Real.pi*Real.exp (2*(401/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(401/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (25/32:ℝ) (401/512:ℝ) (24074171819/1600000000:ℝ) (540043/625000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1201).1
  intro u hu
  exact (show (704685553528594139707/1000000000000000000000000:ℝ) ≤ (1/4-6*(24074171819/1600000000:ℝ)+4*(24074171819/1600000000:ℝ)^2)*(540043/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_401 :
    ∀ u ∈ Set.Icc (401/512:ℝ) (201/256:ℝ), (335268886713492521407/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (15105247164633/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(201/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(201/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (401/512:ℝ) (201/256:ℝ) (15105247164633/1000000000000:ℝ) (81544923/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1206).1
  intro u hu
  exact (show (335268886713492521407/500000000000000000000000:ℝ) ≤ (1/4-6*(15105247164633/1000000000000:ℝ)+4*(15105247164633/1000000000000:ℝ)^2)*(81544923/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_402 :
    ∀ u ∈ Set.Icc (201/256:ℝ) (403/512:ℝ), (79737063846885334561/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (236943241101/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(403/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(403/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (201/256:ℝ) (403/512:ℝ) (236943241101/15625000000:ℝ) (19234701/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1207).1
  intro u hu
  exact (show (79737063846885334561/125000000000000000000000:ℝ) ≤ (1/4-6*(236943241101/15625000000:ℝ)+4*(236943241101/15625000000:ℝ)^2)*(19234701/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_403 :
    ∀ u ∈ Set.Icc (403/512:ℝ) (101/128:ℝ), (606702680145717299149/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (15223719086473/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(101/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (403/512:ℝ) (101/128:ℝ) (15223719086473/1000000000000:ℝ) (72576069/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1212).1
  intro u hu
  exact (show (606702680145717299149/1000000000000000000000000:ℝ) ≤ (1/4-6*(15223719086473/1000000000000:ℝ)+4*(15223719086473/1000000000000:ℝ)^2)*(72576069/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_404 :
    ∀ u ∈ Set.Icc (101/128:ℝ) (405/512:ℝ), (28844958935722614037/50000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3056660607659/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(405/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(405/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (101/128:ℝ) (405/512:ℝ) (3056660607659/200000000000:ℝ) (68444817/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1213).1
  intro u hu
  exact (show (28844958935722614037/50000000000000000000000:ℝ) ≤ (1/4-6*(3056660607659/200000000000:ℝ)+4*(3056660607659/200000000000:ℝ)^2)*(68444817/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_405 :
    ∀ u ∈ Set.Icc (405/512:ℝ) (203/256:ℝ), (548430824615958364363/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (15343120195111/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(203/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(203/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (405/512:ℝ) (203/256:ℝ) (15343120195111/1000000000000:ℝ) (64533677/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1218).1
  intro u hu
  exact (show (548430824615958364363/1000000000000000000000000:ℝ) ≤ (1/4-6*(15343120195111/1000000000000:ℝ)+4*(15343120195111/1000000000000:ℝ)^2)*(64533677/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_406 :
    ∀ u ∈ Set.Icc (203/256:ℝ) (407/512:ℝ), (260622157493413149371/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (770158573483/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(407/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(407/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (203/256:ℝ) (407/512:ℝ) (770158573483/50000000000:ℝ) (15207947/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1219).1
  intro u hu
  exact (show (260622157493413149371/500000000000000000000000:ℝ) ≤ (1/4-6*(770158573483/50000000000:ℝ)+4*(770158573483/50000000000:ℝ)^2)*(15207947/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_407 :
    ∀ u ∈ Set.Icc (407/512:ℝ) (51/64:ℝ), (61911020223082356311/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3865864444563/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (407/512:ℝ) (51/64:ℝ) (3865864444563/250000000000:ℝ) (57328777/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1224).1
  intro u hu
  exact (show (61911020223082356311/125000000000000000000000:ℝ) ≤ (1/4-6*(3865864444563/250000000000:ℝ)+4*(3865864444563/250000000000:ℝ)^2)*(57328777/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_408 :
    ∀ u ∈ Set.Icc (51/64:ℝ) (409/512:ℝ), (235256328239877616081/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (970248752549/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(409/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(409/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (51/64:ℝ) (409/512:ℝ) (970248752549/62500000000:ℝ) (54014741/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1225).1
  intro u hu
  exact (show (235256328239877616081/500000000000000000000000:ℝ) ≤ (1/4-6*(970248752549/62500000000:ℝ)+4*(970248752549/62500000000:ℝ)^2)*(54014741/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_409 :
    ∀ u ∈ Set.Icc (409/512:ℝ) (205/256:ℝ), (446869821522720662701/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3116947836151/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(205/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(205/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (409/512:ℝ) (205/256:ℝ) (3116947836151/200000000000:ℝ) (12720057/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1230).1
  intro u hu
  exact (show (446869821522720662701/1000000000000000000000000:ℝ) ≤ (1/4-6*(3116947836151/200000000000:ℝ)+4*(3116947836151/200000000000:ℝ)^2)*(12720057/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_410 :
    ∀ u ∈ Set.Icc (205/256:ℝ) (411/512:ℝ), (424313339071429810603/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (625829445011/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(411/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(411/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (205/256:ℝ) (411/512:ℝ) (625829445011/40000000000:ℝ) (5989527/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1231).1
  intro u hu
  exact (show (424313339071429810603/1000000000000000000000000:ℝ) ≤ (1/4-6*(625829445011/40000000000:ℝ)+4*(625829445011/40000000000:ℝ)^2)*(5989527/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_411 :
    ∀ u ∈ Set.Icc (411/512:ℝ) (103/128:ℝ), (100699638499636611463/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7853485902543/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(103/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (411/512:ℝ) (103/128:ℝ) (7853485902543/500000000000:ℝ) (45114101/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1236).1
  intro u hu
  exact (show (100699638499636611463/250000000000000000000000:ℝ) ≤ (1/4-6*(7853485902543/500000000000:ℝ)+4*(7853485902543/500000000000:ℝ)^2)*(45114101/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_412 :
    ∀ u ∈ Set.Icc (103/128:ℝ) (413/512:ℝ), (382282366579116366383/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3942111788643/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(413/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(413/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (103/128:ℝ) (413/512:ℝ) (3942111788643/250000000000:ℝ) (42465673/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1237).1
  intro u hu
  exact (show (382282366579116366383/1000000000000000000000000:ℝ) ≤ (1/4-6*(3942111788643/250000000000:ℝ)+4*(3942111788643/250000000000:ℝ)^2)*(42465673/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_413 :
    ∀ u ∈ Set.Icc (413/512:ℝ) (207/256:ℝ), (362723226362548670817/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (15830163111773/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(207/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(207/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (413/512:ℝ) (207/256:ℝ) (15830163111773/1000000000000:ℝ) (1248847/3125000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1242).1
  intro u hu
  exact (show (362723226362548670817/1000000000000000000000000:ℝ) ≤ (1/4-6*(15830163111773/1000000000000:ℝ)+4*(15830163111773/1000000000000:ℝ)^2)*(1248847/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_414 :
    ∀ u ∈ Set.Icc (207/256:ℝ) (415/512:ℝ), (172040548003624162409/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19865150773/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(415/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(415/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (207/256:ℝ) (415/512:ℝ) (19865150773/1250000000:ℝ) (37598933/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1243).1
  intro u hu
  exact (show (172040548003624162409/500000000000000000000000:ℝ) ≤ (1/4-6*(19865150773/1250000000:ℝ)+4*(19865150773/1250000000:ℝ)^2)*(37598933/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_415 :
    ∀ u ∈ Set.Icc (415/512:ℝ) (13/16:ℝ), (13052694597686269063/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3988580154963/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (415/512:ℝ) (13/16:ℝ) (3988580154963/250000000000:ℝ) (17683023/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1248).1
  intro u hu
  exact (show (13052694597686269063/40000000000000000000000:ℝ) ≤ (1/4-6*(3988580154963/250000000000:ℝ)+4*(3988580154963/250000000000:ℝ)^2)*(17683023/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

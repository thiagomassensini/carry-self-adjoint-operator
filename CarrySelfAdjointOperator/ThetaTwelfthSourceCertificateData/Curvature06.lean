import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_192 :
    ∀ u ∈ Set.Icc (3/8:ℝ) (193/512:ℝ), (421372198150856993365933/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (417298788559/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(193/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(193/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/8:ℝ) (193/512:ℝ) (417298788559/62500000000:ℝ) (304224667353/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0577).1
  intro u hu
  exact (show (421372198150856993365933/1000000000000000000000000:ℝ) ≤ (1/4-6*(417298788559/62500000000:ℝ)+4*(417298788559/62500000000:ℝ)^2)*(304224667353/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_193 :
    ∀ u ∈ Set.Icc (193/512:ℝ) (97/256:ℝ), (82917690064399091062251/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1340582559483/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(97/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (193/512:ℝ) (97/256:ℝ) (1340582559483/200000000000:ℝ) (1186668643/400000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0582).1
  intro u hu
  exact (show (82917690064399091062251/200000000000000000000000:ℝ) ≤ (1/4-6*(1340582559483/200000000000:ℝ)+4*(1340582559483/200000000000:ℝ)^2)*(1186668643/400000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_194 :
    ∀ u ∈ Set.Icc (97/256:ℝ) (195/512:ℝ), (407869947363270890347949/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6729147256349/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(195/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(195/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (97/256:ℝ) (195/512:ℝ) (6729147256349/1000000000000:ℝ) (56497619/19531250000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0583).1
  intro u hu
  exact (show (407869947363270890347949/1000000000000000000000000:ℝ) ≤ (1/4-6*(6729147256349/1000000000000:ℝ)+4*(6729147256349/1000000000000:ℝ)^2)*(56497619/19531250000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_195 :
    ∀ u ∈ Set.Icc (195/512:ℝ) (49/128:ℝ), (200608460632174198657677/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1688871098513/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (195/512:ℝ) (49/128:ℝ) (1688871098513/250000000000:ℝ) (282024050041/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0588).1
  intro u hu
  exact (show (200608460632174198657677/500000000000000000000000:ℝ) ≤ (1/4-6*(1688871098513/250000000000:ℝ)+4*(1688871098513/250000000000:ℝ)^2)*(282024050041/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_196 :
    ∀ u ∈ Set.Icc (49/128:ℝ) (197/512:ℝ), (394629585759214226027709/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6781924612397/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(197/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(197/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (49/128:ℝ) (197/512:ℝ) (6781924612397/1000000000000:ℝ) (274933345111/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0589).1
  intro u hu
  exact (show (394629585759214226027709/1000000000000000000000000:ℝ) ≤ (1/4-6*(6781924612397/1000000000000:ℝ)+4*(6781924612397/1000000000000:ℝ)^2)*(274933345111/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_197 :
    ∀ u ∈ Set.Icc (197/512:ℝ) (99/256:ℝ), (194054068215068659549999/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6808468314831/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(99/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (197/512:ℝ) (99/256:ℝ) (6808468314831/1000000000000:ℝ) (133996590813/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0594).1
  intro u hu
  exact (show (194054068215068659549999/500000000000000000000000:ℝ) ≤ (1/4-6*(6808468314831/1000000000000:ℝ)+4*(6808468314831/1000000000000:ℝ)^2)*(133996590813/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_198 :
    ∀ u ∈ Set.Icc (99/256:ℝ) (199/512:ℝ), (190826375409226913883677/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6835115906379/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(199/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(199/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (99/256:ℝ) (199/512:ℝ) (6835115906379/1000000000000:ℝ) (65300267963/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0595).1
  intro u hu
  exact (show (190826375409226913883677/500000000000000000000000:ℝ) ≤ (1/4-6*(6835115906379/1000000000000:ℝ)+4*(6835115906379/1000000000000:ℝ)^2)*(65300267963/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_199 :
    ∀ u ∈ Set.Icc (199/512:ℝ) (25/64:ℝ), (375263588556175193661479/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6861867793651/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (199/512:ℝ) (25/64:ℝ) (6861867793651/1000000000000:ℝ) (12727727663/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0600).1
  intro u hu
  exact (show (375263588556175193661479/1000000000000000000000000:ℝ) ≤ (1/4-6*(6861867793651/1000000000000:ℝ)+4*(6861867793651/1000000000000:ℝ)^2)*(12727727663/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_200 :
    ∀ u ∈ Set.Icc (25/64:ℝ) (201/512:ℝ), (368940791481683951042041/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (137774487697/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(201/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(201/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (25/64:ℝ) (201/512:ℝ) (137774487697/20000000000:ℝ) (248051188579/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0601).1
  intro u hu
  exact (show (368940791481683951042041/1000000000000000000000000:ℝ) ≤ (1/4-6*(137774487697/20000000000:ℝ)+4*(137774487697/20000000000:ℝ)^2)*(248051188579/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_201 :
    ∀ u ∈ Set.Icc (201/512:ℝ) (101/256:ℝ), (181342241891124615302757/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (276627443591/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(101/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (201/512:ℝ) (101/256:ℝ) (276627443591/40000000000:ℝ) (241688565857/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0606).1
  intro u hu
  exact (show (181342241891124615302757/500000000000000000000000:ℝ) ≤ (1/4-6*(276627443591/40000000000:ℝ)+4*(276627443591/40000000000:ℝ)^2)*(241688565857/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_202 :
    ∀ u ∈ Set.Icc (101/256:ℝ) (203/512:ℝ), (356494772124939210200983/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6942753319829/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(203/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(203/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (101/256:ℝ) (203/512:ℝ) (6942753319829/1000000000000:ℝ) (235464298503/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0607).1
  intro u hu
  exact (show (356494772124939210200983/1000000000000000000000000:ℝ) ≤ (1/4-6*(6942753319829/1000000000000:ℝ)+4*(6942753319829/1000000000000:ℝ)^2)*(235464298503/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_203 :
    ∀ u ∈ Set.Icc (203/512:ℝ) (51/128:ℝ), (875929364510965849653/2500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3484963244013/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (203/512:ℝ) (51/128:ℝ) (3484963244013/500000000000:ℝ) (22937602533/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0612).1
  intro u hu
  exact (show (875929364510965849653/2500000000000000000000:ℝ) ≤ (1/4-6*(3484963244013/500000000000:ℝ)+4*(3484963244013/500000000000:ℝ)^2)*(22937602533/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_204 :
    ∀ u ∈ Set.Icc (51/128:ℝ) (205/512:ℝ), (172157738447815749517883/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6997206008997/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(205/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(205/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (51/128:ℝ) (205/512:ℝ) (6997206008997/1000000000000:ℝ) (223421410591/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0613).1
  intro u hu
  exact (show (172157738447815749517883/500000000000000000000000:ℝ) ≤ (1/4-6*(6997206008997/1000000000000:ℝ)+4*(6997206008997/1000000000000:ℝ)^2)*(223421410591/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_205 :
    ∀ u ∈ Set.Icc (205/512:ℝ) (103/256:ℝ), (169163010199648404157571/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3512296149497/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(103/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (205/512:ℝ) (103/256:ℝ) (3512296149497/500000000000:ℝ) (3399971/1562500000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0618).1
  intro u hu
  exact (show (169163010199648404157571/500000000000000000000000:ℝ) ≤ (1/4-6*(3512296149497/500000000000:ℝ)+4*(3512296149497/500000000000:ℝ)^2)*(3399971/1562500000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_206 :
    ∀ u ∈ Set.Icc (103/256:ℝ) (207/512:ℝ), (332403414418076337135631/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7052085775899/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(207/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(207/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (103/256:ℝ) (207/512:ℝ) (7052085775899/1000000000000:ℝ) (211903940763/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0619).1
  intro u hu
  exact (show (332403414418076337135631/1000000000000000000000000:ℝ) ≤ (1/4-6*(7052085775899/1000000000000:ℝ)+4*(7052085775899/1000000000000:ℝ)^2)*(211903940763/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_207 :
    ∀ u ∈ Set.Icc (207/512:ℝ) (13/32:ℝ), (326547680306461325909969/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (707968685923/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (207/512:ℝ) (13/32:ℝ) (707968685923/100000000000:ℝ) (103168270791/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0624).1
  intro u hu
  exact (show (326547680306461325909969/1000000000000000000000000:ℝ) ≤ (1/4-6*(707968685923/100000000000:ℝ)+4*(707968685923/100000000000:ℝ)^2)*(103168270791/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_208 :
    ∀ u ∈ Set.Icc (13/32:ℝ) (209/512:ℝ), (160379411427857512154149/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7107395970147/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(209/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(209/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (13/32:ℝ) (209/512:ℝ) (7107395970147/1000000000000:ℝ) (6277928521/3125000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0625).1
  intro u hu
  exact (show (160379411427857512154149/500000000000000000000000:ℝ) ≤ (1/4-6*(7107395970147/1000000000000:ℝ)+4*(7107395970147/1000000000000:ℝ)^2)*(6277928521/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_209 :
    ∀ u ∈ Set.Icc (209/512:ℝ) (105/256:ℝ), (78759207614849840720043/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3567606765729/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(105/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (209/512:ℝ) (105/256:ℝ) (3567606765729/500000000000:ℝ) (48893311439/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0630).1
  intro u hu
  exact (show (78759207614849840720043/250000000000000000000000:ℝ) ≤ (1/4-6*(3567606765729/500000000000:ℝ)+4*(3567606765729/500000000000:ℝ)^2)*(48893311439/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_210 :
    ∀ u ∈ Set.Icc (105/256:ℝ) (211/512:ℝ), (38672709412707373928059/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3581569983813/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(211/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(211/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (105/256:ℝ) (211/512:ℝ) (3581569983813/500000000000:ℝ) (38074591613/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0631).1
  intro u hu
  exact (show (38672709412707373928059/125000000000000000000000:ℝ) ≤ (1/4-6*(3581569983813/500000000000:ℝ)+4*(3581569983813/500000000000:ℝ)^2)*(38074591613/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_211 :
    ∀ u ∈ Set.Icc (211/512:ℝ) (53/128:ℝ), (151896656769668924807039/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3595587852387/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (211/512:ℝ) (53/128:ℝ) (3595587852387/500000000000:ℝ) (7411627693/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0636).1
  intro u hu
  exact (show (151896656769668924807039/500000000000000000000000:ℝ) ≤ (1/4-6*(3595587852387/500000000000:ℝ)+4*(3595587852387/500000000000:ℝ)^2)*(7411627693/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_212 :
    ∀ u ∈ Set.Icc (53/128:ℝ) (213/512:ℝ), (59654337099177772698799/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1443864234139/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(213/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(213/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (53/128:ℝ) (213/512:ℝ) (1443864234139/200000000000:ℝ) (90162158371/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0637).1
  intro u hu
  exact (show (59654337099177772698799/200000000000000000000000:ℝ) ≤ (1/4-6*(1443864234139/200000000000:ℝ)+4*(1443864234139/200000000000:ℝ)^2)*(90162158371/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_213 :
    ∀ u ∈ Set.Icc (213/512:ℝ) (107/256:ℝ), (292816715856159756349177/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (905947099357/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(107/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (213/512:ℝ) (107/256:ℝ) (905947099357/125000000000:ℝ) (175471724979/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0642).1
  intro u hu
  exact (show (292816715856159756349177/1000000000000000000000000:ℝ) ≤ (1/4-6*(905947099357/125000000000:ℝ)+4*(905947099357/125000000000:ℝ)^2)*(175471724979/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_214 :
    ∀ u ∈ Set.Icc (107/256:ℝ) (215/512:ℝ), (3592853923256872964007/12500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3637971504201/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(215/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(215/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (107/256:ℝ) (215/512:ℝ) (3637971504201/500000000000:ℝ) (42682709031/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0643).1
  intro u hu
  exact (show (3592853923256872964007/12500000000000000000000:ℝ) ≤ (1/4-6*(3637971504201/500000000000:ℝ)+4*(3637971504201/500000000000:ℝ)^2)*(42682709031/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_215 :
    ∀ u ∈ Set.Icc (215/512:ℝ) (27/64:ℝ), (282106373519129414186399/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7304420244169/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (215/512:ℝ) (27/64:ℝ) (7304420244169/1000000000000:ℝ) (166099594661/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0648).1
  intro u hu
  exact (show (282106373519129414186399/1000000000000000000000000:ℝ) ≤ (1/4-6*(7304420244169/1000000000000:ℝ)+4*(7304420244169/1000000000000:ℝ)^2)*(166099594661/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_216 :
    ∀ u ∈ Set.Icc (27/64:ℝ) (217/512:ℝ), (55370154762726230771913/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1466601787337/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(217/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(217/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (27/64:ℝ) (217/512:ℝ) (1466601787337/200000000000:ℝ) (80787985213/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0649).1
  intro u hu
  exact (show (55370154762726230771913/200000000000000000000000:ℝ) ≤ (1/4-6*(1466601787337/200000000000:ℝ)+4*(1466601787337/200000000000:ℝ)^2)*(80787985213/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_217 :
    ∀ u ∈ Set.Icc (217/512:ℝ) (109/256:ℝ), (135830689454414892203241/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7361709522181/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(109/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (217/512:ℝ) (109/256:ℝ) (7361709522181/1000000000000:ℝ) (982237241/625000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0654).1
  intro u hu
  exact (show (135830689454414892203241/500000000000000000000000:ℝ) ≤ (1/4-6*(7361709522181/1000000000000:ℝ)+4*(7361709522181/1000000000000:ℝ)^2)*(982237241/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_218 :
    ∀ u ∈ Set.Icc (109/256:ℝ) (219/512:ℝ), (33317254796652589707933/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7390522438591/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(219/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(219/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (109/256:ℝ) (219/512:ℝ) (7390522438591/1000000000000:ℝ) (7642178973/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0655).1
  intro u hu
  exact (show (33317254796652589707933/125000000000000000000000:ℝ) ≤ (1/4-6*(7390522438591/1000000000000:ℝ)+4*(7390522438591/1000000000000:ℝ)^2)*(7642178973/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_219 :
    ∀ u ∈ Set.Icc (219/512:ℝ) (55/128:ℝ), (3268507342467591650561/12500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7419448125569/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (219/512:ℝ) (55/128:ℝ) (7419448125569/1000000000000:ℝ) (58058937/39062500000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0660).1
  intro u hu
  exact (show (3268507342467591650561/12500000000000000000000:ℝ) ≤ (1/4-6*(7419448125569/1000000000000:ℝ)+4*(7419448125569/1000000000000:ℝ)^2)*(58058937/39062500000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_220 :
    ∀ u ∈ Set.Icc (55/128:ℝ) (221/512:ℝ), (128244423508421206272841/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1862121756121/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(221/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(221/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (55/128:ℝ) (221/512:ℝ) (1862121756121/250000000000:ℝ) (36129481767/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0661).1
  intro u hu
  exact (show (128244423508421206272841/500000000000000000000000:ℝ) ≤ (1/4-6*(1862121756121/250000000000:ℝ)+4*(1862121756121/250000000000:ℝ)^2)*(36129481767/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_221 :
    ∀ u ∈ Set.Icc (221/512:ℝ) (111/256:ℝ), (251562624344124832607773/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1869409894609/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (221/512:ℝ) (111/256:ℝ) (1869409894609/250000000000:ℝ) (1405028203/1000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0666).1
  intro u hu
  exact (show (251562624344124832607773/1000000000000000000000000:ℝ) ≤ (1/4-6*(1869409894609/250000000000:ℝ)+4*(1869409894609/250000000000:ℝ)^2)*(1405028203/1000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_222 :
    ∀ u ∈ Set.Icc (111/256:ℝ) (223/512:ℝ), (61675428197927839744517/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3753453116129/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(223/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(223/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (111/256:ℝ) (223/512:ℝ) (3753453116129/500000000000:ℝ) (68291839601/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0667).1
  intro u hu
  exact (show (61675428197927839744517/250000000000000000000000:ℝ) ≤ (1/4-6*(3753453116129/500000000000:ℝ)+4*(3753453116129/500000000000:ℝ)^2)*(68291839601/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_223 :
    ∀ u ∈ Set.Icc (223/512:ℝ) (7/16:ℝ), (120952946156479495543801/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1884071858131/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (223/512:ℝ) (7/16:ℝ) (1884071858131/250000000000:ℝ) (5310345979/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0672).1
  intro u hu
  exact (show (120952946156479495543801/500000000000000000000000:ℝ) ≤ (1/4-6*(1884071858131/250000000000:ℝ)+4*(1884071858131/250000000000:ℝ)^2)*(5310345979/4000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

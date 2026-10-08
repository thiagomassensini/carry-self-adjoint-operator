import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_224 :
    ∀ u ∈ Set.Icc (7/8:ℝ) (225/256:ℝ), (45469611906907/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (90393037439/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/8:ℝ)) := by
    calc
      (90393037439/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(7/8:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(7/8:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (7/8:ℝ) (225/256:ℝ) (90393037439/5000000000:ℝ) (3791907/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1350).1
  intro u hu
  exact (show (45469611906907/1000000000000000000:ℝ) ≤ (1/4-6*(90393037439/5000000000:ℝ)+4*(90393037439/5000000000:ℝ)^2)*(3791907/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_225 :
    ∀ u ∈ Set.Icc (225/256:ℝ) (113/128:ℝ), (20070903384091/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (36440798931/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(225/256:ℝ)) := by
    calc
      (36440798931/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(225/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(225/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (225/256:ℝ) (113/128:ℝ) (36440798931/2000000000:ℝ) (3293391/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1356).1
  intro u hu
  exact (show (20070903384091/500000000000000000:ℝ) ≤ (1/4-6*(36440798931/2000000000:ℝ)+4*(36440798931/2000000000:ℝ)^2)*(3293391/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_226 :
    ∀ u ∈ Set.Icc (113/128:ℝ) (227/256:ℝ), (35398370214817/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (45908258791/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(113/128:ℝ)) := by
    calc
      (45908258791/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(113/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(113/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (113/128:ℝ) (227/256:ℝ) (45908258791/2500000000:ℝ) (285721/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1362).1
  intro u hu
  exact (show (35398370214817/1000000000000000000:ℝ) ≤ (1/4-6*(45908258791/2500000000:ℝ)+4*(45908258791/2500000000:ℝ)^2)*(285721/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_227 :
    ∀ u ∈ Set.Icc (227/256:ℝ) (57/64:ℝ), (15590014330449/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (185073283621/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(227/256:ℝ)) := by
    calc
      (185073283621/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(227/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(227/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (227/256:ℝ) (57/64:ℝ) (185073283621/10000000000:ℝ) (2475999/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1368).1
  intro u hu
  exact (show (15590014330449/500000000000000000:ℝ) ≤ (1/4-6*(185073283621/10000000000:ℝ)+4*(185073283621/10000000000:ℝ)^2)*(2475999/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_228 :
    ∀ u ∈ Set.Icc (57/64:ℝ) (229/256:ℝ), (27432954452633/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (186524827923/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/64:ℝ)) := by
    calc
      (186524827923/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(57/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(57/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (57/64:ℝ) (229/256:ℝ) (186524827923/10000000000:ℝ) (2143207/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1374).1
  intro u hu
  exact (show (27432954452633/1000000000000000000:ℝ) ≤ (1/4-6*(186524827923/10000000000:ℝ)+4*(186524827923/10000000000:ℝ)^2)*(2143207/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_229 :
    ∀ u ∈ Set.Icc (229/256:ℝ) (115/128:ℝ), (12054189803443/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (93993878329/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(229/256:ℝ)) := by
    calc
      (93993878329/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(229/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(229/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (229/256:ℝ) (115/128:ℝ) (93993878329/5000000000:ℝ) (926509/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1380).1
  intro u hu
  exact (show (12054189803443/500000000000000000:ℝ) ≤ (1/4-6*(93993878329/5000000000:ℝ)+4*(93993878329/5000000000:ℝ)^2)*(926509/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_230 :
    ∀ u ∈ Set.Icc (115/128:ℝ) (231/256:ℝ), (10581051391233/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (189462159107/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/128:ℝ)) := by
    calc
      (189462159107/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(115/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(115/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (115/128:ℝ) (231/256:ℝ) (189462159107/10000000000:ℝ) (1600269/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1386).1
  intro u hu
  exact (show (10581051391233/500000000000000000:ℝ) ≤ (1/4-6*(189462159107/10000000000:ℝ)+4*(189462159107/10000000000:ℝ)^2)*(1600269/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_231 :
    ∀ u ∈ Set.Icc (231/256:ℝ) (29/32:ℝ), (9277074693267/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (47737031313/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(231/256:ℝ)) := by
    calc
      (47737031313/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(231/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(231/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (231/256:ℝ) (29/32:ℝ) (47737031313/2500000000:ℝ) (276077/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1392).1
  intro u hu
  exact (show (9277074693267/500000000000000000:ℝ) ≤ (1/4-6*(47737031313/2500000000:ℝ)+4*(47737031313/2500000000:ℝ)^2)*(276077/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_232 :
    ∀ u ∈ Set.Icc (29/32:ℝ) (233/256:ℝ), (16248401359171/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (192445745779/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/32:ℝ)) := by
    calc
      (192445745779/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(29/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(29/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (29/32:ℝ) (233/256:ℝ) (192445745779/10000000000:ℝ) (297329/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1398).1
  intro u hu
  exact (show (16248401359171/1000000000000000000:ℝ) ≤ (1/4-6*(192445745779/10000000000:ℝ)+4*(192445745779/10000000000:ℝ)^2)*(297329/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_233 :
    ∀ u ∈ Set.Icc (233/256:ℝ) (117/128:ℝ), (14212279360473/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (96977556043/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(233/256:ℝ)) := by
    calc
      (96977556043/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(233/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(233/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (233/256:ℝ) (117/128:ℝ) (96977556043/5000000000:ℝ) (511741/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1404).1
  intro u hu
  exact (show (14212279360473/1000000000000000000:ℝ) ≤ (1/4-6*(96977556043/5000000000:ℝ)+4*(96977556043/5000000000:ℝ)^2)*(511741/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_234 :
    ∀ u ∈ Set.Icc (117/128:ℝ) (235/256:ℝ), (1552051974267/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (1527158721/78125000:ℝ) ≤ Real.pi*Real.exp (2*(117/128:ℝ)) := by
    calc
      (1527158721/78125000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(117/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(117/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (117/128:ℝ) (235/256:ℝ) (1527158721/78125000:ℝ) (879721/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1410).1
  intro u hu
  exact (show (1552051974267/125000000000000000:ℝ) ≤ (1/4-6*(1527158721/78125000:ℝ)+4*(1527158721/78125000:ℝ)^2)*(879721/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_235 :
    ∀ u ∈ Set.Icc (235/256:ℝ) (59/64:ℝ), (5417188802421/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (197009451221/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(235/256:ℝ)) := by
    calc
      (197009451221/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(235/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(235/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (235/256:ℝ) (59/64:ℝ) (197009451221/10000000000:ℝ) (188811/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1416).1
  intro u hu
  exact (show (5417188802421/500000000000000000:ℝ) ≤ (1/4-6*(197009451221/10000000000:ℝ)+4*(197009451221/10000000000:ℝ)^2)*(188811/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_236 :
    ∀ u ∈ Set.Icc (59/64:ℝ) (237/256:ℝ), (2360604497989/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (3971092209/200000000:ℝ) ≤ Real.pi*Real.exp (2*(59/64:ℝ)) := by
    calc
      (3971092209/200000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(59/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(59/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (59/64:ℝ) (237/256:ℝ) (3971092209/200000000:ℝ) (129519/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1422).1
  intro u hu
  exact (show (2360604497989/250000000000000000:ℝ) ≤ (1/4-6*(3971092209/200000000:ℝ)+4*(3971092209/200000000:ℝ)^2)*(129519/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_237 :
    ∀ u ∈ Set.Icc (237/256:ℝ) (119/128:ℝ), (8219203312331/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (12506993017/625000000:ℝ) ≤ Real.pi*Real.exp (2*(237/256:ℝ)) := by
    calc
      (12506993017/625000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(237/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(237/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (237/256:ℝ) (119/128:ℝ) (12506993017/625000000:ℝ) (138653/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1428).1
  intro u hu
  exact (show (8219203312331/1000000000000000000:ℝ) ≤ (1/4-6*(12506993017/625000000:ℝ)+4*(12506993017/625000000:ℝ)^2)*(138653/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_238 :
    ∀ u ∈ Set.Icc (119/128:ℝ) (239/256:ℝ), (1786401178299/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (50420344931/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(119/128:ℝ)) := by
    calc
      (50420344931/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(119/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(119/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (119/128:ℝ) (239/256:ℝ) (50420344931/2500000000:ℝ) (94879/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1434).1
  intro u hu
  exact (show (1786401178299/250000000000000000:ℝ) ≤ (1/4-6*(50420344931/2500000000:ℝ)+4*(50420344931/2500000000:ℝ)^2)*(94879/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_239 :
    ∀ u ∈ Set.Icc (239/256:ℝ) (15/16:ℝ), (155112952199/25000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (50815795147/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(239/256:ℝ)) := by
    calc
      (50815795147/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(239/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(239/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (239/256:ℝ) (15/16:ℝ) (50815795147/2500000000:ℝ) (202639/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1440).1
  intro u hu
  exact (show (155112952199/25000000000000000:ℝ) ≤ (1/4-6*(50815795147/2500000000:ℝ)+4*(50815795147/2500000000:ℝ)^2)*(202639/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_240 :
    ∀ u ∈ Set.Icc (15/16:ℝ) (241/256:ℝ), (5380608354027/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (204857387397/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/16:ℝ)) := by
    calc
      (204857387397/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(15/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(15/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (15/16:ℝ) (241/256:ℝ) (204857387397/10000000000:ℝ) (172899/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1446).1
  intro u hu
  exact (show (5380608354027/1000000000000000000:ℝ) ≤ (1/4-6*(204857387397/10000000000:ℝ)+4*(204857387397/10000000000:ℝ)^2)*(172899/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_241 :
    ∀ u ∈ Set.Icc (241/256:ℝ) (121/128:ℝ), (582524031463/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (1290400609/62500000:ℝ) ≤ Real.pi*Real.exp (2*(241/256:ℝ)) := by
    calc
      (1290400609/62500000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(241/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(241/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (241/256:ℝ) (121/128:ℝ) (1290400609/62500000:ℝ) (11787/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1452).1
  intro u hu
  exact (show (582524031463/125000000000000000:ℝ) ≤ (1/4-6*(1290400609/62500000:ℝ)+4*(1290400609/62500000:ℝ)^2)*(11787/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_242 :
    ∀ u ∈ Set.Icc (121/128:ℝ) (243/256:ℝ), (2015550292363/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (208083408769/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/128:ℝ)) := by
    calc
      (208083408769/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(121/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(121/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (121/128:ℝ) (243/256:ℝ) (208083408769/10000000000:ℝ) (31349/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1458).1
  intro u hu
  exact (show (2015550292363/500000000000000000:ℝ) ≤ (1/4-6*(208083408769/10000000000:ℝ)+4*(208083408769/10000000000:ℝ)^2)*(31349/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_243 :
    ∀ u ∈ Set.Icc (243/256:ℝ) (61/64:ℝ), (3482453219147/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (52428855051/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(243/256:ℝ)) := by
    calc
      (52428855051/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(243/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(243/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (243/256:ℝ) (61/64:ℝ) (52428855051/2500000000:ℝ) (213171/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1464).1
  intro u hu
  exact (show (3482453219147/1000000000000000000:ℝ) ≤ (1/4-6*(52428855051/2500000000:ℝ)+4*(52428855051/2500000000:ℝ)^2)*(213171/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_244 :
    ∀ u ∈ Set.Icc (61/64:ℝ) (245/256:ℝ), (3004587016079/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (211360231341/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/64:ℝ)) := by
    calc
      (211360231341/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(61/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(61/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (61/64:ℝ) (245/256:ℝ) (211360231341/10000000000:ℝ) (1131/625000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1470).1
  intro u hu
  exact (show (3004587016079/1000000000000000000:ℝ) ≤ (1/4-6*(211360231341/10000000000:ℝ)+4*(211360231341/10000000000:ℝ)^2)*(1131/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_245 :
    ∀ u ∈ Set.Icc (245/256:ℝ) (123/128:ℝ), (647229882051/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (53254485639/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(245/256:ℝ)) := by
    calc
      (53254485639/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(245/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(245/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (245/256:ℝ) (123/128:ℝ) (53254485639/2500000000:ℝ) (153417/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1476).1
  intro u hu
  exact (show (647229882051/250000000000000000:ℝ) ≤ (1/4-6*(53254485639/2500000000:ℝ)+4*(53254485639/2500000000:ℝ)^2)*(153417/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_246 :
    ∀ u ∈ Set.Icc (123/128:ℝ) (247/256:ℝ), (445562075193/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (214688655011/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/128:ℝ)) := by
    calc
      (214688655011/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(123/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(123/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (123/128:ℝ) (247/256:ℝ) (214688655011/10000000000:ℝ) (25979/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1482).1
  intro u hu
  exact (show (445562075193/200000000000000000:ℝ) ≤ (1/4-6*(214688655011/10000000000:ℝ)+4*(214688655011/10000000000:ℝ)^2)*(25979/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_247 :
    ∀ u ∈ Set.Icc (247/256:ℝ) (31/32:ℝ), (1914543067207/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (216372470661/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(247/256:ℝ)) := by
    calc
      (216372470661/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(247/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(247/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (247/256:ℝ) (31/32:ℝ) (216372470661/10000000000:ℝ) (21967/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1488).1
  intro u hu
  exact (show (1914543067207/1000000000000000000:ℝ) ≤ (1/4-6*(216372470661/10000000000:ℝ)+4*(216372470661/10000000000:ℝ)^2)*(21967/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_248 :
    ∀ u ∈ Set.Icc (31/32:ℝ) (249/256:ℝ), (1643123144931/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (218069492261/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/32:ℝ)) := by
    calc
      (218069492261/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(31/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(31/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (31/32:ℝ) (249/256:ℝ) (218069492261/10000000000:ℝ) (92749/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1494).1
  intro u hu
  exact (show (1643123144931/1000000000000000000:ℝ) ≤ (1/4-6*(218069492261/10000000000:ℝ)+4*(218069492261/10000000000:ℝ)^2)*(92749/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_249 :
    ∀ u ∈ Set.Icc (249/256:ℝ) (125/128:ℝ), (1408286069707/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (219779823371/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(249/256:ℝ)) := by
    calc
      (219779823371/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(249/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(249/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (249/256:ℝ) (125/128:ℝ) (219779823371/10000000000:ℝ) (9777/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1500).1
  intro u hu
  exact (show (1408286069707/1000000000000000000:ℝ) ≤ (1/4-6*(219779823371/10000000000:ℝ)+4*(219779823371/10000000000:ℝ)^2)*(9777/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_250 :
    ∀ u ∈ Set.Icc (125/128:ℝ) (251/256:ℝ), (301343536891/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (110751784181/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(125/128:ℝ)) := by
    calc
      (110751784181/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(125/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(125/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (125/128:ℝ) (251/256:ℝ) (110751784181/5000000000:ℝ) (65871/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1506).1
  intro u hu
  exact (show (301343536891/250000000000000000:ℝ) ≤ (1/4-6*(110751784181/5000000000:ℝ)+4*(110751784181/5000000000:ℝ)^2)*(65871/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_251 :
    ∀ u ∈ Set.Icc (251/256:ℝ) (63/64:ℝ), (2060581617/2000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (8929633297/400000000:ℝ) ≤ Real.pi*Real.exp (2*(251/256:ℝ)) := by
    calc
      (8929633297/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(251/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(251/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (251/256:ℝ) (63/64:ℝ) (8929633297/400000000:ℝ) (55399/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1512).1
  intro u hu
  exact (show (2060581617/2000000000000000:ℝ) ≤ (1/4-6*(8929633297/400000000:ℝ)+4*(8929633297/400000000:ℝ)^2)*(55399/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_252 :
    ∀ u ∈ Set.Icc (63/64:ℝ) (253/256:ℝ), (439714250091/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (56247930393/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(63/64:ℝ)) := by
    calc
      (56247930393/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(63/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(63/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (63/64:ℝ) (253/256:ℝ) (56247930393/2500000000:ℝ) (727/1562500000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1518).1
  intro u hu
  exact (show (439714250091/500000000000000000:ℝ) ≤ (1/4-6*(56247930393/2500000000:ℝ)+4*(56247930393/2500000000:ℝ)^2)*(727/1562500000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_253 :
    ∀ u ∈ Set.Icc (253/256:ℝ) (127/128:ℝ), (149921195583/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (226756342649/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(253/256:ℝ)) := by
    calc
      (226756342649/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(253/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(253/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (253/256:ℝ) (127/128:ℝ) (226756342649/10000000000:ℝ) (39023/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1524).1
  intro u hu
  exact (show (149921195583/200000000000000000:ℝ) ≤ (1/4-6*(226756342649/10000000000:ℝ)+4*(226756342649/10000000000:ℝ)^2)*(39023/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_254 :
    ∀ u ∈ Set.Icc (127/128:ℝ) (255/256:ℝ), (39878476441/62500000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (114267401669/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(127/128:ℝ)) := by
    calc
      (114267401669/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(127/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(127/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (127/128:ℝ) (255/256:ℝ) (114267401669/5000000000:ℝ) (32683/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1530).1
  intro u hu
  exact (show (39878476441/62500000000000000:ℝ) ≤ (1/4-6*(114267401669/5000000000:ℝ)+4*(114267401669/5000000000:ℝ)^2)*(32683/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_255 :
    ∀ u ∈ Set.Icc (255/256:ℝ) (1/1:ℝ), (108469580301/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (46065442433/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(255/256:ℝ)) := by
    calc
      (46065442433/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(255/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(255/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (255/256:ℝ) (1/1:ℝ) (46065442433/2000000000:ℝ) (5467/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1536).1
  intro u hu
  exact (show (108469580301/200000000000000000:ℝ) ≤ (1/4-6*(46065442433/2000000000:ℝ)+4*(46065442433/2000000000:ℝ)^2)*(5467/20000000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

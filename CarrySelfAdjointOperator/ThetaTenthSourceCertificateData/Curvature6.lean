import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_192 :
    ∀ u ∈ Set.Icc (3/4:ℝ) (193/256:ℝ), (14208294001147/10000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (14079637569/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/4:ℝ)) := by
    calc
      (14079637569/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/4:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/4:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/4:ℝ) (193/256:ℝ) (14079637569/1000000000:ℝ) (40095821/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1158).1
  intro u hu
  exact (show (14208294001147/10000000000000000:ℝ) ≤ (1/4-6*(14079637569/1000000000:ℝ)+4*(14079637569/1000000000:ℝ)^2)*(40095821/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_193 :
    ∀ u ∈ Set.Icc (193/256:ℝ) (97/128:ℝ), (323729221238183/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (141900654801/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(193/256:ℝ)) := by
    calc
      (141900654801/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(193/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(193/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (193/256:ℝ) (97/128:ℝ) (141900654801/10000000000:ℝ) (89857211/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1164).1
  intro u hu
  exact (show (323729221238183/250000000000000000:ℝ) ≤ (1/4-6*(141900654801/10000000000:ℝ)+4*(141900654801/10000000000:ℝ)^2)*(89857211/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_194 :
    ∀ u ∈ Set.Icc (97/128:ℝ) (195/256:ℝ), (589561754626943/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (143013594849/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/128:ℝ)) := by
    calc
      (143013594849/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(97/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(97/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (97/128:ℝ) (195/256:ℝ) (143013594849/10000000000:ℝ) (32191977/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1170).1
  intro u hu
  exact (show (589561754626943/500000000000000000:ℝ) ≤ (1/4-6*(143013594849/10000000000:ℝ)+4*(143013594849/10000000000:ℝ)^2)*(32191977/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_195 :
    ∀ u ∈ Set.Icc (195/256:ℝ) (49/64:ℝ), (536365970577363/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (144135263759/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(195/256:ℝ)) := by
    calc
      (144135263759/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(195/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(195/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (195/256:ℝ) (49/64:ℝ) (144135263759/10000000000:ℝ) (28807151/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1176).1
  intro u hu
  exact (show (536365970577363/500000000000000000:ℝ) ≤ (1/4-6*(144135263759/10000000000:ℝ)+4*(144135263759/10000000000:ℝ)^2)*(28807151/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_196 :
    ∀ u ∈ Set.Icc (49/64:ℝ) (197/256:ℝ), (975067464150909/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (145265729993/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/64:ℝ)) := by
    calc
      (145265729993/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(49/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(49/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (49/64:ℝ) (197/256:ℝ) (145265729993/10000000000:ℝ) (128776883/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1182).1
  intro u hu
  exact (show (975067464150909/1000000000000000000:ℝ) ≤ (1/4-6*(145265729993/10000000000:ℝ)+4*(145265729993/10000000000:ℝ)^2)*(128776883/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_197 :
    ∀ u ∈ Set.Icc (197/256:ℝ) (99/128:ℝ), (885496145229559/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (29281012509/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(197/256:ℝ)) := by
    calc
      (29281012509/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(197/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(197/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (197/256:ℝ) (99/128:ℝ) (29281012509/2000000000:ℝ) (11503167/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1188).1
  intro u hu
  exact (show (885496145229559/1000000000000000000:ℝ) ≤ (1/4-6*(29281012509/2000000000:ℝ)+4*(29281012509/2000000000:ℝ)^2)*(11503167/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_198 :
    ∀ u ∈ Set.Icc (99/128:ℝ) (199/256:ℝ), (100427867549897/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (147553330953/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/128:ℝ)) := by
    calc
      (147553330953/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(99/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(99/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (99/128:ℝ) (199/256:ℝ) (147553330953/10000000000:ℝ) (102661077/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1194).1
  intro u hu
  exact (show (100427867549897/125000000000000000:ℝ) ≤ (1/4-6*(147553330953/10000000000:ℝ)+4*(147553330953/10000000000:ℝ)^2)*(102661077/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_199 :
    ∀ u ∈ Set.Icc (199/256:ℝ) (25/32:ℝ), (36414495119801/50000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (148710605301/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(199/256:ℝ)) := by
    calc
      (148710605301/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(199/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(199/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (199/256:ℝ) (25/32:ℝ) (148710605301/10000000000:ℝ) (11442213/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1200).1
  intro u hu
  exact (show (36414495119801/50000000000000000:ℝ) ≤ (1/4-6*(148710605301/10000000000:ℝ)+4*(148710605301/10000000000:ℝ)^2)*(11442213/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_200 :
    ∀ u ∈ Set.Icc (25/32:ℝ) (201/256:ℝ), (659574402541617/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (7493847811/500000000:ℝ) ≤ Real.pi*Real.exp (2*(25/32:ℝ)) := by
    calc
      (7493847811/500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(25/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(25/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (25/32:ℝ) (201/256:ℝ) (7493847811/500000000:ℝ) (81544923/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1206).1
  intro u hu
  exact (show (659574402541617/1000000000000000000:ℝ) ≤ (1/4-6*(7493847811/500000000:ℝ)+4*(7493847811/500000000:ℝ)^2)*(81544923/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_201 :
    ∀ u ∈ Set.Icc (201/256:ℝ) (101/128:ℝ), (298393710712757/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (151052454897/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(201/256:ℝ)) := by
    calc
      (151052454897/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(201/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(201/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (201/256:ℝ) (101/128:ℝ) (151052454897/10000000000:ℝ) (72576069/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1212).1
  intro u hu
  exact (show (298393710712757/500000000000000000:ℝ) ≤ (1/4-6*(151052454897/10000000000:ℝ)+4*(151052454897/10000000000:ℝ)^2)*(72576069/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_202 :
    ∀ u ∈ Set.Icc (101/128:ℝ) (203/256:ℝ), (539471835378099/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (6089486923/400000000:ℝ) ≤ Real.pi*Real.exp (2*(101/128:ℝ)) := by
    calc
      (6089486923/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(101/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(101/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (101/128:ℝ) (203/256:ℝ) (6089486923/400000000:ℝ) (64533677/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1218).1
  intro u hu
  exact (show (539471835378099/1000000000000000000:ℝ) ≤ (1/4-6*(6089486923/400000000:ℝ)+4*(6089486923/400000000:ℝ)^2)*(64533677/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_203 :
    ∀ u ∈ Set.Icc (203/256:ℝ) (51/64:ℝ), (12180020474541/25000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (153431183063/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(203/256:ℝ)) := by
    calc
      (153431183063/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(203/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(203/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (203/256:ℝ) (51/64:ℝ) (153431183063/10000000000:ℝ) (57328777/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1224).1
  intro u hu
  exact (show (12180020474541/25000000000000000:ℝ) ≤ (1/4-6*(153431183063/10000000000:ℝ)+4*(153431183063/10000000000:ℝ)^2)*(57328777/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_204 :
    ∀ u ∈ Set.Icc (51/64:ℝ) (205/256:ℝ), (54947028858241/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (77317278867/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/64:ℝ)) := by
    calc
      (77317278867/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(51/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(51/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (51/64:ℝ) (205/256:ℝ) (77317278867/5000000000:ℝ) (12720057/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1230).1
  intro u hu
  exact (show (54947028858241/125000000000000000:ℝ) ≤ (1/4-6*(77317278867/5000000000:ℝ)+4*(77317278867/5000000000:ℝ)^2)*(12720057/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_205 :
    ∀ u ∈ Set.Icc (205/256:ℝ) (103/128:ℝ), (396227085824353/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (155847370533/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(205/256:ℝ)) := by
    calc
      (155847370533/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(205/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(205/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (205/256:ℝ) (103/128:ℝ) (155847370533/10000000000:ℝ) (45114101/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1236).1
  intro u hu
  exact (show (396227085824353/1000000000000000000:ℝ) ≤ (1/4-6*(155847370533/10000000000:ℝ)+4*(155847370533/10000000000:ℝ)^2)*(45114101/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_206 :
    ∀ u ∈ Set.Icc (103/128:ℝ) (207/256:ℝ), (22300504829651/62500000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (78534847741/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/128:ℝ)) := by
    calc
      (78534847741/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(103/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(103/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (103/128:ℝ) (207/256:ℝ) (78534847741/5000000000:ℝ) (1248847/3125000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1242).1
  intro u hu
  exact (show (22300504829651/62500000000000000:ℝ) ≤ (1/4-6*(78534847741/5000000000:ℝ)+4*(78534847741/5000000000:ℝ)^2)*(1248847/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_207 :
    ∀ u ∈ Set.Icc (207/256:ℝ) (13/16:ℝ), (80249536094603/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (79150803591/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(207/256:ℝ)) := by
    calc
      (79150803591/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(207/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(207/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (207/256:ℝ) (13/16:ℝ) (79150803591/5000000000:ℝ) (17683023/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1248).1
  intro u hu
  exact (show (80249536094603/250000000000000000:ℝ) ≤ (1/4-6*(79150803591/5000000000:ℝ)+4*(79150803591/5000000000:ℝ)^2)*(17683023/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_208 :
    ∀ u ∈ Set.Icc (13/16:ℝ) (209/256:ℝ), (28849907635213/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (159543180821/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/16:ℝ)) := by
    calc
      (159543180821/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(13/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(13/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (13/16:ℝ) (209/256:ℝ) (159543180821/10000000000:ℝ) (31267337/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1254).1
  intro u hu
  exact (show (28849907635213/100000000000000000:ℝ) ≤ (1/4-6*(159543180821/10000000000:ℝ)+4*(159543180821/10000000000:ℝ)^2)*(31267337/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_209 :
    ∀ u ∈ Set.Icc (209/256:ℝ) (105/128:ℝ), (25903420067651/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (6431779687/400000000:ℝ) ≤ Real.pi*Real.exp (2*(209/256:ℝ)) := by
    calc
      (6431779687/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(209/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(209/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (209/256:ℝ) (105/128:ℝ) (6431779687/400000000:ℝ) (27616527/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1260).1
  intro u hu
  exact (show (25903420067651/100000000000000000:ℝ) ≤ (1/4-6*(6431779687/400000000:ℝ)+4*(6431779687/400000000:ℝ)^2)*(27616527/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_210 :
    ∀ u ∈ Set.Icc (105/128:ℝ) (211/256:ℝ), (232347092922457/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (162055617613/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/128:ℝ)) := by
    calc
      (162055617613/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(105/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(105/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (105/128:ℝ) (211/256:ℝ) (162055617613/10000000000:ℝ) (194943/800000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1266).1
  intro u hu
  exact (show (232347092922457/1000000000000000000:ℝ) ≤ (1/4-6*(162055617613/10000000000:ℝ)+4*(162055617613/10000000000:ℝ)^2)*(194943/800000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_211 :
    ∀ u ∈ Set.Icc (211/256:ℝ) (53/64:ℝ), (26025045292513/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (81663317053/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(211/256:ℝ)) := by
    calc
      (81663317053/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(211/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(211/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (211/256:ℝ) (53/64:ℝ) (81663317053/5000000000:ℝ) (1342497/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1272).1
  intro u hu
  exact (show (26025045292513/125000000000000000:ℝ) ≤ (1/4-6*(81663317053/5000000000:ℝ)+4*(81663317053/5000000000:ℝ)^2)*(1342497/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_212 :
    ∀ u ∈ Set.Icc (53/64:ℝ) (213/256:ℝ), (46593623740507/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (82303809613/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/64:ℝ)) := by
    calc
      (82303809613/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(53/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(53/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (53/64:ℝ) (213/256:ℝ) (82303809613/5000000000:ℝ) (9457637/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1278).1
  intro u hu
  exact (show (46593623740507/250000000000000000:ℝ) ≤ (1/4-6*(82303809613/5000000000:ℝ)+4*(82303809613/5000000000:ℝ)^2)*(9457637/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_213 :
    ∀ u ∈ Set.Icc (213/256:ℝ) (107/128:ℝ), (41666673119801/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (33179730231/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(213/256:ℝ)) := by
    calc
      (33179730231/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(213/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(213/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (213/256:ℝ) (107/128:ℝ) (33179730231/2000000000:ℝ) (16639957/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1284).1
  intro u hu
  exact (show (41666673119801/250000000000000000:ℝ) ≤ (1/4-6*(33179730231/2000000000:ℝ)+4*(33179730231/2000000000:ℝ)^2)*(16639957/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_214 :
    ∀ u ∈ Set.Icc (107/128:ℝ) (215/256:ℝ), (74444924862353/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (83599904343/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/128:ℝ)) := by
    calc
      (83599904343/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(107/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(107/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (107/128:ℝ) (215/256:ℝ) (83599904343/5000000000:ℝ) (14623407/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1290).1
  intro u hu
  exact (show (74444924862353/500000000000000000:ℝ) ≤ (1/4-6*(83599904343/5000000000:ℝ)+4*(83599904343/5000000000:ℝ)^2)*(14623407/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_215 :
    ∀ u ∈ Set.Icc (215/256:ℝ) (27/32:ℝ), (33217875238267/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (5265974101/312500000:ℝ) ≤ Real.pi*Real.exp (2*(215/256:ℝ)) := by
    calc
      (5265974101/312500000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(215/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(215/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (215/256:ℝ) (27/32:ℝ) (5265974101/312500000:ℝ) (6419013/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1296).1
  intro u hu
  exact (show (33217875238267/250000000000000000:ℝ) ≤ (1/4-6*(5265974101/312500000:ℝ)+4*(5265974101/312500000:ℝ)^2)*(6419013/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_216 :
    ∀ u ∈ Set.Icc (27/32:ℝ) (217/256:ℝ), (118452877704869/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (169832818827/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/32:ℝ)) := by
    calc
      (169832818827/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(27/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(27/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (27/32:ℝ) (217/256:ℝ) (169832818827/10000000000:ℝ) (11258947/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1302).1
  intro u hu
  exact (show (118452877704869/1000000000000000000:ℝ) ≤ (1/4-6*(169832818827/10000000000:ℝ)+4*(169832818827/10000000000:ℝ)^2)*(11258947/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_217 :
    ∀ u ∈ Set.Icc (217/256:ℝ) (109/128:ℝ), (1054879510589/10000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (171164832133/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(217/256:ℝ)) := by
    calc
      (171164832133/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(217/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(217/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (217/256:ℝ) (109/128:ℝ) (171164832133/10000000000:ℝ) (1232973/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1308).1
  intro u hu
  exact (show (1054879510589/10000000000000000:ℝ) ≤ (1/4-6*(171164832133/10000000000:ℝ)+4*(171164832133/10000000000:ℝ)^2)*(1232973/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_218 :
    ∀ u ∈ Set.Icc (109/128:ℝ) (219/256:ℝ), (93842617334969/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (43126823111/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(109/128:ℝ)) := by
    calc
      (43126823111/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(109/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(109/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (109/128:ℝ) (219/256:ℝ) (43126823111/2500000000:ℝ) (8632411/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1314).1
  intro u hu
  exact (show (93842617334969/1000000000000000000:ℝ) ≤ (1/4-6*(43126823111/2500000000:ℝ)+4*(43126823111/2500000000:ℝ)^2)*(8632411/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_219 :
    ∀ u ∈ Set.Icc (219/256:ℝ) (55/64:ℝ), (16678757434983/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (86930140847/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(219/256:ℝ)) := by
    calc
      (86930140847/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(219/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(219/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (219/256:ℝ) (55/64:ℝ) (86930140847/5000000000:ℝ) (3773373/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1320).1
  intro u hu
  exact (show (16678757434983/200000000000000000:ℝ) ≤ (1/4-6*(86930140847/5000000000:ℝ)+4*(86930140847/5000000000:ℝ)^2)*(3773373/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_220 :
    ∀ u ∈ Set.Icc (55/64:ℝ) (221/256:ℝ), (37014350035403/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (21902985307/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(55/64:ℝ)) := by
    calc
      (21902985307/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(55/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(55/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (55/64:ℝ) (221/256:ℝ) (21902985307/1250000000:ℝ) (6590569/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1326).1
  intro u hu
  exact (show (37014350035403/500000000000000000:ℝ) ≤ (1/4-6*(21902985307/1250000000:ℝ)+4*(21902985307/1250000000:ℝ)^2)*(6590569/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_221 :
    ∀ u ∈ Set.Icc (221/256:ℝ) (111/128:ℝ), (410275687759/6250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (176598177951/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(221/256:ℝ)) := by
    calc
      (176598177951/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(221/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(221/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (221/256:ℝ) (111/128:ℝ) (176598177951/10000000000:ℝ) (287467/5000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1332).1
  intro u hu
  exact (show (410275687759/6250000000000000:ℝ) ≤ (1/4-6*(176598177951/10000000000:ℝ)+4*(176598177951/10000000000:ℝ)^2)*(287467/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_222 :
    ∀ u ∈ Set.Icc (111/128:ℝ) (223/256:ℝ), (11629122491573/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (35596650411/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/128:ℝ)) := by
    calc
      (35596650411/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(111/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(111/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (111/128:ℝ) (223/256:ℝ) (35596650411/2000000000:ℝ) (5010041/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1338).1
  intro u hu
  exact (show (11629122491573/200000000000000000:ℝ) ≤ (1/4-6*(35596650411/2000000000:ℝ)+4*(35596650411/2000000000:ℝ)^2)*(5010041/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_223 :
    ∀ u ∈ Set.Icc (223/256:ℝ) (7/8:ℝ), (6430874207139/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (179379189299/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(223/256:ℝ)) := by
    calc
      (179379189299/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(223/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(223/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (223/256:ℝ) (7/8:ℝ) (179379189299/10000000000:ℝ) (436103/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1344).1
  intro u hu
  exact (show (6430874207139/125000000000000000:ℝ) ≤ (1/4-6*(179379189299/10000000000:ℝ)+4*(179379189299/10000000000:ℝ)^2)*(436103/10000000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

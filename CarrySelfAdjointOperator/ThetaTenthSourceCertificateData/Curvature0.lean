import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_000 :
    ∀ u ∈ Set.Icc (0/1:ℝ) (1/256:ℝ), (882017793809669459/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (392699/125000:ℝ) ≤ Real.pi*Real.exp (2*(0/1:ℝ)) := by
    calc
      (392699/125000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(0/1:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(0/1:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (0/1:ℝ) (1/256:ℝ) (392699/125000:ℝ) (8448911971117/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0006).1
  intro u hu
  exact (show (882017793809669459/500000000000000000:ℝ) ≤ (1/4-6*(392699/125000:ℝ)+4*(392699/125000:ℝ)^2)*(8448911971117/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_001 :
    ∀ u ∈ Set.Icc (1/256:ℝ) (1/128:ℝ), (1763262794674044371/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (15831159057/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/256:ℝ)) := by
    calc
      (15831159057/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/256:ℝ) (1/128:ℝ) (15831159057/5000000000:ℝ) (4128898006789/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0012).1
  intro u hu
  exact (show (1763262794674044371/1000000000000000000:ℝ) ≤ (1/4-6*(15831159057/5000000000:ℝ)+4*(15831159057/5000000000:ℝ)^2)*(4128898006789/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_002 :
    ∀ u ∈ Set.Icc (1/128:ℝ) (3/256:ℝ), (176197573183638029/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (31910648753/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/128:ℝ)) := by
    calc
      (31910648753/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/128:ℝ) (3/256:ℝ) (31910648753/10000000000:ℝ) (322777252513/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0018).1
  intro u hu
  exact (show (176197573183638029/100000000000000000:ℝ) ≤ (1/4-6*(31910648753/10000000000:ℝ)+4*(31910648753/10000000000:ℝ)^2)*(322777252513/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_003 :
    ∀ u ∈ Set.Icc (3/256:ℝ) (1/64:ℝ), (176017638148269469/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (32160927073/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/256:ℝ)) := by
    calc
      (32160927073/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/256:ℝ) (1/64:ℝ) (32160927073/10000000000:ℝ) (3941907799509/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0024).1
  intro u hu
  exact (show (176017638148269469/100000000000000000:ℝ) ≤ (1/4-6*(32160927073/10000000000:ℝ)+4*(32160927073/10000000000:ℝ)^2)*(3941907799509/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_004 :
    ∀ u ∈ Set.Icc (1/64:ℝ) (5/256:ℝ), (351573408933338897/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (648263367/200000000:ℝ) ≤ Real.pi*Real.exp (2*(1/64:ℝ)) := by
    calc
      (648263367/200000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/64:ℝ) (5/256:ℝ) (648263367/200000000:ℝ) (3850472904461/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0030).1
  intro u hu
  exact (show (351573408933338897/200000000000000000:ℝ) ≤ (1/4-6*(648263367/200000000:ℝ)+4*(648263367/200000000:ℝ)^2)*(3850472904461/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_005 :
    ∀ u ∈ Set.Icc (5/256:ℝ) (3/128:ℝ), (219381292635168023/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (1633369399/500000000:ℝ) ≤ Real.pi*Real.exp (2*(5/256:ℝ)) := by
    calc
      (1633369399/500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(5/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(5/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (5/256:ℝ) (3/128:ℝ) (1633369399/500000000:ℝ) (1880204522387/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0036).1
  intro u hu
  exact (show (219381292635168023/125000000000000000:ℝ) ≤ (1/4-6*(1633369399/500000000:ℝ)+4*(1633369399/500000000:ℝ)^2)*(1880204522387/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_006 :
    ∀ u ∈ Set.Icc (3/128:ℝ) (7/256:ℝ), (875864604429554181/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (823090037/250000000:ℝ) ≤ Real.pi*Real.exp (2*(3/128:ℝ)) := by
    calc
      (823090037/250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/128:ℝ) (7/256:ℝ) (823090037/250000000:ℝ) (1835856950571/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0042).1
  intro u hu
  exact (show (875864604429554181/500000000000000000:ℝ) ≤ (1/4-6*(823090037/250000000:ℝ)+4*(823090037/250000000:ℝ)^2)*(1835856950571/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_007 :
    ∀ u ∈ Set.Icc (7/256:ℝ) (1/32:ℝ), (873953451803742743/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (16590912243/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/256:ℝ)) := by
    calc
      (16590912243/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(7/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(7/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (7/256:ℝ) (1/32:ℝ) (16590912243/5000000000:ℝ) (448048095471/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0048).1
  intro u hu
  exact (show (873953451803742743/500000000000000000:ℝ) ≤ (1/4-6*(16590912243/5000000000:ℝ)+4*(16590912243/5000000000:ℝ)^2)*(448048095471/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_008 :
    ∀ u ∈ Set.Icc (1/32:ℝ) (9/256:ℝ), (871793499300891957/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (33442072761/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/32:ℝ)) := by
    calc
      (33442072761/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/32:ℝ) (9/256:ℝ) (33442072761/10000000000:ℝ) (3498418534927/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0054).1
  intro u hu
  exact (show (871793499300891957/500000000000000000:ℝ) ≤ (1/4-6*(33442072761/10000000000:ℝ)+4*(33442072761/10000000000:ℝ)^2)*(3498418534927/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_009 :
    ∀ u ∈ Set.Icc (9/256:ℝ) (5/128:ℝ), (1738773382538984943/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (33704362189/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/256:ℝ)) := by
    calc
      (33704362189/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(9/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(9/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (9/256:ℝ) (5/128:ℝ) (33704362189/10000000000:ℝ) (1365524692699/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0060).1
  intro u hu
  exact (show (1738773382538984943/1000000000000000000:ℝ) ≤ (1/4-6*(33704362189/10000000000:ℝ)+4*(33704362189/10000000000:ℝ)^2)*(1365524692699/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_010 :
    ∀ u ∈ Set.Icc (5/128:ℝ) (11/256:ℝ), (433367564585813153/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (16984354389/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/128:ℝ)) := by
    calc
      (16984354389/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(5/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(5/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (5/128:ℝ) (11/256:ℝ) (16984354389/5000000000:ℝ) (3330560489303/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0066).1
  intro u hu
  exact (show (433367564585813153/250000000000000000:ℝ) ≤ (1/4-6*(16984354389/5000000000:ℝ)+4*(16984354389/5000000000:ℝ)^2)*(3330560489303/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_011 :
    ∀ u ∈ Set.Icc (11/256:ℝ) (3/64:ℝ), (107980133847500327/62500000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (34235128663/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/256:ℝ)) := by
    calc
      (34235128663/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(11/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(11/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (11/256:ℝ) (3/64:ℝ) (34235128663/10000000000:ℝ) (6497321127709/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0072).1
  intro u hu
  exact (show (107980133847500327/62500000000000000:ℝ) ≤ (1/4-6*(34235128663/10000000000:ℝ)+4*(34235128663/10000000000:ℝ)^2)*(6497321127709/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_012 :
    ∀ u ∈ Set.Icc (3/64:ℝ) (13/256:ℝ), (430353464465377497/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (6900727621/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/64:ℝ)) := by
    calc
      (6900727621/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/64:ℝ) (13/256:ℝ) (6900727621/2000000000:ℝ) (316810733639/5000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0078).1
  intro u hu
  exact (show (430353464465377497/250000000000000000:ℝ) ≤ (1/4-6*(6900727621/2000000000:ℝ)+4*(6900727621/2000000000:ℝ)^2)*(316810733639/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_013 :
    ∀ u ∈ Set.Icc (13/256:ℝ) (7/128:ℝ), (1714670540522423867/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (8693563373/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(13/256:ℝ)) := by
    calc
      (8693563373/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(13/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(13/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (13/256:ℝ) (7/128:ℝ) (8693563373/2500000000:ℝ) (3088895816439/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0084).1
  intro u hu
  exact (show (1714670540522423867/1000000000000000000:ℝ) ≤ (1/4-6*(8693563373/2500000000:ℝ)+4*(8693563373/2500000000:ℝ)^2)*(3088895816439/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_014 :
    ∀ u ∈ Set.Icc (7/128:ℝ) (15/256:ℝ), (106716101744309517/62500000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (35046991343/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/128:ℝ)) := by
    calc
      (35046991343/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(7/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(7/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (7/128:ℝ) (15/256:ℝ) (35046991343/10000000000:ℝ) (6022041292103/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0090).1
  intro u hu
  exact (show (106716101744309517/62500000000000000:ℝ) ≤ (1/4-6*(35046991343/10000000000:ℝ)+4*(35046991343/10000000000:ℝ)^2)*(6022041292103/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_015 :
    ∀ u ∈ Set.Icc (15/256:ℝ) (1/16:ℝ), (1699780859421808009/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (35321868303/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/256:ℝ)) := by
    calc
      (35321868303/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(15/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(15/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (15/256:ℝ) (1/16:ℝ) (35321868303/10000000000:ℝ) (73361902601/1250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0096).1
  intro u hu
  exact (show (1699780859421808009/1000000000000000000:ℝ) ≤ (1/4-6*(35321868303/10000000000:ℝ)+4*(35321868303/10000000000:ℝ)^2)*(73361902601/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_016 :
    ∀ u ∈ Set.Icc (1/16:ℝ) (17/256:ℝ), (1691646272594122039/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (35598901149/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/16:ℝ)) := by
    calc
      (35598901149/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/16:ℝ) (17/256:ℝ) (35598901149/10000000000:ℝ) (2859256110477/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0102).1
  intro u hu
  exact (show (1691646272594122039/1000000000000000000:ℝ) ≤ (1/4-6*(35598901149/10000000000:ℝ)+4*(35598901149/10000000000:ℝ)^2)*(2859256110477/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_017 :
    ∀ u ∈ Set.Icc (17/256:ℝ) (9/128:ℝ), (841530099567674249/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (35878106791/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/256:ℝ)) := by
    calc
      (35878106791/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(17/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(17/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (17/256:ℝ) (9/128:ℝ) (35878106791/10000000000:ℝ) (13926771157/250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0108).1
  intro u hu
  exact (show (841530099567674249/500000000000000000:ℝ) ≤ (1/4-6*(35878106791/10000000000:ℝ)+4*(35878106791/10000000000:ℝ)^2)*(13926771157/250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_018 :
    ∀ u ∈ Set.Icc (9/128:ℝ) (19/256:ℝ), (1674029260262033759/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (3615950227/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/128:ℝ)) := by
    calc
      (3615950227/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(9/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(9/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (9/128:ℝ) (19/256:ℝ) (3615950227/1000000000:ℝ) (1356381841877/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0114).1
  intro u hu
  exact (show (1674029260262033759/1000000000000000000:ℝ) ≤ (1/4-6*(3615950227/1000000000:ℝ)+4*(3615950227/1000000000:ℝ)^2)*(1356381841877/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_019 :
    ∀ u ∈ Set.Icc (19/256:ℝ) (5/64:ℝ), (832280181221222783/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (18221552381/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/256:ℝ)) := by
    calc
      (18221552381/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(19/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(19/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (19/256:ℝ) (5/64:ℝ) (18221552381/5000000000:ℝ) (2641477340537/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0120).1
  intro u hu
  exact (show (832280181221222783/500000000000000000:ℝ) ≤ (1/4-6*(18221552381/5000000000:ℝ)+4*(18221552381/5000000000:ℝ)^2)*(2641477340537/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_020 :
    ∀ u ∈ Set.Icc (5/64:ℝ) (21/256:ℝ), (1654660691937798839/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (1469157263/400000000:ℝ) ≤ Real.pi*Real.exp (2*(5/64:ℝ)) := by
    calc
      (1469157263/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(5/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(5/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (5/64:ℝ) (21/256:ℝ) (1469157263/400000000:ℝ) (5142975472393/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0126).1
  intro u hu
  exact (show (1654660691937798839/1000000000000000000:ℝ) ≤ (1/4-6*(1469157263/400000000:ℝ)+4*(1469157263/400000000:ℝ)^2)*(5142975472393/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_021 :
    ∀ u ∈ Set.Icc (21/256:ℝ) (11/128:ℝ), (12846388361106899/7812500000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (9254250039/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(21/256:ℝ)) := by
    calc
      (9254250039/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(21/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(21/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (21/256:ℝ) (11/128:ℝ) (9254250039/2500000000:ℝ) (2502787072221/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0132).1
  intro u hu
  exact (show (12846388361106899/7812500000000000:ℝ) ≤ (1/4-6*(9254250039/2500000000:ℝ)+4*(9254250039/2500000000:ℝ)^2)*(2502787072221/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_022 :
    ∀ u ∈ Set.Icc (11/128:ℝ) (23/256:ℝ), (326719829522905161/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (18653664043/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/128:ℝ)) := by
    calc
      (18653664043/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(11/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(11/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (11/128:ℝ) (23/256:ℝ) (18653664043/5000000000:ℝ) (97414688919/2000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0138).1
  intro u hu
  exact (show (326719829522905161/200000000000000000:ℝ) ≤ (1/4-6*(18653664043/5000000000:ℝ)+4*(18653664043/5000000000:ℝ)^2)*(97414688919/2000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_023 :
    ∀ u ∈ Set.Icc (23/256:ℝ) (3/32:ℝ), (64898119919301951/40000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (37599933087/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/256:ℝ)) := by
    calc
      (37599933087/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(23/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(23/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (23/256:ℝ) (3/32:ℝ) (37599933087/10000000000:ℝ) (4738439483347/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0144).1
  intro u hu
  exact (show (64898119919301951/40000000000000000:ℝ) ≤ (1/4-6*(37599933087/10000000000:ℝ)+4*(37599933087/10000000000:ℝ)^2)*(4738439483347/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_024 :
    ∀ u ∈ Set.Icc (3/32:ℝ) (25/256:ℝ), (805453755869069143/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (37894833017/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/32:ℝ)) := by
    calc
      (37894833017/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/32:ℝ) (25/256:ℝ) (37894833017/10000000000:ℝ) (576083966659/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0150).1
  intro u hu
  exact (show (805453755869069143/500000000000000000:ℝ) ≤ (1/4-6*(37894833017/10000000000:ℝ)+4*(37894833017/10000000000:ℝ)^2)*(576083966659/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_025 :
    ∀ u ∈ Set.Icc (25/256:ℝ) (13/128:ℝ), (799485594891087013/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (9548011469/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(25/256:ℝ)) := by
    calc
      (9548011469/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(25/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(25/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (25/256:ℝ) (13/128:ℝ) (9548011469/2500000000:ℝ) (4481413055423/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0156).1
  intro u hu
  exact (show (799485594891087013/500000000000000000:ℝ) ≤ (1/4-6*(9548011469/2500000000:ℝ)+4*(9548011469/2500000000:ℝ)^2)*(4481413055423/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_026 :
    ∀ u ∈ Set.Icc (13/128:ℝ) (27/256:ℝ), (793326388093261413/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (9622897451/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(13/128:ℝ)) := by
    calc
      (9622897451/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(13/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(13/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (13/128:ℝ) (27/256:ℝ) (9622897451/2500000000:ℝ) (4356644705751/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0162).1
  intro u hu
  exact (show (793326388093261413/500000000000000000:ℝ) ≤ (1/4-6*(9622897451/2500000000:ℝ)+4*(9622897451/2500000000:ℝ)^2)*(4356644705751/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_027 :
    ∀ u ∈ Set.Icc (27/256:ℝ) (7/64:ℝ), (1573961251251712099/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (7758696617/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/256:ℝ)) := by
    calc
      (7758696617/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(27/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(27/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (27/256:ℝ) (7/64:ℝ) (7758696617/2000000000:ℝ) (2117173675039/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0168).1
  intro u hu
  exact (show (1573961251251712099/1000000000000000000:ℝ) ≤ (1/4-6*(7758696617/2000000000:ℝ)+4*(7758696617/2000000000:ℝ)^2)*(2117173675039/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_028 :
    ∀ u ∈ Set.Icc (7/64:ℝ) (29/256:ℝ), (97556613961683183/62500000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (39097744143/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/64:ℝ)) := by
    calc
      (39097744143/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(7/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(7/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (7/64:ℝ) (29/256:ℝ) (39097744143/10000000000:ℝ) (514312634759/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0174).1
  intro u hu
  exact (show (97556613961683183/62500000000000000:ℝ) ≤ (1/4-6*(39097744143/10000000000:ℝ)+4*(39097744143/10000000000:ℝ)^2)*(514312634759/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_029 :
    ∀ u ∈ Set.Icc (29/256:ℝ) (15/128:ℝ), (1547495922062128387/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (39404391551/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/256:ℝ)) := by
    calc
      (39404391551/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(29/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(29/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (29/256:ℝ) (15/128:ℝ) (39404391551/10000000000:ℝ) (1998542708769/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0180).1
  intro u hu
  exact (show (1547495922062128387/1000000000000000000:ℝ) ≤ (1/4-6*(39404391551/10000000000:ℝ)+4*(39404391551/10000000000:ℝ)^2)*(1998542708769/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_030 :
    ∀ u ∈ Set.Icc (15/128:ℝ) (31/256:ℝ), (1533741188904293299/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (1588537761/400000000:ℝ) ≤ Real.pi*Real.exp (2*(15/128:ℝ)) := by
    calc
      (1588537761/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(15/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(15/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (15/128:ℝ) (31/256:ℝ) (1588537761/400000000:ℝ) (242629959321/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0186).1
  intro u hu
  exact (show (1533741188904293299/1000000000000000000:ℝ) ≤ (1/4-6*(1588537761/400000000:ℝ)+4*(1588537761/400000000:ℝ)^2)*(242629959321/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_031 :
    ∀ u ∈ Set.Icc (31/256:ℝ) (1/8:ℝ), (759825734717146723/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (40024920427/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/256:ℝ)) := by
    calc
      (40024920427/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(31/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(31/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (31/256:ℝ) (1/8:ℝ) (40024920427/10000000000:ℝ) (1884730660659/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0192).1
  intro u hu
  exact (show (759825734717146723/500000000000000000:ℝ) ≤ (1/4-6*(40024920427/10000000000:ℝ)+4*(40024920427/10000000000:ℝ)^2)*(1884730660659/50000000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

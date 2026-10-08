import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_032 :
    ∀ u ∈ Set.Icc (1/8:ℝ) (33/256:ℝ), (1505236804533694299/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (5042354971/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(1/8:ℝ)) := by
    calc
      (5042354971/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/8:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/8:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/8:ℝ) (33/256:ℝ) (5042354971/1250000000:ℝ) (3659209265657/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0198).1
  intro u hu
  exact (show (1505236804533694299/1000000000000000000:ℝ) ≤ (1/4-6*(5042354971/1250000000:ℝ)+4*(5042354971/1250000000:ℝ)^2)*(3659209265657/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_033 :
    ∀ u ∈ Set.Icc (33/256:ℝ) (17/128:ℝ), (372626855380705201/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (4065522121/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/256:ℝ)) := by
    calc
      (4065522121/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(33/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(33/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (33/256:ℝ) (17/128:ℝ) (4065522121/1000000000:ℝ) (1775650306231/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0204).1
  intro u hu
  exact (show (372626855380705201/250000000000000000:ℝ) ≤ (1/4-6*(4065522121/1000000000:ℝ)+4*(4065522121/1000000000:ℝ)^2)*(1775650306231/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_034 :
    ∀ u ∈ Set.Icc (17/128:ℝ) (35/256:ℝ), (737736862199491809/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (20487042031/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/128:ℝ)) := by
    calc
      (20487042031/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(17/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(17/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (17/128:ℝ) (35/256:ℝ) (20487042031/5000000000:ℝ) (689142461327/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0210).1
  intro u hu
  exact (show (737736862199491809/500000000000000000:ℝ) ≤ (1/4-6*(20487042031/5000000000:ℝ)+4*(20487042031/5000000000:ℝ)^2)*(689142461327/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_035 :
    ∀ u ∈ Set.Icc (35/256:ℝ) (9/64:ℝ), (45629571400713733/31250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (20647723893/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/256:ℝ)) := by
    calc
      (20647723893/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(35/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(35/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (35/256:ℝ) (9/64:ℝ) (20647723893/5000000000:ℝ) (3342420823879/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0216).1
  intro u hu
  exact (show (45629571400713733/31250000000000000:ℝ) ≤ (1/4-6*(20647723893/5000000000:ℝ)+4*(20647723893/5000000000:ℝ)^2)*(3342420823879/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_036 :
    ∀ u ∈ Set.Icc (9/64:ℝ) (37/256:ℝ), (288907166448900491/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (41619331997/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/64:ℝ)) := by
    calc
      (41619331997/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(9/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(9/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (9/64:ℝ) (37/256:ℝ) (41619331997/10000000000:ℝ) (129656087483/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0222).1
  intro u hu
  exact (show (288907166448900491/200000000000000000:ℝ) ≤ (1/4-6*(41619331997/10000000000:ℝ)+4*(41619331997/10000000000:ℝ)^2)*(129656087483/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_037 :
    ∀ u ∈ Set.Icc (37/256:ℝ) (19/128:ℝ), (89290827741626873/62500000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (41945756463/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/256:ℝ)) := by
    calc
      (41945756463/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(37/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(37/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (37/256:ℝ) (19/128:ℝ) (41945756463/10000000000:ℝ) (785657995753/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0228).1
  intro u hu
  exact (show (89290827741626873/62500000000000000:ℝ) ≤ (1/4-6*(41945756463/10000000000:ℝ)+4*(41945756463/10000000000:ℝ)^2)*(785657995753/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_038 :
    ∀ u ∈ Set.Icc (19/128:ℝ) (39/256:ℝ), (1412509534683562307/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (42274741109/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/128:ℝ)) := by
    calc
      (42274741109/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(19/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(19/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (19/128:ℝ) (39/256:ℝ) (42274741109/10000000000:ℝ) (380760672401/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0234).1
  intro u hu
  exact (show (1412509534683562307/1000000000000000000:ℝ) ≤ (1/4-6*(42274741109/10000000000:ℝ)+4*(42274741109/10000000000:ℝ)^2)*(380760672401/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_039 :
    ∀ u ∈ Set.Icc (39/256:ℝ) (5/32:ℝ), (349028961673015303/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (42606306013/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/256:ℝ)) := by
    calc
      (42606306013/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(39/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(39/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (39/256:ℝ) (5/32:ℝ) (42606306013/10000000000:ℝ) (184483571317/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0240).1
  intro u hu
  exact (show (349028961673015303/250000000000000000:ℝ) ≤ (1/4-6*(42606306013/10000000000:ℝ)+4*(42606306013/10000000000:ℝ)^2)*(184483571317/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_040 :
    ∀ u ∈ Set.Icc (5/32:ℝ) (41/256:ℝ), (1379483438729095073/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (10735117853/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(5/32:ℝ)) := by
    calc
      (10735117853/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(5/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(5/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (5/32:ℝ) (41/256:ℝ) (10735117853/2500000000:ℝ) (178722603073/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0246).1
  intro u hu
  exact (show (1379483438729095073/1000000000000000000:ℝ) ≤ (1/4-6*(10735117853/2500000000:ℝ)+4*(10735117853/2500000000:ℝ)^2)*(178722603073/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_041 :
    ∀ u ∈ Set.Icc (41/256:ℝ) (21/128:ℝ), (272524735160506569/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (5409657213/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(41/256:ℝ)) := by
    calc
      (5409657213/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(41/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(41/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (41/256:ℝ) (21/128:ℝ) (5409657213/1250000000:ℝ) (1384766458359/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0252).1
  intro u hu
  exact (show (272524735160506569/200000000000000000:ℝ) ≤ (1/4-6*(5409657213/1250000000:ℝ)+4*(5409657213/1250000000:ℝ)^2)*(1384766458359/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_042 :
    ∀ u ∈ Set.Icc (21/128:ℝ) (43/256:ℝ), (168193502212474447/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (43616685443/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/128:ℝ)) := by
    calc
      (43616685443/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(21/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(21/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (21/128:ℝ) (43/256:ℝ) (43616685443/10000000000:ℝ) (167601537953/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0258).1
  intro u hu
  exact (show (168193502212474447/125000000000000000:ℝ) ≤ (1/4-6*(43616685443/10000000000:ℝ)+4*(43616685443/10000000000:ℝ)^2)*(167601537953/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_043 :
    ∀ u ∈ Set.Icc (43/256:ℝ) (11/64:ℝ), (664134004242976343/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (43958775347/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/256:ℝ)) := by
    calc
      (43958775347/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(43/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(43/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (43/256:ℝ) (11/64:ℝ) (43958775347/10000000000:ℝ) (1297905026173/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0264).1
  intro u hu
  exact (show (664134004242976343/500000000000000000:ℝ) ≤ (1/4-6*(43958775347/10000000000:ℝ)+4*(43958775347/10000000000:ℝ)^2)*(1297905026173/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_044 :
    ∀ u ∈ Set.Icc (11/64:ℝ) (45/256:ℝ), (655397632509854761/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (8860709659/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/64:ℝ)) := by
    calc
      (8860709659/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(11/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(11/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (11/64:ℝ) (45/256:ℝ) (8860709659/2000000000:ℝ) (2512062269617/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0270).1
  intro u hu
  exact (show (655397632509854761/500000000000000000:ℝ) ≤ (1/4-6*(8860709659/2000000000:ℝ)+4*(8860709659/2000000000:ℝ)^2)*(2512062269617/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_045 :
    ∀ u ∈ Set.Icc (45/256:ℝ) (23/128:ℝ), (10102667702120131/7812500000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (44651025331/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/256:ℝ)) := by
    calc
      (44651025331/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(45/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(45/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (45/256:ℝ) (23/128:ℝ) (44651025331/10000000000:ℝ) (1215176990341/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0276).1
  intro u hu
  exact (show (10102667702120131/7812500000000000:ℝ) ≤ (1/4-6*(44651025331/10000000000:ℝ)+4*(44651025331/10000000000:ℝ)^2)*(1215176990341/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_046 :
    ∀ u ∈ Set.Icc (23/128:ℝ) (47/256:ℝ), (1275318339791649473/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (45001227663/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/128:ℝ)) := by
    calc
      (45001227663/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(23/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(23/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (23/128:ℝ) (47/256:ℝ) (45001227663/10000000000:ℝ) (587664407333/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0282).1
  intro u hu
  exact (show (1275318339791649473/1000000000000000000:ℝ) ≤ (1/4-6*(45001227663/10000000000:ℝ)+4*(45001227663/10000000000:ℝ)^2)*(587664407333/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_047 :
    ∀ u ∈ Set.Icc (47/256:ℝ) (3/16:ℝ), (628668827175261319/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (22677088333/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/256:ℝ)) := by
    calc
      (22677088333/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(47/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(47/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (47/256:ℝ) (3/16:ℝ) (22677088333/5000000000:ℝ) (2272945399673/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0288).1
  intro u hu
  exact (show (628668827175261319/500000000000000000:ℝ) ≤ (1/4-6*(22677088333/5000000000:ℝ)+4*(22677088333/5000000000:ℝ)^2)*(2272945399673/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_048 :
    ∀ u ∈ Set.Icc (3/16:ℝ) (49/256:ℝ), (247842240871482451/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (22854946941/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/16:ℝ)) := by
    calc
      (22854946941/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/16:ℝ) (49/256:ℝ) (22854946941/5000000000:ℝ) (439437846891/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0294).1
  intro u hu
  exact (show (247842240871482451/200000000000000000:ℝ) ≤ (1/4-6*(22854946941/5000000000:ℝ)+4*(22854946941/5000000000:ℝ)^2)*(439437846891/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_049 :
    ∀ u ∈ Set.Icc (49/256:ℝ) (25/128:ℝ), (1220950800364612401/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (46068401023/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/256:ℝ)) := by
    calc
      (46068401023/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(49/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(49/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (49/256:ℝ) (25/128:ℝ) (46068401023/10000000000:ℝ) (1061680426651/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0300).1
  intro u hu
  exact (show (1220950800364612401/1000000000000000000:ℝ) ≤ (1/4-6*(46068401023/10000000000:ℝ)+4*(46068401023/10000000000:ℝ)^2)*(1061680426651/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_050 :
    ∀ u ∈ Set.Icc (25/128:ℝ) (51/256:ℝ), (1202568256922579683/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (4642971997/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/128:ℝ)) := by
    calc
      (4642971997/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(25/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(25/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (25/128:ℝ) (51/256:ℝ) (4642971997/1000000000:ℝ) (2051431771071/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0306).1
  intro u hu
  exact (show (1202568256922579683/1000000000000000000:ℝ) ≤ (1/4-6*(4642971997/1000000000:ℝ)+4*(4642971997/1000000000:ℝ)^2)*(2051431771071/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_051 :
    ∀ u ∈ Set.Icc (51/256:ℝ) (13/64:ℝ), (592037690565412011/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (46793872777/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/256:ℝ)) := by
    calc
      (46793872777/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(51/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(51/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (51/256:ℝ) (13/64:ℝ) (46793872777/10000000000:ℝ) (79254932647/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0312).1
  intro u hu
  exact (show (592037690565412011/500000000000000000:ℝ) ≤ (1/4-6*(46793872777/10000000000:ℝ)+4*(46793872777/10000000000:ℝ)^2)*(79254932647/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_052 :
    ∀ u ∈ Set.Icc (13/64:ℝ) (53/256:ℝ), (1165483960852216633/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (4716088167/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/64:ℝ)) := by
    calc
      (4716088167/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(13/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(13/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (13/64:ℝ) (53/256:ℝ) (4716088167/1000000000:ℝ) (23914458111/1250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0318).1
  intro u hu
  exact (show (1165483960852216633/1000000000000000000:ℝ) ≤ (1/4-6*(4716088167/1000000000:ℝ)+4*(4716088167/1000000000:ℝ)^2)*(23914458111/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_053 :
    ∀ u ∈ Set.Icc (53/256:ℝ) (27/128:ℝ), (1146805753150462477/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (47530769049/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/256:ℝ)) := by
    calc
      (47530769049/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(53/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(53/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (53/256:ℝ) (27/128:ℝ) (47530769049/10000000000:ℝ) (1846752779581/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0324).1
  intro u hu
  exact (show (1146805753150462477/1000000000000000000:ℝ) ≤ (1/4-6*(47530769049/10000000000:ℝ)+4*(47530769049/10000000000:ℝ)^2)*(1846752779581/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_054 :
    ∀ u ∈ Set.Icc (27/128:ℝ) (55/256:ℝ), (564026236416942689/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (47903557491/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/128:ℝ)) := by
    calc
      (47903557491/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(27/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(27/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (27/128:ℝ) (55/256:ℝ) (47903557491/10000000000:ℝ) (89106629353/5000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0330).1
  intro u hu
  exact (show (564026236416942689/500000000000000000:ℝ) ≤ (1/4-6*(47903557491/10000000000:ℝ)+4*(47903557491/10000000000:ℝ)^2)*(89106629353/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_055 :
    ∀ u ∈ Set.Icc (55/256:ℝ) (7/32:ℝ), (221847156154640409/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (48279269749/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/256:ℝ)) := by
    calc
      (48279269749/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(55/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(55/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (55/256:ℝ) (7/32:ℝ) (48279269749/10000000000:ℝ) (429816709153/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0336).1
  intro u hu
  exact (show (221847156154640409/200000000000000000:ℝ) ≤ (1/4-6*(48279269749/10000000000:ℝ)+4*(48279269749/10000000000:ℝ)^2)*(429816709153/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_056 :
    ∀ u ∈ Set.Icc (7/32:ℝ) (57/256:ℝ), (545183636290087911/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (9731585751/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/32:ℝ)) := by
    calc
      (9731585751/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(7/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(7/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (7/32:ℝ) (57/256:ℝ) (9731585751/2000000000:ℝ) (829063099083/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0342).1
  intro u hu
  exact (show (545183636290087911/500000000000000000:ℝ) ≤ (1/4-6*(9731585751/2000000000:ℝ)+4*(9731585751/2000000000:ℝ)^2)*(829063099083/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_057 :
    ∀ u ∈ Set.Icc (57/256:ℝ) (29/128:ℝ), (214291693428588019/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (2451977881/500000000:ℝ) ≤ Real.pi*Real.exp (2*(57/256:ℝ)) := by
    calc
      (2451977881/500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(57/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(57/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (57/256:ℝ) (29/128:ℝ) (2451977881/500000000:ℝ) (399670316053/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0348).1
  intro u hu
  exact (show (214291693428588019/200000000000000000:ℝ) ≤ (1/4-6*(2451977881/500000000:ℝ)+4*(2451977881/500000000:ℝ)^2)*(399670316053/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_058 :
    ∀ u ∈ Set.Icc (29/128:ℝ) (59/256:ℝ), (8222818714789663/7812500000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (49424179637/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/128:ℝ)) := by
    calc
      (49424179637/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(29/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(29/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (29/128:ℝ) (59/256:ℝ) (49424179637/10000000000:ℝ) (770451283849/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0354).1
  intro u hu
  exact (show (8222818714789663/7812500000000000:ℝ) ≤ (1/4-6*(49424179637/10000000000:ℝ)+4*(49424179637/10000000000:ℝ)^2)*(770451283849/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_059 :
    ∀ u ∈ Set.Icc (59/256:ℝ) (15/64:ℝ), (516782794844143017/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (49811818283/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/256:ℝ)) := by
    calc
      (49811818283/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(59/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(59/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (59/256:ℝ) (15/64:ℝ) (49811818283/10000000000:ℝ) (1484760599721/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0360).1
  intro u hu
  exact (show (516782794844143017/500000000000000000:ℝ) ≤ (1/4-6*(49811818283/10000000000:ℝ)+4*(49811818283/10000000000:ℝ)^2)*(1484760599721/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_060 :
    ∀ u ∈ Set.Icc (15/64:ℝ) (61/256:ℝ), (31706377237718811/31250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (784414019/156250000:ℝ) ≤ Real.pi*Real.exp (2*(15/64:ℝ)) := by
    calc
      (784414019/156250000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(15/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(15/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (15/64:ℝ) (61/256:ℝ) (784414019/156250000:ℝ) (1430225827093/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0366).1
  intro u hu
  exact (show (31706377237718811/31250000000000000:ℝ) ≤ (1/4-6*(784414019/156250000:ℝ)+4*(784414019/156250000:ℝ)^2)*(1430225827093/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_061 :
    ∀ u ∈ Set.Icc (61/256:ℝ) (31/128:ℝ), (497823671186989721/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (50596240281/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/256:ℝ)) := by
    calc
      (50596240281/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(61/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(61/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (61/256:ℝ) (31/128:ℝ) (50596240281/10000000000:ℝ) (275453741949/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0372).1
  intro u hu
  exact (show (497823671186989721/500000000000000000:ℝ) ≤ (1/4-6*(50596240281/10000000000:ℝ)+4*(50596240281/10000000000:ℝ)^2)*(275453741949/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_062 :
    ∀ u ∈ Set.Icc (31/128:ℝ) (63/256:ℝ), (97670637171555123/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (6374133939/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(31/128:ℝ)) := by
    calc
      (6374133939/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(31/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(31/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (31/128:ℝ) (63/256:ℝ) (6374133939/1250000000:ℝ) (331464929477/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0378).1
  intro u hu
  exact (show (97670637171555123/100000000000000000:ℝ) ≤ (1/4-6*(6374133939/1250000000:ℝ)+4*(6374133939/1250000000:ℝ)^2)*(331464929477/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_063 :
    ∀ u ∈ Set.Icc (63/256:ℝ) (1/4:ℝ), (23944799682406223/25000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (51393015129/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/256:ℝ)) := by
    calc
      (51393015129/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(63/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(63/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (63/256:ℝ) (1/4:ℝ) (51393015129/10000000000:ℝ) (159496168639/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0384).1
  intro u hu
  exact (show (23944799682406223/25000000000000000:ℝ) ≤ (1/4-6*(51393015129/10000000000:ℝ)+4*(51393015129/10000000000:ℝ)^2)*(159496168639/12500000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

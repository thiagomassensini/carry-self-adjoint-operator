import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_128 :
    ∀ u ∈ Set.Icc (1/2:ℝ) (129/256:ℝ), (56635078811378937/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (85397324389/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/2:ℝ)) := by
    calc
      (85397324389/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/2:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/2:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/2:ℝ) (129/256:ℝ) (85397324389/10000000000:ℝ) (47054788389/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0774).1
  intro u hu
  exact (show (56635078811378937/500000000000000000:ℝ) ≤ (1/4-6*(85397324389/10000000000:ℝ)+4*(85397324389/10000000000:ℝ)^2)*(47054788389/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_129 :
    ∀ u ∈ Set.Icc (129/256:ℝ) (65/128:ℝ), (21586144939916833/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (86067103899/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(129/256:ℝ)) := by
    calc
      (86067103899/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(129/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(129/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (129/256:ℝ) (65/128:ℝ) (86067103899/10000000000:ℝ) (44069259259/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0780).1
  intro u hu
  exact (show (21586144939916833/200000000000000000:ℝ) ≤ (1/4-6*(86067103899/10000000000:ℝ)+4*(86067103899/10000000000:ℝ)^2)*(44069259259/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_130 :
    ∀ u ∈ Set.Icc (65/128:ℝ) (131/256:ℝ), (102786981858788307/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (43371068277/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(65/128:ℝ)) := by
    calc
      (43371068277/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(65/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(65/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (65/128:ℝ) (131/256:ℝ) (43371068277/5000000000:ℝ) (20625655061/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0786).1
  intro u hu
  exact (show (102786981858788307/1000000000000000000:ℝ) ≤ (1/4-6*(43371068277/5000000000:ℝ)+4*(43371068277/5000000000:ℝ)^2)*(20625655061/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_131 :
    ∀ u ∈ Set.Icc (131/256:ℝ) (33/64:ℝ), (12229335208502793/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (17484492711/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(131/256:ℝ)) := by
    calc
      (17484492711/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(131/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(131/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (131/256:ℝ) (33/64:ℝ) (17484492711/2000000000:ℝ) (19296476363/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0792).1
  intro u hu
  exact (show (12229335208502793/125000000000000000:ℝ) ≤ (1/4-6*(17484492711/2000000000:ℝ)+4*(17484492711/2000000000:ℝ)^2)*(19296476363/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_132 :
    ∀ u ∈ Set.Icc (33/64:ℝ) (133/256:ℝ), (46534764213673919/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (44054063213/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/64:ℝ)) := by
    calc
      (44054063213/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(33/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(33/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (33/64:ℝ) (133/256:ℝ) (44054063213/5000000000:ℝ) (36086496271/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0798).1
  intro u hu
  exact (show (46534764213673919/500000000000000000:ℝ) ≤ (1/4-6*(44054063213/5000000000:ℝ)+4*(44054063213/5000000000:ℝ)^2)*(36086496271/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_133 :
    ∀ u ∈ Set.Icc (133/256:ℝ) (67/128:ℝ), (88487185923985229/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (44399583509/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(133/256:ℝ)) := by
    calc
      (44399583509/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(133/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(133/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (133/256:ℝ) (67/128:ℝ) (44399583509/5000000000:ℝ) (33724540723/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0804).1
  intro u hu
  exact (show (88487185923985229/1000000000000000000:ℝ) ≤ (1/4-6*(44399583509/5000000000:ℝ)+4*(44399583509/5000000000:ℝ)^2)*(33724540723/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_134 :
    ∀ u ∈ Set.Icc (67/128:ℝ) (135/256:ℝ), (21020821257204279/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (89495627507/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/128:ℝ)) := by
    calc
      (89495627507/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(67/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(67/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (67/128:ℝ) (135/256:ℝ) (89495627507/10000000000:ℝ) (3149997007/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0810).1
  intro u hu
  exact (show (21020821257204279/250000000000000000:ℝ) ≤ (1/4-6*(89495627507/10000000000:ℝ)+4*(89495627507/10000000000:ℝ)^2)*(3149997007/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_135 :
    ∀ u ∈ Set.Icc (135/256:ℝ) (17/32:ℝ), (2495419722748173/31250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (45098775201/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(135/256:ℝ)) := by
    calc
      (45098775201/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(135/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(135/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (135/256:ℝ) (17/32:ℝ) (45098775201/5000000000:ℝ) (367574319/1250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0816).1
  intro u hu
  exact (show (2495419722748173/31250000000000000:ℝ) ≤ (1/4-6*(45098775201/5000000000:ℝ)+4*(45098775201/5000000000:ℝ)^2)*(367574319/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_136 :
    ∀ u ∈ Set.Icc (17/32:ℝ) (137/256:ℝ), (2368537855823959/31250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (45452489273/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/32:ℝ)) := by
    calc
      (45452489273/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(17/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(17/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (17/32:ℝ) (137/256:ℝ) (45452489273/5000000000:ℝ) (27435898671/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0822).1
  intro u hu
  exact (show (2368537855823959/31250000000000000:ℝ) ≤ (1/4-6*(45452489273/5000000000:ℝ)+4*(45452489273/5000000000:ℝ)^2)*(27435898671/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_137 :
    ∀ u ∈ Set.Icc (137/256:ℝ) (69/128:ℝ), (35949100893156969/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (91617955117/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(137/256:ℝ)) := by
    calc
      (91617955117/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(137/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(137/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (137/256:ℝ) (69/128:ℝ) (91617955117/10000000000:ℝ) (159897029/625000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0828).1
  intro u hu
  exact (show (35949100893156969/500000000000000000:ℝ) ≤ (1/4-6*(91617955117/10000000000:ℝ)+4*(91617955117/10000000000:ℝ)^2)*(159897029/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_138 :
    ∀ u ∈ Set.Icc (69/128:ℝ) (139/256:ℝ), (68163974002885677/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (92336523631/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(69/128:ℝ)) := by
    calc
      (92336523631/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(69/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(69/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (69/128:ℝ) (139/256:ℝ) (92336523631/10000000000:ℝ) (5960693797/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0834).1
  intro u hu
  exact (show (68163974002885677/1000000000000000000:ℝ) ≤ (1/4-6*(92336523631/10000000000:ℝ)+4*(92336523631/10000000000:ℝ)^2)*(5960693797/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_139 :
    ∀ u ∈ Set.Icc (139/256:ℝ) (35/64:ℝ), (6458610204731741/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (93060727947/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(139/256:ℝ)) := by
    calc
      (93060727947/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(139/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(139/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (139/256:ℝ) (35/64:ℝ) (93060727947/10000000000:ℝ) (2220785183/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0840).1
  intro u hu
  exact (show (6458610204731741/100000000000000000:ℝ) ≤ (1/4-6*(93060727947/10000000000:ℝ)+4*(93060727947/10000000000:ℝ)^2)*(2220785183/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_140 :
    ∀ u ∈ Set.Icc (35/64:ℝ) (141/256:ℝ), (30580084349091647/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (93790612267/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/64:ℝ)) := by
    calc
      (93790612267/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(35/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(35/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (35/64:ℝ) (141/256:ℝ) (93790612267/10000000000:ℝ) (4134639791/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0846).1
  intro u hu
  exact (show (30580084349091647/500000000000000000:ℝ) ≤ (1/4-6*(93790612267/10000000000:ℝ)+4*(93790612267/10000000000:ℝ)^2)*(4134639791/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_141 :
    ∀ u ∈ Set.Icc (141/256:ℝ) (71/128:ℝ), (904402682722187/15625000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (47263110569/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(141/256:ℝ)) := by
    calc
      (47263110569/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(141/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(141/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (141/256:ℝ) (71/128:ℝ) (47263110569/5000000000:ℝ) (3846699391/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0852).1
  intro u hu
  exact (show (904402682722187/15625000000000000:ℝ) ≤ (1/4-6*(47263110569/5000000000:ℝ)+4*(47263110569/5000000000:ℝ)^2)*(3846699391/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_142 :
    ∀ u ∈ Set.Icc (71/128:ℝ) (143/256:ℝ), (27373264861214221/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (95267599461/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/128:ℝ)) := by
    calc
      (95267599461/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(71/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(71/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (71/128:ℝ) (143/256:ℝ) (95267599461/10000000000:ℝ) (3576731077/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0858).1
  intro u hu
  exact (show (27373264861214221/500000000000000000:ℝ) ≤ (1/4-6*(95267599461/10000000000:ℝ)+4*(95267599461/10000000000:ℝ)^2)*(3576731077/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_143 :
    ∀ u ∈ Set.Icc (143/256:ℝ) (9/16:ℝ), (25875044056449187/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (24003698121/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(143/256:ℝ)) := by
    calc
      (24003698121/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(143/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(143/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (143/256:ℝ) (9/16:ℝ) (24003698121/2500000000:ℝ) (8309403073/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0864).1
  intro u hu
  exact (show (25875044056449187/500000000000000000:ℝ) ≤ (1/4-6*(24003698121/2500000000:ℝ)+4*(24003698121/2500000000:ℝ)^2)*(8309403073/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_144 :
    ∀ u ∈ Set.Icc (9/16:ℝ) (145/256:ℝ), (9777624868232171/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (96767845813/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/16:ℝ)) := by
    calc
      (96767845813/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(9/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(9/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (9/16:ℝ) (145/256:ℝ) (96767845813/10000000000:ℝ) (192928709/1250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0870).1
  intro u hu
  exact (show (9777624868232171/200000000000000000:ℝ) ≤ (1/4-6*(96767845813/10000000000:ℝ)+4*(96767845813/10000000000:ℝ)^2)*(192928709/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_145 :
    ∀ u ∈ Set.Icc (145/256:ℝ) (73/128:ℝ), (23078176624776193/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (97526805411/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(145/256:ℝ)) := by
    calc
      (97526805411/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(145/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(145/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (145/256:ℝ) (73/128:ℝ) (97526805411/10000000000:ℝ) (14325683451/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0876).1
  intro u hu
  exact (show (23078176624776193/500000000000000000:ℝ) ≤ (1/4-6*(97526805411/10000000000:ℝ)+4*(97526805411/10000000000:ℝ)^2)*(14325683451/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_146 :
    ∀ u ∈ Set.Icc (73/128:ℝ) (147/256:ℝ), (21775266004453039/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (122864647/12500000:ℝ) ≤ Real.pi*Real.exp (2*(73/128:ℝ)) := by
    calc
      (122864647/12500000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(73/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(73/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (73/128:ℝ) (147/256:ℝ) (122864647/12500000:ℝ) (6644362441/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0882).1
  intro u hu
  exact (show (21775266004453039/500000000000000000:ℝ) ≤ (1/4-6*(122864647/12500000:ℝ)+4*(122864647/12500000:ℝ)^2)*(6644362441/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_147 :
    ∀ u ∈ Set.Icc (147/256:ℝ) (37/64:ℝ), (20533232419187341/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (99062629069/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(147/256:ℝ)) := by
    calc
      (99062629069/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(147/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(147/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (147/256:ℝ) (37/64:ℝ) (99062629069/10000000000:ℝ) (6159687581/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0888).1
  intro u hu
  exact (show (20533232419187341/500000000000000000:ℝ) ≤ (1/4-6*(99062629069/10000000000:ℝ)+4*(99062629069/10000000000:ℝ)^2)*(6159687581/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_148 :
    ∀ u ∈ Set.Icc (37/64:ℝ) (149/256:ℝ), (19350003728002473/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (99839586869/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/64:ℝ)) := by
    calc
      (99839586869/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(37/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(37/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (37/64:ℝ) (149/256:ℝ) (99839586869/10000000000:ℝ) (1426722191/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0894).1
  intro u hu
  exact (show (19350003728002473/500000000000000000:ℝ) ≤ (1/4-6*(99839586869/10000000000:ℝ)+4*(99839586869/10000000000:ℝ)^2)*(1426722191/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_149 :
    ∀ u ∈ Set.Icc (149/256:ℝ) (75/128:ℝ), (1822353562406607/50000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (50311319211/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(149/256:ℝ)) := by
    calc
      (50311319211/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(149/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(149/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (149/256:ℝ) (75/128:ℝ) (50311319211/5000000000:ℝ) (5284128929/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0900).1
  intro u hu
  exact (show (1822353562406607/50000000000000000:ℝ) ≤ (1/4-6*(50311319211/5000000000:ℝ)+4*(50311319211/5000000000:ℝ)^2)*(5284128929/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_150 :
    ∀ u ∈ Set.Icc (75/128:ℝ) (151/256:ℝ), (17151813610223543/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (50705915761/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/128:ℝ)) := by
    calc
      (50705915761/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(75/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(75/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (75/128:ℝ) (151/256:ℝ) (50705915761/5000000000:ℝ) (9779318327/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0906).1
  intro u hu
  exact (show (17151813610223543/500000000000000000:ℝ) ≤ (1/4-6*(50705915761/5000000000:ℝ)+4*(50705915761/5000000000:ℝ)^2)*(9779318327/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_151 :
    ∀ u ∈ Set.Icc (151/256:ℝ) (19/32:ℝ), (8066427405520841/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (51103607169/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(151/256:ℝ)) := by
    calc
      (51103607169/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(151/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(151/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (151/256:ℝ) (19/32:ℝ) (51103607169/5000000000:ℝ) (9043631137/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0912).1
  intro u hu
  exact (show (8066427405520841/250000000000000000:ℝ) ≤ (1/4-6*(51103607169/5000000000:ℝ)+4*(51103607169/5000000000:ℝ)^2)*(9043631137/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_152 :
    ∀ u ∈ Set.Icc (19/32:ℝ) (153/256:ℝ), (30329419364521959/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (12876104427/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(19/32:ℝ)) := by
    calc
      (12876104427/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(19/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(19/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (19/32:ℝ) (153/256:ℝ) (12876104427/1250000000:ℝ) (8358032363/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0918).1
  intro u hu
  exact (show (30329419364521959/1000000000000000000:ℝ) ≤ (1/4-6*(12876104427/1250000000:ℝ)+4*(12876104427/1250000000:ℝ)^2)*(8358032363/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_153 :
    ∀ u ∈ Set.Icc (153/256:ℝ) (77/128:ℝ), (5698185426869039/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (103816743683/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(153/256:ℝ)) := by
    calc
      (103816743683/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(153/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(153/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (153/256:ℝ) (77/128:ℝ) (103816743683/10000000000:ℝ) (771951589/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0924).1
  intro u hu
  exact (show (5698185426869039/200000000000000000:ℝ) ≤ (1/4-6*(103816743683/10000000000:ℝ)+4*(103816743683/10000000000:ℝ)^2)*(771951589/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_154 :
    ∀ u ∈ Set.Icc (77/128:ℝ) (155/256:ℝ), (13373238132940231/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (2092619769/200000000:ℝ) ≤ Real.pi*Real.exp (2*(77/128:ℝ)) := by
    calc
      (2092619769/200000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(77/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(77/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (77/128:ℝ) (155/256:ℝ) (2092619769/200000000:ℝ) (1425045493/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0930).1
  intro u hu
  exact (show (13373238132940231/500000000000000000:ℝ) ≤ (1/4-6*(2092619769/200000000:ℝ)+4*(2092619769/200000000:ℝ)^2)*(1425045493/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_155 :
    ∀ u ∈ Set.Icc (155/256:ℝ) (39/64:ℝ), (2509238535479287/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (52725809707/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(155/256:ℝ)) := by
    calc
      (52725809707/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(155/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(155/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (155/256:ℝ) (39/64:ℝ) (52725809707/5000000000:ℝ) (3286229431/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0936).1
  intro u hu
  exact (show (2509238535479287/100000000000000000:ℝ) ≤ (1/4-6*(52725809707/5000000000:ℝ)+4*(52725809707/5000000000:ℝ)^2)*(3286229431/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_156 :
    ∀ u ∈ Set.Icc (39/64:ℝ) (157/256:ℝ), (941002024403311/40000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (106278686663/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/64:ℝ)) := by
    calc
      (106278686663/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(39/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(39/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (39/64:ℝ) (157/256:ℝ) (106278686663/10000000000:ℝ) (3029321081/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0942).1
  intro u hu
  exact (show (941002024403311/40000000000000000:ℝ) ≤ (1/4-6*(106278686663/10000000000:ℝ)+4*(106278686663/10000000000:ℝ)^2)*(3029321081/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_157 :
    ∀ u ∈ Set.Icc (157/256:ℝ) (79/128:ℝ), (22040947956740601/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (107112240677/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(157/256:ℝ)) := by
    calc
      (107112240677/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(157/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(157/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (157/256:ℝ) (79/128:ℝ) (107112240677/10000000000:ℝ) (1116268831/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0948).1
  intro u hu
  exact (show (22040947956740601/1000000000000000000:ℝ) ≤ (1/4-6*(107112240677/10000000000:ℝ)+4*(107112240677/10000000000:ℝ)^2)*(1116268831/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_158 :
    ∀ u ∈ Set.Icc (79/128:ℝ) (159/256:ℝ), (10318317444428261/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (26988083083/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(79/128:ℝ)) := by
    calc
      (26988083083/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(79/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(79/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (79/128:ℝ) (159/256:ℝ) (26988083083/2500000000:ℝ) (1027652173/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0954).1
  intro u hu
  exact (show (10318317444428261/500000000000000000:ℝ) ≤ (1/4-6*(26988083083/2500000000:ℝ)+4*(26988083083/2500000000:ℝ)^2)*(1027652173/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_159 :
    ∀ u ∈ Set.Icc (159/256:ℝ) (5/8:ℝ), (9654376044293469/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (13599876613/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(159/256:ℝ)) := by
    calc
      (13599876613/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(159/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(159/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (159/256:ℝ) (5/8:ℝ) (13599876613/1250000000:ℝ) (1181803051/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0960).1
  intro u hu
  exact (show (9654376044293469/500000000000000000:ℝ) ≤ (1/4-6*(13599876613/1250000000:ℝ)+4*(13599876613/1250000000:ℝ)^2)*(1181803051/25000000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

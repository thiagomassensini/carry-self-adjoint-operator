import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_416 :
    ∀ u ∈ Set.Icc (13/16:ℝ) (417/512:ℝ), (154697424799214552691/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16016764065227/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(417/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(417/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (13/16:ℝ) (417/512:ℝ) (16016764065227/1000000000000:ℝ) (16628833/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1249).1
  intro u hu
  exact (show (154697424799214552691/500000000000000000000000:ℝ) ≤ (1/4-6*(16016764065227/1000000000000:ℝ)+4*(16016764065227/1000000000000:ℝ)^2)*(16628833/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_417 :
    ∀ u ∈ Set.Icc (417/512:ℝ) (209/256:ℝ), (36659716912842526041/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2009931488417/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(209/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(209/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (417/512:ℝ) (209/256:ℝ) (2009931488417/125000000000:ℝ) (31267337/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1254).1
  intro u hu
  exact (show (36659716912842526041/125000000000000000000000:ℝ) ≤ (1/4-6*(2009931488417/125000000000:ℝ)+4*(2009931488417/125000000000:ℝ)^2)*(31267337/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_418 :
    ∀ u ∈ Set.Icc (209/256:ℝ) (419/512:ℝ), (277931522703706091913/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16142385102723/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(419/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(419/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (209/256:ℝ) (419/512:ℝ) (16142385102723/1000000000000:ℝ) (29388909/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1255).1
  intro u hu
  exact (show (277931522703706091913/1000000000000000000000000:ℝ) ≤ (1/4-6*(16142385102723/1000000000000:ℝ)+4*(16142385102723/1000000000000:ℝ)^2)*(29388909/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_419 :
    ∀ u ∈ Set.Icc (419/512:ℝ) (105/128:ℝ), (16457687982596865951/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2025695576459/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(105/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (419/512:ℝ) (105/128:ℝ) (2025695576459/125000000000:ℝ) (27616527/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1260).1
  intro u hu
  exact (show (16457687982596865951/62500000000000000000000:ℝ) ≤ (1/4-6*(2025695576459/125000000000:ℝ)+4*(2025695576459/125000000000:ℝ)^2)*(27616527/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_420 :
    ∀ u ∈ Set.Icc (105/128:ℝ) (421/512:ℝ), (249420229777245076453/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4067247849557/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(421/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(421/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (105/128:ℝ) (421/512:ℝ) (4067247849557/250000000000:ℝ) (25944617/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1261).1
  intro u hu
  exact (show (249420229777245076453/1000000000000000000000000:ℝ) ≤ (1/4-6*(4067247849557/250000000000:ℝ)+4*(4067247849557/250000000000:ℝ)^2)*(25944617/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_421 :
    ∀ u ∈ Set.Icc (421/512:ℝ) (211/256:ℝ), (236192444692696261033/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16332666430207/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(211/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(211/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (421/512:ℝ) (211/256:ℝ) (16332666430207/1000000000000:ℝ) (194943/800000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1266).1
  intro u hu
  exact (show (236192444692696261033/1000000000000000000000000:ℝ) ≤ (1/4-6*(16332666430207/1000000000000:ℝ)+4*(16332666430207/1000000000000:ℝ)^2)*(194943/800000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_422 :
    ∀ u ∈ Set.Icc (211/256:ℝ) (423/512:ℝ), (223610065160718119631/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3279318135843/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(423/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(423/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (211/256:ℝ) (423/512:ℝ) (3279318135843/200000000000:ℝ) (22881253/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1267).1
  intro u hu
  exact (show (223610065160718119631/1000000000000000000000000:ℝ) ≤ (1/4-6*(3279318135843/200000000000:ℝ)+4*(3279318135843/200000000000:ℝ)^2)*(22881253/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_423 :
    ∀ u ∈ Set.Icc (423/512:ℝ) (53/64:ℝ), (264555831899039919/1250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16460765120659/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (423/512:ℝ) (53/64:ℝ) (16460765120659/1000000000000:ℝ) (1342497/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1272).1
  intro u hu
  exact (show (264555831899039919/1250000000000000000000:ℝ) ≤ (1/4-6*(16460765120659/1000000000000:ℝ)+4*(16460765120659/1000000000000:ℝ)^2)*(1342497/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_424 :
    ∀ u ∈ Set.Icc (53/64:ℝ) (425/512:ℝ), (40053779141744391673/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8262595366883/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(425/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(425/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (53/64:ℝ) (425/512:ℝ) (8262595366883/500000000000:ℝ) (10079703/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1273).1
  intro u hu
  exact (show (40053779141744391673/200000000000000000000000:ℝ) ≤ (1/4-6*(8262595366883/500000000000:ℝ)+4*(8262595366883/500000000000:ℝ)^2)*(10079703/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_425 :
    ∀ u ∈ Set.Icc (425/512:ℝ) (213/256:ℝ), (189456469475912015979/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16589868501593/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(213/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(213/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (425/512:ℝ) (213/256:ℝ) (16589868501593/1000000000000:ℝ) (9457637/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1278).1
  intro u hu
  exact (show (189456469475912015979/1000000000000000000000000:ℝ) ≤ (1/4-6*(16589868501593/1000000000000:ℝ)+4*(16589868501593/1000000000000:ℝ)^2)*(9457637/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_426 :
    ∀ u ∈ Set.Icc (213/256:ℝ) (427/512:ℝ), (179182140372564781941/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8327399705523/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(427/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(427/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (213/256:ℝ) (427/512:ℝ) (8327399705523/500000000000:ℝ) (17743431/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1279).1
  intro u hu
  exact (show (179182140372564781941/1000000000000000000000000:ℝ) ≤ (1/4-6*(8327399705523/500000000000:ℝ)+4*(8327399705523/500000000000:ℝ)^2)*(17743431/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_427 :
    ∀ u ∈ Set.Icc (427/512:ℝ) (107/128:ℝ), (42355413677653710627/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16719984452893/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(107/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(107/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (427/512:ℝ) (107/128:ℝ) (16719984452893/1000000000000:ℝ) (16639957/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1284).1
  intro u hu
  exact (show (42355413677653710627/250000000000000000000000:ℝ) ≤ (1/4-6*(16719984452893/1000000000000:ℝ)+4*(16719984452893/1000000000000:ℝ)^2)*(16639957/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_428 :
    ∀ u ∈ Set.Icc (107/128:ℝ) (429/512:ℝ), (80075860635909528499/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16785424621781/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(429/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(429/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (107/128:ℝ) (429/512:ℝ) (16785424621781/1000000000000:ℝ) (1950141/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1285).1
  intro u hu
  exact (show (80075860635909528499/500000000000000000000000:ℝ) ≤ (1/4-6*(16785424621781/1000000000000:ℝ)+4*(16785424621781/1000000000000:ℝ)^2)*(1950141/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_429 :
    ∀ u ∈ Set.Icc (429/512:ℝ) (215/256:ℝ), (75674989066615317153/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2106390114531/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(215/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(215/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (429/512:ℝ) (215/256:ℝ) (2106390114531/125000000000:ℝ) (14623407/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1290).1
  intro u hu
  exact (show (75674989066615317153/500000000000000000000000:ℝ) ≤ (1/4-6*(2106390114531/125000000000:ℝ)+4*(2106390114531/125000000000:ℝ)^2)*(14623407/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_430 :
    ∀ u ∈ Set.Icc (215/256:ℝ) (431/512:ℝ), (142994966948344169319/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (16917074338741/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(431/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(431/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (215/256:ℝ) (431/512:ℝ) (16917074338741/1000000000000:ℝ) (3425859/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1291).1
  intro u hu
  exact (show (142994966948344169319/1000000000000000000000000:ℝ) ≤ (1/4-6*(16917074338741/1000000000000:ℝ)+4*(16917074338741/1000000000000:ℝ)^2)*(3425859/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_431 :
    ∀ u ∈ Set.Icc (431/512:ℝ) (27/32:ℝ), (67533041812260745961/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1061455368477/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(27/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (431/512:ℝ) (27/32:ℝ) (1061455368477/62500000000:ℝ) (6419013/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1296).1
  intro u hu
  exact (show (67533041812260745961/500000000000000000000000:ℝ) ≤ (1/4-6*(1061455368477/62500000000:ℝ)+4*(1061455368477/62500000000:ℝ)^2)*(6419013/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_432 :
    ∀ u ∈ Set.Icc (27/32:ℝ) (433/512:ℝ), (12754359956592189627/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (17049756597229/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(433/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(433/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (27/32:ℝ) (433/512:ℝ) (17049756597229/1000000000000:ℝ) (6012077/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1297).1
  intro u hu
  exact (show (12754359956592189627/100000000000000000000000:ℝ) ≤ (1/4-6*(17049756597229/1000000000000:ℝ)+4*(17049756597229/1000000000000:ℝ)^2)*(6012077/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_433 :
    ∀ u ∈ Set.Icc (433/512:ℝ) (217/256:ℝ), (30102135937187152831/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4279121864449/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(217/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(217/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (433/512:ℝ) (217/256:ℝ) (4279121864449/250000000000:ℝ) (11258947/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1302).1
  intro u hu
  exact (show (30102135937187152831/250000000000000000000000:ℝ) ≤ (1/4-6*(4279121864449/250000000000:ℝ)+4*(4279121864449/250000000000:ℝ)^2)*(11258947/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_434 :
    ∀ u ∈ Set.Icc (217/256:ℝ) (435/512:ℝ), (28410692966885968931/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (17183479495567/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(435/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(435/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (217/256:ℝ) (435/512:ℝ) (17183479495567/1000000000000:ℝ) (2634921/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1303).1
  intro u hu
  exact (show (28410692966885968931/250000000000000000000000:ℝ) ≤ (1/4-6*(17183479495567/1000000000000:ℝ)+4*(17183479495567/1000000000000:ℝ)^2)*(2634921/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_435 :
    ∀ u ∈ Set.Icc (435/512:ℝ) (109/128:ℝ), (107228885635937195173/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (431268343319/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(109/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (435/512:ℝ) (109/128:ℝ) (431268343319/25000000000:ℝ) (1232973/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1308).1
  intro u hu
  exact (show (107228885635937195173/1000000000000000000000000:ℝ) ≤ (1/4-6*(431268343319/25000000000:ℝ)+4*(431268343319/25000000000:ℝ)^2)*(1232973/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_436 :
    ∀ u ∈ Set.Icc (109/128:ℝ) (437/512:ℝ), (101150201789825405357/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4329562798899/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(437/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(437/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (109/128:ℝ) (437/512:ℝ) (4329562798899/250000000000:ℝ) (9228799/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1309).1
  intro u hu
  exact (show (101150201789825405357/1000000000000000000000000:ℝ) ≤ (1/4-6*(4329562798899/250000000000:ℝ)+4*(4329562798899/250000000000:ℝ)^2)*(9228799/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_437 :
    ∀ u ∈ Set.Icc (437/512:ℝ) (219/256:ℝ), (95390762738773861167/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (17386032914309/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(219/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(219/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (437/512:ℝ) (219/256:ℝ) (17386032914309/1000000000000:ℝ) (8632411/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1314).1
  intro u hu
  exact (show (95390762738773861167/1000000000000000000000000:ℝ) ≤ (1/4-6*(17386032914309/1000000000000:ℝ)+4*(17386032914309/1000000000000:ℝ)^2)*(8632411/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_438 :
    ∀ u ∈ Set.Icc (219/256:ℝ) (439/512:ℝ), (17987049298196460369/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (545439997599/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(439/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(439/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (219/256:ℝ) (439/512:ℝ) (545439997599/31250000000:ℝ) (403621/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1315).1
  intro u hu
  exact (show (17987049298196460369/200000000000000000000000:ℝ) ≤ (1/4-6*(545439997599/31250000000:ℝ)+4*(545439997599/31250000000:ℝ)^2)*(403621/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_439 :
    ∀ u ∈ Set.Icc (439/512:ℝ) (55/64:ℝ), (84769028413781074171/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1752239326049/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (439/512:ℝ) (55/64:ℝ) (1752239326049/100000000000:ℝ) (3773373/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1320).1
  intro u hu
  exact (show (84769028413781074171/1000000000000000000000000:ℝ) ≤ (1/4-6*(1752239326049/100000000000:ℝ)+4*(1752239326049/100000000000:ℝ)^2)*(3773373/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_440 :
    ∀ u ∈ Set.Icc (55/64:ℝ) (441/512:ℝ), (3195123917450644637/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3518194793731/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(441/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(441/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (55/64:ℝ) (441/512:ℝ) (3518194793731/200000000000:ℝ) (3526709/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1321).1
  intro u hu
  exact (show (3195123917450644637/40000000000000000000000:ℝ) ≤ (1/4-6*(3518194793731/200000000000:ℝ)+4*(3518194793731/200000000000:ℝ)^2)*(3526709/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_441 :
    ∀ u ∈ Set.Icc (441/512:ℝ) (221/256:ℝ), (188122596808558179/2500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8829911547061/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(221/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(221/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (441/512:ℝ) (221/256:ℝ) (8829911547061/500000000000:ℝ) (6590569/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1326).1
  intro u hu
  exact (show (188122596808558179/2500000000000000000000:ℝ) ≤ (1/4-6*(8829911547061/500000000000:ℝ)+4*(8829911547061/500000000000:ℝ)^2)*(6590569/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_442 :
    ∀ u ∈ Set.Icc (221/256:ℝ) (443/512:ℝ), (566952332575732811/8000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (17728941687447/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(443/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(443/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (221/256:ℝ) (443/512:ℝ) (17728941687447/1000000000000:ℝ) (3078217/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1327).1
  intro u hu
  exact (show (566952332575732811/8000000000000000000000:ℝ) ≤ (1/4-6*(17728941687447/1000000000000:ℝ)+4*(17728941687447/1000000000000:ℝ)^2)*(3078217/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_443 :
    ∀ u ∈ Set.Icc (443/512:ℝ) (111/128:ℝ), (13345164857540070351/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8899165401649/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (443/512:ℝ) (111/128:ℝ) (8899165401649/500000000000:ℝ) (287467/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1332).1
  intro u hu
  exact (show (13345164857540070351/200000000000000000000000:ℝ) ≤ (1/4-6*(8899165401649/500000000000:ℝ)+4*(8899165401649/500000000000:ℝ)^2)*(287467/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_444 :
    ∀ u ∈ Set.Icc (111/128:ℝ) (445/512:ℝ), (6280768722054132469/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (17867991500469/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(445/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(445/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (111/128:ℝ) (445/512:ℝ) (17867991500469/1000000000000:ℝ) (1341927/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1333).1
  intro u hu
  exact (show (6280768722054132469/100000000000000000000000:ℝ) ≤ (1/4-6*(17867991500469/1000000000000:ℝ)+4*(17867991500469/1000000000000:ℝ)^2)*(1341927/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_445 :
    ∀ u ∈ Set.Icc (445/512:ℝ) (223/256:ℝ), (14775851413730711587/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (17937924841901/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(223/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(223/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (445/512:ℝ) (223/256:ℝ) (17937924841901/1000000000000:ℝ) (5010041/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1338).1
  intro u hu
  exact (show (14775851413730711587/250000000000000000000000:ℝ) ≤ (1/4-6*(17937924841901/1000000000000:ℝ)+4*(17937924841901/1000000000000:ℝ)^2)*(5010041/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_446 :
    ∀ u ∈ Set.Icc (223/256:ℝ) (447/512:ℝ), (27801147271290414531/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (18008131894691/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(447/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(447/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (223/256:ℝ) (447/512:ℝ) (18008131894691/1000000000000:ℝ) (4674927/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1339).1
  intro u hu
  exact (show (27801147271290414531/500000000000000000000000:ℝ) ≤ (1/4-6*(18008131894691/1000000000000:ℝ)+4*(18008131894691/1000000000000:ℝ)^2)*(4674927/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_447 :
    ∀ u ∈ Set.Icc (447/512:ℝ) (7/8:ℝ), (13073532968807063897/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9039306865059/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (447/512:ℝ) (7/8:ℝ) (9039306865059/500000000000:ℝ) (436103/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1344).1
  intro u hu
  exact (show (13073532968807063897/250000000000000000000000:ℝ) ≤ (1/4-6*(9039306865059/500000000000:ℝ)+4*(9039306865059/500000000000:ℝ)^2)*(436103/10000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

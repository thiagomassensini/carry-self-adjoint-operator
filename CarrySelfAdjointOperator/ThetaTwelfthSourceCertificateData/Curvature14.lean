import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_448 :
    ∀ u ∈ Set.Icc (7/8:ℝ) (449/512:ℝ), (24584581102903339971/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (567167856989/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(449/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(449/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/8:ℝ) (449/512:ℝ) (567167856989/31250000000:ℝ) (254193/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1345).1
  intro u hu
  exact (show (24584581102903339971/500000000000000000000000:ℝ) ≤ (1/4-6*(567167856989/31250000000:ℝ)+4*(567167856989/31250000000:ℝ)^2)*(254193/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_449 :
    ∀ u ∈ Set.Icc (449/512:ℝ) (225/256:ℝ), (46218050966034724083/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (18220406054961/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(225/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(225/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (449/512:ℝ) (225/256:ℝ) (18220406054961/1000000000000:ℝ) (3791907/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1350).1
  intro u hu
  exact (show (46218050966034724083/1000000000000000000000000:ℝ) ≤ (1/4-6*(18220406054961/1000000000000:ℝ)+4*(18220406054961/1000000000000:ℝ)^2)*(3791907/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_450 :
    ∀ u ∈ Set.Icc (225/256:ℝ) (451/512:ℝ), (10857980484460440403/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (457292967699/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(451/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(451/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (225/256:ℝ) (451/512:ℝ) (457292967699/25000000000:ℝ) (1767181/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1351).1
  intro u hu
  exact (show (10857980484460440403/250000000000000000000000:ℝ) ≤ (1/4-6*(457292967699/25000000000:ℝ)+4*(457292967699/25000000000:ℝ)^2)*(1767181/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_451 :
    ∀ u ∈ Set.Icc (451/512:ℝ) (113/128:ℝ), (40802309277093263701/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (18363310470791/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(113/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (451/512:ℝ) (113/128:ℝ) (18363310470791/1000000000000:ℝ) (3293391/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1356).1
  intro u hu
  exact (show (40802309277093263701/1000000000000000000000000:ℝ) ≤ (1/4-6*(18363310470791/1000000000000:ℝ)+4*(18363310470791/1000000000000:ℝ)^2)*(3293391/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_452 :
    ∀ u ∈ Set.Icc (113/128:ℝ) (453/512:ℝ), (9580276645360851979/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (18435182435859/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(453/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(453/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (113/128:ℝ) (453/512:ℝ) (18435182435859/1000000000000:ℝ) (3067989/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1357).1
  intro u hu
  exact (show (9580276645360851979/250000000000000000000000:ℝ) ≤ (1/4-6*(18435182435859/1000000000000:ℝ)+4*(18435182435859/1000000000000:ℝ)^2)*(3067989/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_453 :
    ∀ u ∈ Set.Icc (453/512:ℝ) (227/256:ℝ), (719612273135570069/20000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3701467139969/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(227/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(227/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (453/512:ℝ) (227/256:ℝ) (3701467139969/200000000000:ℝ) (285721/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1362).1
  intro u hu
  exact (show (719612273135570069/20000000000000000000000:ℝ) ≤ (1/4-6*(3701467139969/200000000000:ℝ)+4*(3701467139969/200000000000:ℝ)^2)*(285721/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_454 :
    ∀ u ∈ Set.Icc (227/256:ℝ) (455/512:ℝ), (33773470833088802241/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9289885681861/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(455/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(455/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (227/256:ℝ) (455/512:ℝ) (9289885681861/500000000000:ℝ) (8313/312500000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1363).1
  intro u hu
  exact (show (33773470833088802241/1000000000000000000000000:ℝ) ≤ (1/4-6*(9289885681861/500000000000:ℝ)+4*(9289885681861/500000000000:ℝ)^2)*(8313/312500000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_455 :
    ∀ u ∈ Set.Icc (455/512:ℝ) (57/64:ℝ), (7923176181761866589/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4663122633193/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (455/512:ℝ) (57/64:ℝ) (4663122633193/250000000000:ℝ) (2475999/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1368).1
  intro u hu
  exact (show (7923176181761866589/250000000000000000000000:ℝ) ≤ (1/4-6*(4663122633193/250000000000:ℝ)+4*(4663122633193/250000000000:ℝ)^2)*(2475999/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_456 :
    ∀ u ∈ Set.Icc (57/64:ℝ) (457/512:ℝ), (3716451004630729741/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (18725494316601/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(457/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(457/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (57/64:ℝ) (457/512:ℝ) (18725494316601/1000000000000:ℝ) (230393/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1369).1
  intro u hu
  exact (show (3716451004630729741/125000000000000000000000:ℝ) ≤ (1/4-6*(18725494316601/1000000000000:ℝ)+4*(18725494316601/1000000000000:ℝ)^2)*(230393/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_457 :
    ∀ u ∈ Set.Icc (457/512:ℝ) (229/256:ℝ), (435685314641347487/15625000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9399391914581/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(229/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(229/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (457/512:ℝ) (229/256:ℝ) (9399391914581/500000000000:ℝ) (2143207/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1374).1
  intro u hu
  exact (show (435685314641347487/15625000000000000000000:ℝ) ≤ (1/4-6*(9399391914581/500000000000:ℝ)+4*(9399391914581/500000000000:ℝ)^2)*(2143207/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_458 :
    ∀ u ∈ Set.Icc (229/256:ℝ) (459/512:ℝ), (26143417121733651497/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3774472037753/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(459/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(459/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (229/256:ℝ) (459/512:ℝ) (3774472037753/200000000000:ℝ) (3189/160000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1375).1
  intro u hu
  exact (show (26143417121733651497/1000000000000000000000000:ℝ) ≤ (1/4-6*(3774472037753/200000000000:ℝ)+4*(3774472037753/200000000000:ℝ)^2)*(3189/160000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_459 :
    ∀ u ∈ Set.Icc (459/512:ℝ) (115/128:ℝ), (24504501761032275709/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9473112259049/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (459/512:ℝ) (115/128:ℝ) (9473112259049/500000000000:ℝ) (926509/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1380).1
  intro u hu
  exact (show (24504501761032275709/1000000000000000000000000:ℝ) ≤ (1/4-6*(9473112259049/500000000000:ℝ)+4*(9473112259049/500000000000:ℝ)^2)*(926509/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_460 :
    ∀ u ∈ Set.Icc (115/128:ℝ) (461/512:ℝ), (4592334517383534719/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19020377944241/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(461/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(461/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (115/128:ℝ) (461/512:ℝ) (19020377944241/1000000000000:ℝ) (1722263/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1381).1
  intro u hu
  exact (show (4592334517383534719/200000000000000000000000:ℝ) ≤ (1/4-6*(19020377944241/1000000000000:ℝ)+4*(19020377944241/1000000000000:ℝ)^2)*(1722263/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_461 :
    ∀ u ∈ Set.Icc (461/512:ℝ) (231/256:ℝ), (21509694396691431421/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (596713174959/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(231/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(231/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (461/512:ℝ) (231/256:ℝ) (596713174959/31250000000:ℝ) (1600269/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1386).1
  intro u hu
  exact (show (21509694396691431421/1000000000000000000000000:ℝ) ≤ (1/4-6*(596713174959/31250000000:ℝ)+4*(596713174959/31250000000:ℝ)^2)*(1600269/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_462 :
    ∀ u ∈ Set.Icc (231/256:ℝ) (463/512:ℝ), (2517955737992315821/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19169556617361/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(463/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(463/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (231/256:ℝ) (463/512:ℝ) (19169556617361/1000000000000:ℝ) (371621/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1387).1
  intro u hu
  exact (show (2517955737992315821/125000000000000000000000:ℝ) ≤ (1/4-6*(19169556617361/1000000000000:ℝ)+4*(19169556617361/1000000000000:ℝ)^2)*(371621/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_463 :
    ∀ u ∈ Set.Icc (463/512:ℝ) (29/32:ℝ), (589337504137818281/31250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9622292070313/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (463/512:ℝ) (29/32:ℝ) (9622292070313/500000000000:ℝ) (276077/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1392).1
  intro u hu
  exact (show (589337504137818281/31250000000000000000000:ℝ) ≤ (1/4-6*(9622292070313/500000000000:ℝ)+4*(9622292070313/500000000000:ℝ)^2)*(276077/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_464 :
    ∀ u ∈ Set.Icc (29/32:ℝ) (465/512:ℝ), (1103169072384304323/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3863981062663/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(465/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(465/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (29/32:ℝ) (465/512:ℝ) (3863981062663/200000000000:ℝ) (1281483/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1393).1
  intro u hu
  exact (show (1103169072384304323/62500000000000000000000:ℝ) ≤ (1/4-6*(3863981062663/200000000000:ℝ)+4*(3863981062663/200000000000:ℝ)^2)*(1281483/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_465 :
    ∀ u ∈ Set.Icc (465/512:ℝ) (233/256:ℝ), (8257550955968549439/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19395521284739/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(233/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(233/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (465/512:ℝ) (233/256:ℝ) (19395521284739/1000000000000:ℝ) (297329/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1398).1
  intro u hu
  exact (show (8257550955968549439/500000000000000000000000:ℝ) ≤ (1/4-6*(19395521284739/1000000000000:ℝ)+4*(19395521284739/1000000000000:ℝ)^2)*(297329/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_466 :
    ∀ u ∈ Set.Icc (233/256:ℝ) (467/512:ℝ), (15447963605229410411/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19471433208707/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(467/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(467/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (233/256:ℝ) (467/512:ℝ) (19471433208707/1000000000000:ℝ) (1103451/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1399).1
  intro u hu
  exact (show (15447963605229410411/1000000000000000000000000:ℝ) ≤ (1/4-6*(19471433208707/1000000000000:ℝ)+4*(19471433208707/1000000000000:ℝ)^2)*(1103451/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_467 :
    ∀ u ∈ Set.Icc (467/512:ℝ) (117/128:ℝ), (14445480376358809353/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3909528448709/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(117/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(117/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (467/512:ℝ) (117/128:ℝ) (3909528448709/200000000000:ℝ) (511741/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1404).1
  intro u hu
  exact (show (14445480376358809353/1000000000000000000000000:ℝ) ≤ (1/4-6*(3909528448709/200000000000:ℝ)+4*(3909528448709/200000000000:ℝ)^2)*(511741/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_468 :
    ∀ u ∈ Set.Icc (117/128:ℝ) (469/512:ℝ), (3376000050664325273/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1226509347007/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(469/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(469/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (117/128:ℝ) (469/512:ℝ) (1226509347007/62500000000:ℝ) (37961/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1405).1
  intro u hu
  exact (show (3376000050664325273/250000000000000000000000:ℝ) ≤ (1/4-6*(1226509347007/62500000000:ℝ)+4*(1226509347007/62500000000:ℝ)^2)*(37961/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_469 :
    ∀ u ∈ Set.Icc (469/512:ℝ) (235/256:ℝ), (6310040703464386403/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9850478150909/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(235/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(235/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (469/512:ℝ) (235/256:ℝ) (9850478150909/500000000000:ℝ) (879721/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1410).1
  intro u hu
  exact (show (6310040703464386403/500000000000000000000000:ℝ) ≤ (1/4-6*(9850478150909/500000000000:ℝ)+4*(9850478150909/500000000000:ℝ)^2)*(879721/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_470 :
    ∀ u ∈ Set.Icc (235/256:ℝ) (471/512:ℝ), (589523037444283507/50000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19778063664643/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(471/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(471/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (235/256:ℝ) (471/512:ℝ) (19778063664643/1000000000000:ℝ) (815233/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1411).1
  intro u hu
  exact (show (589523037444283507/50000000000000000000000:ℝ) ≤ (1/4-6*(19778063664643/1000000000000:ℝ)+4*(19778063664643/1000000000000:ℝ)^2)*(815233/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_471 :
    ∀ u ∈ Set.Icc (471/512:ℝ) (59/64:ℝ), (11012034271656253791/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (19855472817153/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (471/512:ℝ) (59/64:ℝ) (19855472817153/1000000000000:ℝ) (188811/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1416).1
  intro u hu
  exact (show (11012034271656253791/1000000000000000000000000:ℝ) ≤ (1/4-6*(19855472817153/1000000000000:ℝ)+4*(19855472817153/1000000000000:ℝ)^2)*(188811/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_472 :
    ∀ u ∈ Set.Icc (59/64:ℝ) (473/512:ℝ), (2056376216470054499/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (498329623513/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(473/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(473/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (59/64:ℝ) (473/512:ℝ) (498329623513/25000000000:ℝ) (349729/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1417).1
  intro u hu
  exact (show (2056376216470054499/200000000000000000000000:ℝ) ≤ (1/4-6*(498329623513/25000000000:ℝ)+4*(498329623513/25000000000:ℝ)^2)*(349729/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_473 :
    ∀ u ∈ Set.Icc (473/512:ℝ) (237/256:ℝ), (2343066204438221/244140625000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10005600610269/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(237/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(237/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (473/512:ℝ) (237/256:ℝ) (10005600610269/500000000000:ℝ) (129519/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1422).1
  intro u hu
  exact (show (2343066204438221/244140625000000000000:ℝ) ≤ (1/4-6*(10005600610269/500000000000:ℝ)+4*(10005600610269/500000000000:ℝ)^2)*(129519/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_474 :
    ∀ u ∈ Set.Icc (237/256:ℝ) (475/512:ℝ), (8955372340503951647/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (20089522847643/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(475/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(475/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (237/256:ℝ) (475/512:ℝ) (20089522847643/1000000000000:ℝ) (119879/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1423).1
  intro u hu
  exact (show (8955372340503951647/1000000000000000000000000:ℝ) ≤ (1/4-6*(20089522847643/1000000000000:ℝ)+4*(20089522847643/1000000000000:ℝ)^2)*(119879/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_475 :
    ∀ u ∈ Set.Icc (475/512:ℝ) (119/128:ℝ), (8353889591520146871/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (630254719279/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(119/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(119/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (475/512:ℝ) (119/128:ℝ) (630254719279/31250000000:ℝ) (138653/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1428).1
  intro u hu
  exact (show (8353889591520146871/1000000000000000000000000:ℝ) ≤ (1/4-6*(630254719279/31250000000:ℝ)+4*(630254719279/31250000000:ℝ)^2)*(138653/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_476 :
    ∀ u ∈ Set.Icc (119/128:ℝ) (477/512:ℝ), (7790397053757855993/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2530885866021/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(477/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(477/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (119/128:ℝ) (477/512:ℝ) (2530885866021/125000000000:ℝ) (513017/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1429).1
  intro u hu
  exact (show (7790397053757855993/1000000000000000000000000:ℝ) ≤ (1/4-6*(2530885866021/125000000000:ℝ)+4*(2530885866021/125000000000:ℝ)^2)*(513017/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_477 :
    ∀ u ∈ Set.Icc (477/512:ℝ) (239/256:ℝ), (1452532084929160941/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5081582946457/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(239/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(239/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (477/512:ℝ) (239/256:ℝ) (5081582946457/250000000000:ℝ) (94879/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1434).1
  intro u hu
  exact (show (1452532084929160941/200000000000000000000000:ℝ) ≤ (1/4-6*(5081582946457/250000000000:ℝ)+4*(5081582946457/250000000000:ℝ)^2)*(94879/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_478 :
    ∀ u ∈ Set.Icc (239/256:ℝ) (479/512:ℝ), (6768571694957169177/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (20405886799093/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(479/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(479/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (239/256:ℝ) (479/512:ℝ) (20405886799093/1000000000000:ℝ) (87709/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1435).1
  intro u hu
  exact (show (6768571694957169177/1000000000000000000000000:ℝ) ≤ (1/4-6*(20405886799093/1000000000000:ℝ)+4*(20405886799093/1000000000000:ℝ)^2)*(87709/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_479 :
    ∀ u ∈ Set.Icc (479/512:ℝ) (15/16:ℝ), (3153062464355029157/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (32777205091/1600000000:ℝ) ≤ Real.pi*Real.exp (2*(15/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (479/512:ℝ) (15/16:ℝ) (32777205091/1600000000:ℝ) (202639/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1440).1
  intro u hu
  exact (show (3153062464355029157/500000000000000000000000:ℝ) ≤ (1/4-6*(32777205091/1600000000:ℝ)+4*(32777205091/1600000000:ℝ)^2)*(202639/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

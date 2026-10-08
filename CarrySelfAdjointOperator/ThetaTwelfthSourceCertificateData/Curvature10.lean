import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_320 :
    ∀ u ∈ Set.Icc (5/8:ℝ) (321/512:ℝ), (18989797966138220160881/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2201630044591/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(321/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(321/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/8:ℝ) (321/512:ℝ) (2201630044591/200000000000:ℝ) (4533052171/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0961).1
  intro u hu
  exact (show (18989797966138220160881/1000000000000000000000000:ℝ) ≤ (1/4-6*(2201630044591/200000000000:ℝ)+4*(2201630044591/200000000000:ℝ)^2)*(4533052171/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_321 :
    ∀ u ∈ Set.Icc (321/512:ℝ) (161/256:ℝ), (18360765920791664960263/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11051234904747/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(161/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(161/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (321/512:ℝ) (161/256:ℝ) (11051234904747/1000000000000:ℝ) (2173068377/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0966).1
  intro u hu
  exact (show (18360765920791664960263/1000000000000000000000000:ℝ) ≤ (1/4-6*(11051234904747/1000000000000:ℝ)+4*(11051234904747/1000000000000:ℝ)^2)*(2173068377/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_322 :
    ∀ u ∈ Set.Icc (161/256:ℝ) (323/512:ℝ), (2218691076948617867173/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11094488215217/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(323/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(323/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (161/256:ℝ) (323/512:ℝ) (11094488215217/1000000000000:ℝ) (65097281/1562500000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0967).1
  intro u hu
  exact (show (2218691076948617867173/125000000000000000000000:ℝ) ≤ (1/4-6*(11094488215217/1000000000000:ℝ)+4*(11094488215217/1000000000000:ℝ)^2)*(65097281/1562500000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_323 :
    ∀ u ∈ Set.Icc (323/512:ℝ) (81/128:ℝ), (17155688547831666497587/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2784477703589/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(81/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (323/512:ℝ) (81/128:ℝ) (2784477703589/250000000000:ℝ) (99827167/2500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0972).1
  intro u hu
  exact (show (17155688547831666497587/1000000000000000000000000:ℝ) ≤ (1/4-6*(2784477703589/250000000000:ℝ)+4*(2784477703589/250000000000:ℝ)^2)*(99827167/2500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_324 :
    ∀ u ∈ Set.Icc (81/128:ℝ) (325/512:ℝ), (4144713437913322237179/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1397687920593/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(325/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(325/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (81/128:ℝ) (325/512:ℝ) (1397687920593/125000000000:ℝ) (478311537/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0973).1
  intro u hu
  exact (show (4144713437913322237179/250000000000000000000000:ℝ) ≤ (1/4-6*(1397687920593/125000000000:ℝ)+4*(1397687920593/125000000000:ℝ)^2)*(478311537/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_325 :
    ∀ u ∈ Set.Icc (325/512:ℝ) (163/256:ℝ), (16018637837795994942557/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (224505330631/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(163/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(163/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (325/512:ℝ) (163/256:ℝ) (224505330631/20000000000:ℝ) (458277847/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0978).1
  intro u hu
  exact (show (16018637837795994942557/1000000000000000000000000:ℝ) ≤ (1/4-6*(224505330631/20000000000:ℝ)+4*(224505330631/20000000000:ℝ)^2)*(458277847/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_326 :
    ∀ u ∈ Set.Icc (163/256:ℝ) (327/512:ℝ), (7737329995450590364139/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2817300245637/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(327/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(327/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (163/256:ℝ) (327/512:ℝ) (2817300245637/250000000000:ℝ) (1756032201/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0979).1
  intro u hu
  exact (show (7737329995450590364139/500000000000000000000000:ℝ) ≤ (1/4-6*(2817300245637/250000000000:ℝ)+4*(2817300245637/250000000000:ℝ)^2)*(1756032201/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_327 :
    ∀ u ∈ Set.Icc (327/512:ℝ) (41/64:ℝ), (3736636247141410437059/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (18101291821/1600000000:ℝ) ≤ Real.pi*Real.exp (2*(41/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (327/512:ℝ) (41/64:ℝ) (18101291821/1600000000:ℝ) (67276193/2000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0984).1
  intro u hu
  exact (show (3736636247141410437059/250000000000000000000000:ℝ) ≤ (1/4-6*(18101291821/1600000000:ℝ)+4*(18101291821/1600000000:ℝ)^2)*(67276193/2000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_328 :
    ∀ u ∈ Set.Icc (41/64:ℝ) (329/512:ℝ), (2886784644269605718733/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11357586421293/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(329/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(329/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (41/64:ℝ) (329/512:ℝ) (11357586421293/1000000000000:ℝ) (3221257049/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0985).1
  intro u hu
  exact (show (2886784644269605718733/200000000000000000000000:ℝ) ≤ (1/4-6*(11357586421293/1000000000000:ℝ)+4*(11357586421293/1000000000000:ℝ)^2)*(3221257049/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_329 :
    ∀ u ∈ Set.Icc (329/512:ℝ) (165/256:ℝ), (1742053836423642278459/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11402038757697/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(165/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(165/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (329/512:ℝ) (165/256:ℝ) (11402038757697/1000000000000:ℝ) (1542105519/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0990).1
  intro u hu
  exact (show (1742053836423642278459/125000000000000000000000:ℝ) ≤ (1/4-6*(11402038757697/1000000000000:ℝ)+4*(11402038757697/1000000000000:ℝ)^2)*(1542105519/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_330 :
    ∀ u ∈ Set.Icc (165/256:ℝ) (331/512:ℝ), (6726854505705281028953/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5723332537813/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(331/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(331/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (165/256:ℝ) (331/512:ℝ) (5723332537813/500000000000:ℝ) (1476240913/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0991).1
  intro u hu
  exact (show (6726854505705281028953/500000000000000000000000:ℝ) ≤ (1/4-6*(5723332537813/500000000000:ℝ)+4*(5723332537813/500000000000:ℝ)^2)*(1476240913/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_331 :
    ∀ u ∈ Set.Icc (331/512:ℝ) (83/128:ℝ), (2597081084548014810409/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (459658642241/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(83/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(83/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (331/512:ℝ) (83/128:ℝ) (459658642241/40000000000:ℝ) (2825885259/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0996).1
  intro u hu
  exact (show (2597081084548014810409/200000000000000000000000:ℝ) ≤ (1/4-6*(459658642241/40000000000:ℝ)+4*(459658642241/40000000000:ℝ)^2)*(2825885259/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_332 :
    ∀ u ∈ Set.Icc (83/128:ℝ) (333/512:ℝ), (2506234554697104736573/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1442055297813/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(333/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(333/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (83/128:ℝ) (333/512:ℝ) (1442055297813/125000000000:ℝ) (2704242681/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0997).1
  intro u hu
  exact (show (2506234554697104736573/200000000000000000000000:ℝ) ≤ (1/4-6*(1442055297813/125000000000:ℝ)+4*(1442055297813/125000000000:ℝ)^2)*(2704242681/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_333 :
    ∀ u ∈ Set.Icc (333/512:ℝ) (167/256:ℝ), (12090669538846831606073/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11581594741347/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(167/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(167/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (333/512:ℝ) (167/256:ℝ) (11581594741347/1000000000000:ℝ) (2587380807/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1002).1
  intro u hu
  exact (show (12090669538846831606073/1000000000000000000000000:ℝ) ≤ (1/4-6*(11581594741347/1000000000000:ℝ)+4*(11581594741347/1000000000000:ℝ)^2)*(2587380807/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_334 :
    ∀ u ∈ Set.Icc (167/256:ℝ) (335/512:ℝ), (11663559777958023968721/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11626923821527/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(335/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(335/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (167/256:ℝ) (335/512:ℝ) (11626923821527/1000000000000:ℝ) (495026317/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1003).1
  intro u hu
  exact (show (11663559777958023968721/1000000000000000000000000:ℝ) ≤ (1/4-6*(11626923821527/1000000000000:ℝ)+4*(11626923821527/1000000000000:ℝ)^2)*(495026317/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_335 :
    ∀ u ∈ Set.Icc (335/512:ℝ) (21/32:ℝ), (449980526649808350319/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11672430314709/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (335/512:ℝ) (21/32:ℝ) (11672430314709/1000000000000:ℝ) (2367332077/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1008).1
  intro u hu
  exact (show (449980526649808350319/40000000000000000000000:ℝ) ≤ (1/4-6*(11672430314709/1000000000000:ℝ)+4*(11672430314709/1000000000000:ℝ)^2)*(2367332077/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_336 :
    ∀ u ∈ Set.Icc (21/32:ℝ) (337/512:ℝ), (2712051236299203677233/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11718114915271/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(337/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(337/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (21/32:ℝ) (337/512:ℝ) (11718114915271/1000000000000:ℝ) (90552973/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1009).1
  intro u hu
  exact (show (2712051236299203677233/250000000000000000000000:ℝ) ≤ (1/4-6*(11718114915271/1000000000000:ℝ)+4*(11718114915271/1000000000000:ℝ)^2)*(90552973/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_337 :
    ∀ u ∈ Set.Icc (337/512:ℝ) (169/256:ℝ), (1045931593457899070031/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11763978320303/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(169/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(169/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (337/512:ℝ) (169/256:ℝ) (11763978320303/1000000000000:ℝ) (2164455233/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1014).1
  intro u hu
  exact (show (1045931593457899070031/100000000000000000000000:ℝ) ≤ (1/4-6*(11763978320303/1000000000000:ℝ)+4*(11763978320303/1000000000000:ℝ)^2)*(2164455233/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_338 :
    ∀ u ∈ Set.Icc (169/256:ℝ) (339/512:ℝ), (5041266247114722322963/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2952505307407/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(339/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(339/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (169/256:ℝ) (339/512:ℝ) (2952505307407/250000000000:ℝ) (2069076441/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1015).1
  intro u hu
  exact (show (5041266247114722322963/500000000000000000000000:ℝ) ≤ (1/4-6*(2952505307407/250000000000:ℝ)+4*(2952505307407/250000000000:ℝ)^2)*(2069076441/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_339 :
    ∀ u ∈ Set.Icc (339/512:ℝ) (85/128:ℝ), (9717546511209071045359/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2964061086451/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(85/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (339/512:ℝ) (85/128:ℝ) (2964061086451/250000000000:ℝ) (1977544207/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1020).1
  intro u hu
  exact (show (9717546511209071045359/1000000000000000000000000:ℝ) ≤ (1/4-6*(2964061086451/250000000000:ℝ)+4*(2964061086451/250000000000:ℝ)^2)*(1977544207/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_340 :
    ∀ u ∈ Set.Icc (85/128:ℝ) (341/512:ℝ), (1170506923053822489801/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5951324187071/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(341/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(341/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (85/128:ℝ) (341/512:ℝ) (5951324187071/500000000000:ℝ) (1889719291/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1021).1
  intro u hu
  exact (show (1170506923053822489801/125000000000000000000000:ℝ) ≤ (1/4-6*(5951324187071/500000000000:ℝ)+4*(5951324187071/500000000000:ℝ)^2)*(1889719291/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_341 :
    ∀ u ∈ Set.Icc (341/512:ℝ) (171/256:ℝ), (902176198681593383143/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11949234022711/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(171/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(171/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (341/512:ℝ) (171/256:ℝ) (11949234022711/1000000000000:ℝ) (1805466837/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1026).1
  intro u hu
  exact (show (902176198681593383143/100000000000000000000000:ℝ) ≤ (1/4-6*(11949234022711/1000000000000:ℝ)+4*(11949234022711/1000000000000:ℝ)^2)*(1805466837/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_342 :
    ∀ u ∈ Set.Icc (171/256:ℝ) (343/512:ℝ), (4345187324651066737441/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5998001001177/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(343/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(343/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (171/256:ℝ) (343/512:ℝ) (5998001001177/500000000000:ℝ) (862328131/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1027).1
  intro u hu
  exact (show (4345187324651066737441/500000000000000000000000:ℝ) ≤ (1/4-6*(5998001001177/500000000000:ℝ)+4*(5998001001177/500000000000:ℝ)^2)*(862328131/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_343 :
    ∀ u ∈ Set.Icc (343/512:ℝ) (43/64:ℝ), (4184803553622849574231/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6021476513347/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (343/512:ℝ) (43/64:ℝ) (6021476513347/500000000000:ℝ) (82358057/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1032).1
  intro u hu
  exact (show (4184803553622849574231/500000000000000000000000:ℝ) ≤ (1/4-6*(6021476513347/500000000000:ℝ)+4*(6021476513347/500000000000:ℝ)^2)*(82358057/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_344 :
    ∀ u ∈ Set.Icc (43/64:ℝ) (345/512:ℝ), (8059178514888556234447/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12090087812147/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(345/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(345/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (43/64:ℝ) (345/512:ℝ) (12090087812147/1000000000000:ℝ) (786429551/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1033).1
  intro u hu
  exact (show (8059178514888556234447/1000000000000000000000000:ℝ) ≤ (1/4-6*(12090087812147/1000000000000:ℝ)+4*(12090087812147/1000000000000:ℝ)^2)*(786429551/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_345 :
    ∀ u ∈ Set.Icc (345/512:ℝ) (173/256:ℝ), (12123145869520086023/1562500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2427481415587/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(173/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(173/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (345/512:ℝ) (173/256:ℝ) (2427481415587/200000000000:ℝ) (750815859/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1038).1
  intro u hu
  exact (show (12123145869520086023/1562500000000000000000:ℝ) ≤ (1/4-6*(2427481415587/200000000000:ℝ)+4*(2427481415587/200000000000:ℝ)^2)*(750815859/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_346 :
    ∀ u ∈ Set.Icc (173/256:ℝ) (347/512:ℝ), (466765090716006631209/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12184911546093/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(347/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(347/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (173/256:ℝ) (347/512:ℝ) (12184911546093/1000000000000:ℝ) (3583411/250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1039).1
  intro u hu
  exact (show (466765090716006631209/62500000000000000000000:ℝ) ≤ (1/4-6*(12184911546093/1000000000000:ℝ)+4*(12184911546093/1000000000000:ℝ)^2)*(3583411/250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_347 :
    ∀ u ∈ Set.Icc (347/512:ℝ) (87/128:ℝ), (3593598945580688865067/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6116300970741/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(87/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (347/512:ℝ) (87/128:ℝ) (6116300970741/500000000000:ℝ) (683973147/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1044).1
  intro u hu
  exact (show (3593598945580688865067/500000000000000000000000:ℝ) ≤ (1/4-6*(6116300970741/500000000000:ℝ)+4*(6116300970741/500000000000:ℝ)^2)*(683973147/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_348 :
    ∀ u ∈ Set.Icc (87/128:ℝ) (349/512:ℝ), (1383084605119152080019/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12280478991801/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(349/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(349/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (87/128:ℝ) (349/512:ℝ) (12280478991801/1000000000000:ℝ) (163158773/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1045).1
  intro u hu
  exact (show (1383084605119152080019/200000000000000000000000:ℝ) ≤ (1/4-6*(12280478991801/1000000000000:ℝ)+4*(12280478991801/1000000000000:ℝ)^2)*(163158773/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_349 :
    ∀ u ∈ Set.Icc (349/512:ℝ) (175/256:ℝ), (415791399088820588141/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3082135856899/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(175/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(175/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (349/512:ℝ) (175/256:ℝ) (3082135856899/250000000000:ℝ) (622616193/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1050).1
  intro u hu
  exact (show (415791399088820588141/62500000000000000000000:ℝ) ≤ (1/4-6*(3082135856899/250000000000:ℝ)+4*(3082135856899/250000000000:ℝ)^2)*(622616193/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_350 :
    ∀ u ∈ Set.Icc (175/256:ℝ) (351/512:ℝ), (3199333338005062984983/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (495071839291/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(351/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(351/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (175/256:ℝ) (351/512:ℝ) (495071839291/40000000000:ℝ) (593866329/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1051).1
  intro u hu
  exact (show (3199333338005062984983/500000000000000000000000:ℝ) ≤ (1/4-6*(495071839291/40000000000:ℝ)+4*(495071839291/40000000000:ℝ)^2)*(593866329/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_351 :
    ∀ u ∈ Set.Icc (351/512:ℝ) (11/16:ℝ), (1538297928038724187807/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12425237392113/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (351/512:ℝ) (11/16:ℝ) (12425237392113/1000000000000:ℝ) (1132674101/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1056).1
  intro u hu
  exact (show (1538297928038724187807/250000000000000000000000:ℝ) ≤ (1/4-6*(12425237392113/1000000000000:ℝ)+4*(12425237392113/1000000000000:ℝ)^2)*(1132674101/100000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

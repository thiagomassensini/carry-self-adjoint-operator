import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_032 :
    ∀ u ∈ Set.Icc (1/16:ℝ) (33/512:ℝ), (432997527252346110519427/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3573823130933/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/16:ℝ) (33/512:ℝ) (3573823130933/1000000000000:ℝ) (1448350466289/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0097).1
  intro u hu
  exact (show (432997527252346110519427/250000000000000000000000:ℝ) ≤ (1/4-6*(3573823130933/1000000000000:ℝ)+4*(3573823130933/1000000000000:ℝ)^2)*(1448350466289/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_033 :
    ∀ u ∈ Set.Icc (33/512:ℝ) (17/256:ℝ), (215964459059113710098031/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3587810679183/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (33/512:ℝ) (17/256:ℝ) (3587810679183/1000000000000:ℝ) (2859256110477/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0102).1
  intro u hu
  exact (show (215964459059113710098031/125000000000000000000000:ℝ) ≤ (1/4-6*(3587810679183/1000000000000:ℝ)+4*(3587810679183/1000000000000:ℝ)^2)*(2859256110477/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_034 :
    ∀ u ∈ Set.Icc (17/256:ℝ) (35/512:ℝ), (1723326832846077234256913/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (900463243287/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (17/256:ℝ) (35/512:ℝ) (900463243287/250000000000:ℝ) (1411070411223/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0103).1
  intro u hu
  exact (show (1723326832846077234256913/1000000000000000000000000:ℝ) ≤ (1/4-6*(900463243287/250000000000:ℝ)+4*(900463243287/250000000000:ℝ)^2)*(1411070411223/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_035 :
    ∀ u ∈ Set.Icc (35/512:ℝ) (9/128:ℝ), (859412213423130417653039/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1807975113549/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (35/512:ℝ) (9/128:ℝ) (1807975113549/500000000000:ℝ) (13926771157/250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0108).1
  intro u hu
  exact (show (859412213423130417653039/500000000000000000000000:ℝ) ≤ (1/4-6*(1807975113549/500000000000:ℝ)+4*(1807975113549/500000000000:ℝ)^2)*(13926771157/250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_036 :
    ∀ u ∈ Set.Icc (9/128:ℝ) (37/512:ℝ), (13713674475179974256373/8000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (181505132807/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (9/128:ℝ) (37/512:ℝ) (181505132807/50000000000:ℝ) (2748895478593/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0109).1
  intro u hu
  exact (show (13713674475179974256373/8000000000000000000000:ℝ) ≤ (1/4-6*(181505132807/50000000000:ℝ)+4*(181505132807/50000000000:ℝ)^2)*(2748895478593/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_037 :
    ∀ u ∈ Set.Icc (37/512:ℝ) (19/256:ℝ), (1709482353465349946201123/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3644310476223/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (37/512:ℝ) (19/256:ℝ) (3644310476223/1000000000000:ℝ) (1356381841877/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0114).1
  intro u hu
  exact (show (1709482353465349946201123/1000000000000000000000000:ℝ) ≤ (1/4-6*(3644310476223/1000000000000:ℝ)+4*(3644310476223/1000000000000:ℝ)^2)*(1356381841877/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_038 :
    ∀ u ∈ Set.Icc (19/256:ℝ) (39/512:ℝ), (1704644449940327522104199/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3658573904141/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (19/256:ℝ) (39/512:ℝ) (3658573904141/1000000000000:ℝ) (2676957945317/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0115).1
  intro u hu
  exact (show (1704644449940327522104199/1000000000000000000000000:ℝ) ≤ (1/4-6*(3658573904141/1000000000000:ℝ)+4*(3658573904141/1000000000000:ℝ)^2)*(2676957945317/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_039 :
    ∀ u ∈ Set.Icc (39/512:ℝ) (5/64:ℝ), (849848253722663298519713/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1836446578769/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (39/512:ℝ) (5/64:ℝ) (1836446578769/500000000000:ℝ) (2641477340537/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0120).1
  intro u hu
  exact (show (849848253722663298519713/500000000000000000000000:ℝ) ≤ (1/4-6*(1836446578769/500000000000:ℝ)+4*(1836446578769/500000000000:ℝ)^2)*(2641477340537/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_040 :
    ∀ u ∈ Set.Icc (5/64:ℝ) (41/512:ℝ), (1694639452171312002093737/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (921817113727/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/64:ℝ) (41/512:ℝ) (921817113727/250000000000:ℝ) (1303160462837/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0121).1
  intro u hu
  exact (show (1694639452171312002093737/1000000000000000000000000:ℝ) ≤ (1/4-6*(921817113727/250000000000:ℝ)+4*(921817113727/250000000000:ℝ)^2)*(1303160462837/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_041 :
    ∀ u ∈ Set.Icc (41/512:ℝ) (21/256:ℝ), (1689474227727350749544013/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1850850007801/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (41/512:ℝ) (21/256:ℝ) (1850850007801/500000000000:ℝ) (5142975472393/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0126).1
  intro u hu
  exact (show (1689474227727350749544013/1000000000000000000000000:ℝ) ≤ (1/4-6*(1850850007801/500000000000:ℝ)+4*(1850850007801/500000000000:ℝ)^2)*(5142975472393/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_042 :
    ∀ u ∈ Set.Icc (21/256:ℝ) (43/512:ℝ), (1684201794927974646282499/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1858094029913/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (21/256:ℝ) (43/512:ℝ) (1858094029913/500000000000:ℝ) (2536976786917/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0127).1
  intro u hu
  exact (show (1684201794927974646282499/1000000000000000000000000:ℝ) ≤ (1/4-6*(1858094029913/500000000000:ℝ)+4*(1858094029913/500000000000:ℝ)^2)*(2536976786917/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_043 :
    ∀ u ∈ Set.Icc (43/512:ℝ) (11/128:ℝ), (335764626330188313888433/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3730732808653/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (43/512:ℝ) (11/128:ℝ) (3730732808653/1000000000000:ℝ) (2502787072221/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0132).1
  intro u hu
  exact (show (335764626330188313888433/200000000000000000000000:ℝ) ≤ (1/4-6*(3730732808653/1000000000000:ℝ)+4*(3730732808653/1000000000000:ℝ)^2)*(2502787072221/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_044 :
    ∀ u ∈ Set.Icc (11/128:ℝ) (45/512:ℝ), (1673339232620103013215101/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3745334484017/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (11/128:ℝ) (45/512:ℝ) (3745334484017/1000000000000:ℝ) (1234458783113/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0133).1
  intro u hu
  exact (show (1673339232620103013215101/1000000000000000000000000:ℝ) ≤ (1/4-6*(3745334484017/1000000000000:ℝ)+4*(3745334484017/1000000000000:ℝ)^2)*(1234458783113/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_045 :
    ∀ u ∈ Set.Icc (45/512:ℝ) (23/256:ℝ), (416937777305657781247859/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3759993308723/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (45/512:ℝ) (23/256:ℝ) (3759993308723/1000000000000:ℝ) (97414688919/2000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0138).1
  intro u hu
  exact (show (416937777305657781247859/250000000000000000000000:ℝ) ≤ (1/4-6*(3759993308723/1000000000000:ℝ)+4*(3759993308723/1000000000000:ℝ)^2)*(97414688919/2000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_046 :
    ∀ u ∈ Set.Icc (23/256:ℝ) (47/512:ℝ), (1662059789304034033005443/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1887354753223/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (23/256:ℝ) (47/512:ℝ) (1887354753223/500000000000:ℝ) (960853990651/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0139).1
  intro u hu
  exact (show (1662059789304034033005443/1000000000000000000000000:ℝ) ≤ (1/4-6*(1887354753223/500000000000:ℝ)+4*(1887354753223/500000000000:ℝ)^2)*(960853990651/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_047 :
    ∀ u ∈ Set.Icc (47/512:ℝ) (3/32:ℝ), (828133158490629237942809/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1894741650869/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (47/512:ℝ) (3/32:ℝ) (1894741650869/500000000000:ℝ) (4738439483347/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0144).1
  intro u hu
  exact (show (828133158490629237942809/500000000000000000000000:ℝ) ≤ (1/4-6*(1894741650869/500000000000:ℝ)+4*(1894741650869/500000000000:ℝ)^2)*(4738439483347/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_048 :
    ∀ u ∈ Set.Icc (3/32:ℝ) (49/512:ℝ), (1650371752412638040310371/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3804314920031/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/32:ℝ) (49/512:ℝ) (3804314920031/1000000000000:ℝ) (934648165241/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0145).1
  intro u hu
  exact (show (1650371752412638040310371/1000000000000000000000000:ℝ) ≤ (1/4-6*(3804314920031/1000000000000:ℝ)+4*(3804314920031/1000000000000:ℝ)^2)*(934648165241/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_049 :
    ∀ u ∈ Set.Icc (49/512:ℝ) (25/256:ℝ), (411094292900009968783053/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (954801146909/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (49/512:ℝ) (25/256:ℝ) (954801146909/250000000000:ℝ) (576083966659/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0150).1
  intro u hu
  exact (show (411094292900009968783053/250000000000000000000000:ℝ) ≤ (1/4-6*(954801146909/250000000000:ℝ)+4*(954801146909/250000000000:ℝ)^2)*(576083966659/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_050 :
    ∀ u ∈ Set.Icc (25/256:ℝ) (51/512:ℝ), (819141833083700760937913/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3834152531753/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (25/256:ℝ) (51/512:ℝ) (3834152531753/1000000000000:ℝ) (1136182479459/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0151).1
  intro u hu
  exact (show (819141833083700760937913/500000000000000000000000:ℝ) ≤ (1/4-6*(3834152531753/1000000000000:ℝ)+4*(3834152531753/1000000000000:ℝ)^2)*(1136182479459/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_051 :
    ∀ u ∈ Set.Icc (51/512:ℝ) (13/128:ℝ), (816046171560470573584681/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (962289745117/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (51/512:ℝ) (13/128:ℝ) (962289745117/250000000000:ℝ) (4481413055423/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0156).1
  intro u hu
  exact (show (816046171560470573584681/500000000000000000000000:ℝ) ≤ (1/4-6*(962289745117/250000000000:ℝ)+4*(962289745117/250000000000:ℝ)^2)*(4481413055423/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_052 :
    ∀ u ∈ Set.Icc (13/128:ℝ) (53/512:ℝ), (1625804324653926212111369/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (966056040691/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (13/128:ℝ) (53/512:ℝ) (966056040691/250000000000:ℝ) (4418718784289/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0157).1
  intro u hu
  exact (show (1625804324653926212111369/1000000000000000000000000:ℝ) ≤ (1/4-6*(966056040691/250000000000:ℝ)+4*(966056040691/250000000000:ℝ)^2)*(4418718784289/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_053 :
    ∀ u ∈ Set.Icc (53/512:ℝ) (27/256:ℝ), (323884149573414225604271/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (775869661703/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (53/512:ℝ) (27/256:ℝ) (775869661703/200000000000:ℝ) (4356644705751/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0162).1
  intro u hu
  exact (show (323884149573414225604271/200000000000000000000000:ℝ) ≤ (1/4-6*(775869661703/200000000000:ℝ)+4*(775869661703/200000000000:ℝ)^2)*(4356644705751/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_054 :
    ∀ u ∈ Set.Icc (27/256:ℝ) (55/512:ℝ), (806471382291507547903069/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7789063297/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (27/256:ℝ) (55/512:ℝ) (7789063297/2000000000:ℝ) (2147594192367/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0163).1
  intro u hu
  exact (show (806471382291507547903069/500000000000000000000000:ℝ) ≤ (1/4-6*(7789063297/2000000000:ℝ)+4*(7789063297/2000000000:ℝ)^2)*(2147594192367/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_055 :
    ∀ u ∈ Set.Icc (55/512:ℝ) (7/64:ℝ), (1606371541043329696582451/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3909774414397/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (55/512:ℝ) (7/64:ℝ) (3909774414397/1000000000000:ℝ) (2117173675039/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0168).1
  intro u hu
  exact (show (1606371541043329696582451/1000000000000000000000000:ℝ) ≤ (1/4-6*(3909774414397/1000000000000:ℝ)+4*(3909774414397/1000000000000:ℝ)^2)*(2117173675039/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_056 :
    ∀ u ∈ Set.Icc (7/64:ℝ) (57/512:ℝ), (1599708257720913572858011/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (490634604849/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/64:ℝ) (57/512:ℝ) (490634604849/125000000000:ℝ) (4174119095129/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0169).1
  intro u hu
  exact (show (1599708257720913572858011/1000000000000000000000000:ℝ) ≤ (1/4-6*(490634604849/125000000000:ℝ)+4*(490634604849/125000000000:ℝ)^2)*(4174119095129/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_057 :
    ∀ u ∈ Set.Icc (57/512:ℝ) (29/256:ℝ), (24889907953508527837773/15625000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (246277447199/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(29/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (57/512:ℝ) (29/256:ℝ) (246277447199/62500000000:ℝ) (514312634759/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0174).1
  intro u hu
  exact (show (24889907953508527837773/15625000000000000000000:ℝ) ≤ (1/4-6*(246277447199/62500000000:ℝ)+4*(246277447199/62500000000:ℝ)^2)*(514312634759/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_058 :
    ∀ u ∈ Set.Icc (29/256:ℝ) (59/512:ℝ), (793055151525239044885573/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1977930798991/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (29/256:ℝ) (59/512:ℝ) (1977930798991/500000000000:ℝ) (405549072243/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0175).1
  intro u hu
  exact (show (793055151525239044885573/500000000000000000000000:ℝ) ≤ (1/4-6*(1977930798991/500000000000:ℝ)+4*(1977930798991/500000000000:ℝ)^2)*(405549072243/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_059 :
    ∀ u ∈ Set.Icc (59/512:ℝ) (15/128:ℝ), (394794515332816383702243/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1985672201257/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (59/512:ℝ) (15/128:ℝ) (1985672201257/500000000000:ℝ) (1998542708769/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0180).1
  intro u hu
  exact (show (394794515332816383702243/250000000000000000000000:ℝ) ≤ (1/4-6*(1985672201257/500000000000:ℝ)+4*(1985672201257/500000000000:ℝ)^2)*(1998542708769/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_060 :
    ∀ u ∈ Set.Icc (15/128:ℝ) (61/512:ℝ), (1572158618563914001664089/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (398688780503/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (15/128:ℝ) (61/512:ℝ) (398688780503/100000000000:ℝ) (3939282518997/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0181).1
  intro u hu
  exact (show (1572158618563914001664089/1000000000000000000000000:ℝ) ≤ (1/4-6*(398688780503/100000000000:ℝ)+4*(398688780503/100000000000:ℝ)^2)*(3939282518997/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_061 :
    ∀ u ∈ Set.Icc (61/512:ℝ) (31/256:ℝ), (782526611166251537386807/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4002492042703/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (61/512:ℝ) (31/256:ℝ) (4002492042703/1000000000000:ℝ) (242629959321/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0186).1
  intro u hu
  exact (show (782526611166251537386807/500000000000000000000000:ℝ) ≤ (1/4-6*(4002492042703/1000000000000:ℝ)+4*(4002492042703/1000000000000:ℝ)^2)*(242629959321/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_062 :
    ∀ u ∈ Set.Icc (31/256:ℝ) (63/512:ℝ), (778931566418436122015273/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1004539338409/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (31/256:ℝ) (63/512:ℝ) (1004539338409/250000000000:ℝ) (382547319749/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0187).1
  intro u hu
  exact (show (778931566418436122015273/500000000000000000000000:ℝ) ≤ (1/4-6*(1004539338409/250000000000:ℝ)+4*(1004539338409/250000000000:ℝ)^2)*(382547319749/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_063 :
    ∀ u ∈ Set.Icc (63/512:ℝ) (1/8:ℝ), (1550589622624381755686269/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2016941988431/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (63/512:ℝ) (1/8:ℝ) (2016941988431/500000000000:ℝ) (1884730660659/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0192).1
  intro u hu
  exact (show (1550589622624381755686269/1000000000000000000000000:ℝ) ≤ (1/4-6*(2016941988431/500000000000:ℝ)+4*(2016941988431/500000000000:ℝ)^2)*(1884730660659/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

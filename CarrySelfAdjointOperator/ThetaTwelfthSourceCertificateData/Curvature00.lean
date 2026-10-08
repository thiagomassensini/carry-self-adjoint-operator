import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_000 :
    ∀ u ∈ Set.Icc (0/1:ℝ) (1/512:ℝ), (1804357748072860818647303/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1576943921717/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (0/1:ℝ) (1/512:ℝ) (1576943921717/500000000000:ℝ) (8545502162793/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0001).1
  intro u hu
  exact (show (1804357748072860818647303/1000000000000000000000000:ℝ) ≤ (1/4-6*(1576943921717/500000000000:ℝ)+4*(1576943921717/500000000000:ℝ)^2)*(8545502162793/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_001 :
    ∀ u ∈ Set.Icc (1/512:ℝ) (1/256:ℝ), (451017805179600933402433/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1583115905719/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/512:ℝ) (1/256:ℝ) (1583115905719/500000000000:ℝ) (8448911971117/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0006).1
  intro u hu
  exact (show (451017805179600933402433/250000000000000000000000:ℝ) ≤ (1/4-6*(1583115905719/500000000000:ℝ)+4*(1583115905719/500000000000:ℝ)^2)*(8448911971117/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_002 :
    ∀ u ∈ Set.Icc (1/256:ℝ) (3/512:ℝ), (450913435891568441726497/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (198664005773/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(3/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/256:ℝ) (3/512:ℝ) (198664005773/62500000000:ℝ) (1044126246807/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0007).1
  intro u hu
  exact (show (450913435891568441726497/250000000000000000000000:ℝ) ≤ (1/4-6*(198664005773/62500000000:ℝ)+4*(198664005773/62500000000:ℝ)^2)*(1044126246807/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_003 :
    ∀ u ∈ Set.Icc (3/512:ℝ) (1/128:ℝ), (901552761929889255164149/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1595532437657/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/512:ℝ) (1/128:ℝ) (1595532437657/500000000000:ℝ) (4128898006789/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0012).1
  intro u hu
  exact (show (901552761929889255164149/500000000000000000000000:ℝ) ≤ (1/4-6*(1595532437657/500000000000:ℝ)+4*(1595532437657/500000000000:ℝ)^2)*(4128898006789/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_004 :
    ∀ u ∈ Set.Icc (1/128:ℝ) (5/512:ℝ), (72097071559822197032487/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3203554350107/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/128:ℝ) (5/512:ℝ) (3203554350107/1000000000000:ℝ) (408163493967/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0013).1
  intro u hu
  exact (show (72097071559822197032487/40000000000000000000000:ℝ) ≤ (1/4-6*(3203554350107/1000000000000:ℝ)+4*(3203554350107/1000000000000:ℝ)^2)*(408163493967/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_005 :
    ∀ u ∈ Set.Icc (5/512:ℝ) (3/256:ℝ), (450404446639052573669741/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3216092707323/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/512:ℝ) (3/256:ℝ) (3216092707323/1000000000000:ℝ) (322777252513/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0018).1
  intro u hu
  exact (show (450404446639052573669741/250000000000000000000000:ℝ) ≤ (1/4-6*(3216092707323/1000000000000:ℝ)+4*(3216092707323/1000000000000:ℝ)^2)*(322777252513/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_006 :
    ∀ u ∈ Set.Icc (3/256:ℝ) (7/512:ℝ), (56271212010106046098461/31250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3228680138281/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/256:ℝ) (7/512:ℝ) (3228680138281/1000000000000:ℝ) (7976280005461/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0019).1
  intro u hu
  exact (show (56271212010106046098461/31250000000000000000000:ℝ) ≤ (1/4-6*(3228680138281/1000000000000:ℝ)+4*(3228680138281/1000000000000:ℝ)^2)*(7976280005461/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_007 :
    ∀ u ∈ Set.Icc (7/512:ℝ) (1/64:ℝ), (1799610070272661358598833/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3241316835051/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/512:ℝ) (1/64:ℝ) (3241316835051/1000000000000:ℝ) (3941907799509/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0024).1
  intro u hu
  exact (show (1799610070272661358598833/1000000000000000000000000:ℝ) ≤ (1/4-6*(3241316835051/1000000000000:ℝ)+4*(3241316835051/1000000000000:ℝ)^2)*(3941907799509/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_008 :
    ∀ u ∈ Set.Icc (1/64:ℝ) (9/512:ℝ), (1798411952607616720394489/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1627001495227/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/64:ℝ) (9/512:ℝ) (1627001495227/500000000000:ℝ) (7792037685867/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0025).1
  intro u hu
  exact (show (1798411952607616720394489/1000000000000000000000000:ℝ) ≤ (1/4-6*(1627001495227/500000000000:ℝ)+4*(1627001495227/500000000000:ℝ)^2)*(7792037685867/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_009 :
    ∀ u ∈ Set.Icc (9/512:ℝ) (5/256:ℝ), (4492711899304632377717/2500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1633369399033/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (9/512:ℝ) (5/256:ℝ) (1633369399033/500000000000:ℝ) (3850472904461/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0030).1
  intro u hu
  exact (show (4492711899304632377717/2500000000000000000000:ℝ) ≤ (1/4-6*(1633369399033/500000000000:ℝ)+4*(1633369399033/500000000000:ℝ)^2)*(3850472904461/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_010 :
    ∀ u ∈ Set.Icc (5/256:ℝ) (11/512:ℝ), (897814420115531328112517/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3279524452219/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/256:ℝ) (11/512:ℝ) (3279524452219/1000000000000:ℝ) (380526973097/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0031).1
  intro u hu
  exact (show (897814420115531328112517/500000000000000000000000:ℝ) ≤ (1/4-6*(3279524452219/1000000000000:ℝ)+4*(3279524452219/1000000000000:ℝ)^2)*(380526973097/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_011 :
    ∀ u ∈ Set.Icc (11/512:ℝ) (3/128:ℝ), (448511140735877500700207/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3292360148007/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (11/512:ℝ) (3/128:ℝ) (3292360148007/1000000000000:ℝ) (1880204522387/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0036).1
  intro u hu
  exact (show (448511140735877500700207/250000000000000000000000:ℝ) ≤ (1/4-6*(3292360148007/1000000000000:ℝ)+4*(3292360148007/1000000000000:ℝ)^2)*(1880204522387/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_012 :
    ∀ u ∈ Set.Icc (3/128:ℝ) (13/512:ℝ), (358466463367597438820199/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (413155760161/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/128:ℝ) (13/512:ℝ) (413155760161/125000000000:ℝ) (7431781087363/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0037).1
  intro u hu
  exact (show (358466463367597438820199/200000000000000000000000:ℝ) ≤ (1/4-6*(413155760161/125000000000:ℝ)+4*(413155760161/125000000000:ℝ)^2)*(7431781087363/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_013 :
    ∀ u ∈ Set.Icc (13/512:ℝ) (7/256:ℝ), (895246255538171997651203/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1659091224343/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (13/512:ℝ) (7/256:ℝ) (1659091224343/500000000000:ℝ) (1835856950571/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0042).1
  intro u hu
  exact (show (895246255538171997651203/500000000000000000000000:ℝ) ≤ (1/4-6*(1659091224343/500000000000:ℝ)+4*(1659091224343/500000000000:ℝ)^2)*(1835856950571/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_014 :
    ∀ u ∈ Set.Icc (7/256:ℝ) (15/512:ℝ), (447131393731680061742449/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (666233889519/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/256:ℝ) (15/512:ℝ) (666233889519/200000000000:ℝ) (7255757532429/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0043).1
  intro u hu
  exact (show (447131393731680061742449/250000000000000000000000:ℝ) ≤ (1/4-6*(666233889519/200000000000:ℝ)+4*(666233889519/200000000000:ℝ)^2)*(7255757532429/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_015 :
    ∀ u ∈ Set.Icc (15/512:ℝ) (1/32:ℝ), (893215978893590504222731/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (167210363809/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (15/512:ℝ) (1/32:ℝ) (167210363809/50000000000:ℝ) (448048095471/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0048).1
  intro u hu
  exact (show (893215978893590504222731/500000000000000000000000:ℝ) ≤ (1/4-6*(167210363809/50000000000:ℝ)+4*(167210363809/50000000000:ℝ)^2)*(448048095471/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_016 :
    ∀ u ∈ Set.Icc (1/32:ℝ) (17/512:ℝ), (1784212129104098141286139/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (419662016673/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/32:ℝ) (17/512:ℝ) (419662016673/125000000000:ℝ) (1770615747231/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0049).1
  intro u hu
  exact (show (1784212129104098141286139/1000000000000000000000000:ℝ) ≤ (1/4-6*(419662016673/125000000000:ℝ)+4*(419662016673/125000000000:ℝ)^2)*(1770615747231/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_017 :
    ∀ u ∈ Set.Icc (17/512:ℝ) (9/256:ℝ), (222733322296030593255943/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1685218109463/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (17/512:ℝ) (9/256:ℝ) (1685218109463/500000000000:ℝ) (3498418534927/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0054).1
  intro u hu
  exact (show (222733322296030593255943/125000000000000000000000:ℝ) ≤ (1/4-6*(1685218109463/500000000000:ℝ)+4*(1685218109463/500000000000:ℝ)^2)*(3498418534927/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_018 :
    ∀ u ∈ Set.Icc (9/256:ℝ) (19/512:ℝ), (1779395815030052136323121/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3383627733309/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (9/256:ℝ) (19/512:ℝ) (3383627733309/1000000000000:ℝ) (1382378175107/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0055).1
  intro u hu
  exact (show (1779395815030052136323121/1000000000000000000000000:ℝ) ≤ (1/4-6*(3383627733309/1000000000000:ℝ)+4*(3383627733309/1000000000000:ℝ)^2)*(1382378175107/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_019 :
    ∀ u ∈ Set.Icc (19/512:ℝ) (5/128:ℝ), (1776800368486171250048647/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3396870877819/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (19/512:ℝ) (5/128:ℝ) (3396870877819/1000000000000:ℝ) (1365524692699/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0060).1
  intro u hu
  exact (show (1776800368486171250048647/1000000000000000000000000:ℝ) ≤ (1/4-6*(3396870877819/1000000000000:ℝ)+4*(3396870877819/1000000000000:ℝ)^2)*(1365524692699/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_020 :
    ∀ u ∈ Set.Icc (5/128:ℝ) (21/512:ℝ), (1774080787998504949871369/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3410165854531/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/128:ℝ) (21/512:ℝ) (3410165854531/1000000000000:ℝ) (6744033843673/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0061).1
  intro u hu
  exact (show (1774080787998504949871369/1000000000000000000000000:ℝ) ≤ (1/4-6*(3410165854531/1000000000000:ℝ)+4*(3410165854531/1000000000000:ℝ)^2)*(6744033843673/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_021 :
    ∀ u ∈ Set.Icc (21/512:ℝ) (11/256:ℝ), (221404705327917593722827/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3423512866311/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (21/512:ℝ) (11/256:ℝ) (3423512866311/1000000000000:ℝ) (3330560489303/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0066).1
  intro u hu
  exact (show (221404705327917593722827/125000000000000000000000:ℝ) ≤ (1/4-6*(3423512866311/1000000000000:ℝ)+4*(3423512866311/1000000000000:ℝ)^2)*(3330560489303/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_022 :
    ∀ u ∈ Set.Icc (11/256:ℝ) (23/512:ℝ), (176827152117764724806041/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3436912116819/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (11/256:ℝ) (23/512:ℝ) (3436912116819/1000000000000:ℝ) (3289441891889/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0067).1
  intro u hu
  exact (show (176827152117764724806041/100000000000000000000000:ℝ) ≤ (1/4-6*(3436912116819/1000000000000:ℝ)+4*(3436912116819/1000000000000:ℝ)^2)*(3289441891889/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_023 :
    ∀ u ∈ Set.Icc (23/512:ℝ) (3/64:ℝ), (220647879015663931023683/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3450363810509/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (23/512:ℝ) (3/64:ℝ) (3450363810509/1000000000000:ℝ) (6497321127709/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0072).1
  intro u hu
  exact (show (220647879015663931023683/125000000000000000000000:ℝ) ≤ (1/4-6*(3450363810509/1000000000000:ℝ)+4*(3450363810509/1000000000000:ℝ)^2)*(6497321127709/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_024 :
    ∀ u ∈ Set.Icc (3/64:ℝ) (25/512:ℝ), (880986401761846692876809/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3463868152641/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (3/64:ℝ) (25/512:ℝ) (3463868152641/1000000000000:ℝ) (3208215916119/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0073).1
  intro u hu
  exact (show (880986401761846692876809/500000000000000000000000:ℝ) ≤ (1/4-6*(3463868152641/1000000000000:ℝ)+4*(3463868152641/1000000000000:ℝ)^2)*(3208215916119/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_025 :
    ∀ u ∈ Set.Icc (25/512:ℝ) (13/256:ℝ), (1758641482928085514001897/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3477425349273/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (25/512:ℝ) (13/256:ℝ) (3477425349273/1000000000000:ℝ) (316810733639/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0078).1
  intro u hu
  exact (show (1758641482928085514001897/1000000000000000000000000:ℝ) ≤ (1/4-6*(3477425349273/1000000000000:ℝ)+4*(3477425349273/1000000000000:ℝ)^2)*(316810733639/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_026 :
    ∀ u ∈ Set.Icc (13/256:ℝ) (27/512:ℝ), (877594868655878291542799/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (436379450909/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (13/256:ℝ) (27/512:ℝ) (436379450909/125000000000:ℝ) (6256668378569/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0079).1
  intro u hu
  exact (show (877594868655878291542799/500000000000000000000000:ℝ) ≤ (1/4-6*(436379450909/125000000000:ℝ)+4*(436379450909/125000000000:ℝ)^2)*(6256668378569/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_027 :
    ∀ u ∈ Set.Icc (27/512:ℝ) (7/128:ℝ), (175161825295770581263389/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (700939826863/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (27/512:ℝ) (7/128:ℝ) (700939826863/200000000000:ℝ) (3088895816439/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0084).1
  intro u hu
  exact (show (175161825295770581263389/100000000000000000000000:ℝ) ≤ (1/4-6*(700939826863/200000000000:ℝ)+4*(700939826863/200000000000:ℝ)^2)*(3088895816439/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_028 :
    ∀ u ∈ Set.Icc (7/128:ℝ) (29/512:ℝ), (349585547073147977842183/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3518416138891/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/128:ℝ) (29/512:ℝ) (3518416138891/1000000000000:ℝ) (1524895768329/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0085).1
  intro u hu
  exact (show (349585547073147977842183/200000000000000000000000:ℝ) ≤ (1/4-6*(3518416138891/1000000000000:ℝ)+4*(3518416138891/1000000000000:ℝ)^2)*(1524895768329/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_029 :
    ∀ u ∈ Set.Icc (29/512:ℝ) (15/256:ℝ), (1744118909148945553634357/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (706437366061/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (29/512:ℝ) (15/256:ℝ) (706437366061/200000000000:ℝ) (6022041292103/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0090).1
  intro u hu
  exact (show (1744118909148945553634357/1000000000000000000000000:ℝ) ≤ (1/4-6*(706437366061/200000000000:ℝ)+4*(706437366061/200000000000:ℝ)^2)*(6022041292103/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_030 :
    ∀ u ∈ Set.Icc (15/256:ℝ) (31/512:ℝ), (348038503580446356404579/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3546011418681/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (15/256:ℝ) (31/512:ℝ) (3546011418681/1000000000000:ℝ) (148629120907/2500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0091).1
  intro u hu
  exact (show (348038503580446356404579/200000000000000000000000:ℝ) ≤ (1/4-6*(3546011418681/1000000000000:ℝ)+4*(3546011418681/1000000000000:ℝ)^2)*(148629120907/2500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_031 :
    ∀ u ∈ Set.Icc (31/512:ℝ) (1/16:ℝ), (1736149324112270662297763/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3559890114967/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (31/512:ℝ) (1/16:ℝ) (3559890114967/1000000000000:ℝ) (73361902601/1250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0096).1
  intro u hu
  exact (show (1736149324112270662297763/1000000000000000000000000:ℝ) ≤ (1/4-6*(3559890114967/1000000000000:ℝ)+4*(3559890114967/1000000000000:ℝ)^2)*(73361902601/1250000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

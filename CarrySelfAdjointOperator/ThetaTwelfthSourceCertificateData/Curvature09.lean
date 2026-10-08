import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_288 :
    ∀ u ∈ Set.Icc (9/16:ℝ) (289/512:ℝ), (25583653603413205650409/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9714658474943/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(289/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(289/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (9/16:ℝ) (289/512:ℝ) (9714658474943/1000000000000:ℝ) (8008395751/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0865).1
  intro u hu
  exact (show (25583653603413205650409/500000000000000000000000:ℝ) ≤ (1/4-6*(9714658474943/1000000000000:ℝ)+4*(9714658474943/1000000000000:ℝ)^2)*(8008395751/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_289 :
    ∀ u ∈ Set.Icc (289/512:ℝ) (145/256:ℝ), (24864114131483293224261/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4876340286587/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(145/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(145/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (289/512:ℝ) (145/256:ℝ) (4876340286587/500000000000:ℝ) (192928709/1250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0870).1
  intro u hu
  exact (show (24864114131483293224261/500000000000000000000000:ℝ) ≤ (1/4-6*(4876340286587/500000000000:ℝ)+4*(4876340286587/500000000000:ℝ)^2)*(192928709/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_290 :
    ∀ u ∈ Set.Icc (145/256:ℝ) (291/512:ℝ), (12080569058620188148461/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (979085148569/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(291/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(291/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (145/256:ℝ) (291/512:ℝ) (979085148569/100000000000:ℝ) (14870772819/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0871).1
  intro u hu
  exact (show (12080569058620188148461/250000000000000000000000:ℝ) ≤ (1/4-6*(979085148569/100000000000:ℝ)+4*(979085148569/100000000000:ℝ)^2)*(14870772819/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_291 :
    ∀ u ∈ Set.Icc (291/512:ℝ) (73/128:ℝ), (46948909398942769942027/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9829171794933/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(73/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (291/512:ℝ) (73/128:ℝ) (9829171794933/1000000000000:ℝ) (14325683451/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0876).1
  intro u hu
  exact (show (46948909398942769942027/1000000000000000000000000:ℝ) ≤ (1/4-6*(9829171794933/1000000000000:ℝ)+4*(9829171794933/1000000000000:ℝ)^2)*(14325683451/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_292 :
    ∀ u ∈ Set.Icc (73/128:ℝ) (293/512:ℝ), (45607588912752387150693/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4933821042813/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(293/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(293/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (73/128:ℝ) (293/512:ℝ) (4933821042813/500000000000:ℝ) (6899252351/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0877).1
  intro u hu
  exact (show (45607588912752387150693/1000000000000000000000000:ℝ) ≤ (1/4-6*(4933821042813/500000000000:ℝ)+4*(4933821042813/500000000000:ℝ)^2)*(6899252351/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_293 :
    ∀ u ∈ Set.Icc (293/512:ℝ) (147/256:ℝ), (22148889472059177758597/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (495313147239/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(147/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(147/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (293/512:ℝ) (147/256:ℝ) (495313147239/50000000000:ℝ) (6644362441/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0882).1
  intro u hu
  exact (show (22148889472059177758597/500000000000000000000000:ℝ) ≤ (1/4-6*(495313147239/50000000000:ℝ)+4*(495313147239/50000000000:ℝ)^2)*(6644362441/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_294 :
    ∀ u ∈ Set.Icc (147/256:ℝ) (295/512:ℝ), (43018946814087568901247/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4972517480851/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(295/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(295/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (147/256:ℝ) (295/512:ℝ) (4972517480851/500000000000:ℝ) (79974027/625000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0883).1
  intro u hu
  exact (show (43018946814087568901247/1000000000000000000000000:ℝ) ≤ (1/4-6*(4972517480851/500000000000:ℝ)+4*(4972517480851/500000000000:ℝ)^2)*(79974027/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_295 :
    ∀ u ∈ Set.Icc (295/512:ℝ) (37/64:ℝ), (41770563139424439673057/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1247994841001/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (295/512:ℝ) (37/64:ℝ) (1247994841001/125000000000:ℝ) (6159687581/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0888).1
  intro u hu
  exact (show (41770563139424439673057/1000000000000000000000000:ℝ) ≤ (1/4-6*(1247994841001/125000000000:ℝ)+4*(1247994841001/125000000000:ℝ)^2)*(6159687581/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_296 :
    ∀ u ∈ Set.Icc (37/64:ℝ) (297/512:ℝ), (4055210198080225498853/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2505758709407/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(297/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(297/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (37/64:ℝ) (297/512:ℝ) (2505758709407/250000000000:ℝ) (11858841173/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0889).1
  intro u hu
  exact (show (4055210198080225498853/100000000000000000000000:ℝ) ≤ (1/4-6*(2505758709407/250000000000:ℝ)+4*(2505758709407/250000000000:ℝ)^2)*(11858841173/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_297 :
    ∀ u ∈ Set.Icc (297/512:ℝ) (149/256:ℝ), (7872608189018256901441/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10062263886817/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(149/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(149/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (297/512:ℝ) (149/256:ℝ) (10062263886817/1000000000000:ℝ) (1426722191/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0894).1
  intro u hu
  exact (show (7872608189018256901441/200000000000000000000000:ℝ) ≤ (1/4-6*(10062263886817/1000000000000:ℝ)+4*(10062263886817/1000000000000:ℝ)^2)*(1426722191/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_298 :
    ∀ u ∈ Set.Icc (149/256:ℝ) (299/512:ℝ), (19101430668175905514963/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10101646474163/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(299/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(299/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (149/256:ℝ) (299/512:ℝ) (10101646474163/1000000000000:ℝ) (549186531/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0895).1
  intro u hu
  exact (show (19101430668175905514963/500000000000000000000000:ℝ) ≤ (1/4-6*(10101646474163/1000000000000:ℝ)+4*(10101646474163/1000000000000:ℝ)^2)*(549186531/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_299 :
    ∀ u ∈ Set.Icc (299/512:ℝ) (75/128:ℝ), (7414209652781484338813/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5070591600299/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (299/512:ℝ) (75/128:ℝ) (5070591600299/500000000000:ℝ) (5284128929/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0900).1
  intro u hu
  exact (show (7414209652781484338813/200000000000000000000000:ℝ) ≤ (1/4-6*(5070591600299/500000000000:ℝ)+4*(5070591600299/500000000000:ℝ)^2)*(5284128929/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_300 :
    ∀ u ∈ Set.Icc (75/128:ℝ) (301/512:ℝ), (35967090775677729233607/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2036174933881/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(301/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(301/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (75/128:ℝ) (301/512:ℝ) (2036174933881/200000000000:ℝ) (406677099/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0901).1
  intro u hu
  exact (show (35967090775677729233607/1000000000000000000000000:ℝ) ≤ (1/4-6*(2036174933881/200000000000:ℝ)+4*(2036174933881/200000000000:ℝ)^2)*(406677099/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_301 :
    ∀ u ∈ Set.Icc (301/512:ℝ) (151/256:ℝ), (8722620487668306256711/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10220721486229/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(151/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(151/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (301/512:ℝ) (151/256:ℝ) (10220721486229/1000000000000:ℝ) (9779318327/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0906).1
  intro u hu
  exact (show (8722620487668306256711/250000000000000000000000:ℝ) ≤ (1/4-6*(10220721486229/1000000000000:ℝ)+4*(10220721486229/1000000000000:ℝ)^2)*(9779318327/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_302 :
    ∀ u ∈ Set.Icc (151/256:ℝ) (303/512:ℝ), (8460179755947246822237/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2565181064771/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(303/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(303/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (151/256:ℝ) (303/512:ℝ) (2565181064771/250000000000:ℝ) (1175627463/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0907).1
  intro u hu
  exact (show (8460179755947246822237/250000000000000000000000:ℝ) ≤ (1/4-6*(2565181064771/250000000000:ℝ)+4*(2565181064771/250000000000:ℝ)^2)*(1175627463/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_303 :
    ∀ u ∈ Set.Icc (303/512:ℝ) (19/32:ℝ), (16408651743486612312083/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2060176719673/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (303/512:ℝ) (19/32:ℝ) (2060176719673/200000000000:ℝ) (9043631137/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0912).1
  intro u hu
  exact (show (16408651743486612312083/500000000000000000000000:ℝ) ≤ (1/4-6*(2060176719673/200000000000:ℝ)+4*(2060176719673/200000000000:ℝ)^2)*(9043631137/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_304 :
    ∀ u ∈ Set.Icc (19/32:ℝ) (305/512:ℝ), (15909870597333041190103/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10341200116857/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(305/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(305/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (19/32:ℝ) (305/512:ℝ) (10341200116857/1000000000000:ℝ) (8694762209/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0913).1
  intro u hu
  exact (show (15909870597333041190103/500000000000000000000000:ℝ) ≤ (1/4-6*(10341200116857/1000000000000:ℝ)+4*(10341200116857/1000000000000:ℝ)^2)*(8694762209/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_305 :
    ∀ u ∈ Set.Icc (305/512:ℝ) (153/256:ℝ), (30847542448055080598143/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (519083721487/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(153/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(153/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (305/512:ℝ) (153/256:ℝ) (519083721487/50000000000:ℝ) (8358032363/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0918).1
  intro u hu
  exact (show (30847542448055080598143/1000000000000000000000000:ℝ) ≤ (1/4-6*(519083721487/50000000000:ℝ)+4*(519083721487/50000000000:ℝ)^2)*(8358032363/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_306 :
    ∀ u ∈ Set.Icc (153/256:ℝ) (307/512:ℝ), (14950111052747826858571/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2084461430921/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(307/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(307/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (153/256:ℝ) (307/512:ℝ) (2084461430921/200000000000:ℝ) (12551673/156250000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0919).1
  intro u hu
  exact (show (14950111052747826858571/500000000000000000000000:ℝ) ≤ (1/4-6*(2084461430921/200000000000:ℝ)+4*(2084461430921/200000000000:ℝ)^2)*(12551673/156250000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_307 :
    ∀ u ∈ Set.Icc (307/512:ℝ) (77/128:ℝ), (452770307138013511551/15625000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5231549455729/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(77/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (307/512:ℝ) (77/128:ℝ) (5231549455729/500000000000:ℝ) (771951589/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0924).1
  intro u hu
  exact (show (452770307138013511551/15625000000000000000000:ℝ) ≤ (1/4-6*(5231549455729/500000000000:ℝ)+4*(5231549455729/500000000000:ℝ)^2)*(771951589/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_308 :
    ∀ u ∈ Set.Icc (77/128:ℝ) (309/512:ℝ), (28078299312739342725291/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5252025161367/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(309/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(309/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (77/128:ℝ) (309/512:ℝ) (5252025161367/500000000000:ℝ) (741701579/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0925).1
  intro u hu
  exact (show (28078299312739342725291/1000000000000000000000000:ℝ) ≤ (1/4-6*(5252025161367/500000000000:ℝ)+4*(5252025161367/500000000000:ℝ)^2)*(741701579/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_309 :
    ∀ u ∈ Set.Icc (309/512:ℝ) (155/256:ℝ), (27202750094728656016807/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10545162013301/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(155/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(155/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (309/512:ℝ) (155/256:ℝ) (10545162013301/1000000000000:ℝ) (1425045493/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0930).1
  intro u hu
  exact (show (27202750094728656016807/1000000000000000000000000:ℝ) ≤ (1/4-6*(10545162013301/1000000000000:ℝ)+4*(10545162013301/1000000000000:ℝ)^2)*(1425045493/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_310 :
    ∀ u ∈ Set.Icc (155/256:ℝ) (311/512:ℝ), (13175092945756406544489/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2646608652619/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(311/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(311/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (155/256:ℝ) (311/512:ℝ) (2646608652619/250000000000:ℝ) (6843816903/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0931).1
  intro u hu
  exact (show (13175092945756406544489/500000000000000000000000:ℝ) ≤ (1/4-6*(2646608652619/250000000000:ℝ)+4*(2646608652619/250000000000:ℝ)^2)*(6843816903/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_311 :
    ∀ u ∈ Set.Icc (311/512:ℝ) (39/64:ℝ), (5104029109918624195953/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10627868744029/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (311/512:ℝ) (39/64:ℝ) (10627868744029/1000000000000:ℝ) (3286229431/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0936).1
  intro u hu
  exact (show (5104029109918624195953/200000000000000000000000:ℝ) ≤ (1/4-6*(10627868744029/1000000000000:ℝ)+4*(10627868744029/1000000000000:ℝ)^2)*(3286229431/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_312 :
    ∀ u ∈ Set.Icc (39/64:ℝ) (313/512:ℝ), (24712172933868604341027/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2667366261549/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(313/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(313/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (39/64:ℝ) (313/512:ℝ) (2667366261549/250000000000:ℝ) (1577709173/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0937).1
  intro u hu
  exact (show (24712172933868604341027/1000000000000000000000000:ℝ) ≤ (1/4-6*(2667366261549/250000000000:ℝ)+4*(2667366261549/250000000000:ℝ)^2)*(1577709173/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_313 :
    ∀ u ∈ Set.Icc (313/512:ℝ) (157/256:ℝ), (23925816996024384782671/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5355612075843/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(157/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(157/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (313/512:ℝ) (157/256:ℝ) (5355612075843/500000000000:ℝ) (3029321081/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0942).1
  intro u hu
  exact (show (23925816996024384782671/1000000000000000000000000:ℝ) ≤ (1/4-6*(5355612075843/500000000000:ℝ)+4*(5355612075843/500000000000:ℝ)^2)*(3029321081/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_314 :
    ∀ u ∈ Set.Icc (157/256:ℝ) (315/512:ℝ), (2895078978439768447953/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5376573348847/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(315/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(315/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (157/256:ℝ) (315/512:ℝ) (5376573348847/500000000000:ℝ) (2907787643/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0943).1
  intro u hu
  exact (show (2895078978439768447953/125000000000000000000000:ℝ) ≤ (1/4-6*(5376573348847/500000000000:ℝ)+4*(5376573348847/500000000000:ℝ)^2)*(2907787643/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_315 :
    ∀ u ∈ Set.Icc (315/512:ℝ) (79/128:ℝ), (22416176724474318852911/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2698808330977/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(79/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (315/512:ℝ) (79/128:ℝ) (2698808330977/250000000000:ℝ) (1116268831/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0948).1
  intro u hu
  exact (show (22416176724474318852911/1000000000000000000000000:ℝ) ≤ (1/4-6*(2698808330977/250000000000:ℝ)+4*(2698808330977/250000000000:ℝ)^2)*(1116268831/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_316 :
    ∀ u ∈ Set.Icc (79/128:ℝ) (317/512:ℝ), (10846008116516652901023/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10837484672519/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(317/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(317/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (79/128:ℝ) (317/512:ℝ) (10837484672519/1000000000000:ℝ) (5355664767/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0949).1
  intro u hu
  exact (show (10846008116516652901023/500000000000000000000000:ℝ) ≤ (1/4-6*(10837484672519/1000000000000:ℝ)+4*(10837484672519/1000000000000:ℝ)^2)*(5355664767/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_317 :
    ∀ u ∈ Set.Icc (317/512:ℝ) (159/256:ℝ), (1311732513438111663089/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10879901388233/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(159/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(159/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (317/512:ℝ) (159/256:ℝ) (10879901388233/1000000000000:ℝ) (1027652173/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0954).1
  intro u hu
  exact (show (1311732513438111663089/62500000000000000000000:ℝ) ≤ (1/4-6*(10879901388233/1000000000000:ℝ)+4*(10879901388233/1000000000000:ℝ)^2)*(1027652173/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_318 :
    ∀ u ∈ Set.Icc (159/256:ℝ) (319/512:ℝ), (20302863861096708719893/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10922484118279/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(319/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(319/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (159/256:ℝ) (319/512:ℝ) (10922484118279/1000000000000:ℝ) (985772753/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0955).1
  intro u hu
  exact (show (20302863861096708719893/1000000000000000000000000:ℝ) ≤ (1/4-6*(10922484118279/1000000000000:ℝ)+4*(10922484118279/1000000000000:ℝ)^2)*(985772753/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_319 :
    ∀ u ∈ Set.Icc (319/512:ℝ) (5/8:ℝ), (981851388666244180191/50000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5482616756209/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (319/512:ℝ) (5/8:ℝ) (5482616756209/500000000000:ℝ) (1181803051/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0960).1
  intro u hu
  exact (show (981851388666244180191/50000000000000000000000:ℝ) ≤ (1/4-6*(5482616756209/500000000000:ℝ)+4*(5482616756209/500000000000:ℝ)^2)*(1181803051/25000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

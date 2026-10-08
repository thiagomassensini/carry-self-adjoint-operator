import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_352 :
    ∀ u ∈ Set.Icc (11/16:ℝ) (353/512:ℝ), (5915998361410316176869/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3118467099067/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(353/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(353/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (11/16:ℝ) (353/512:ℝ) (3118467099067/250000000000:ℝ) (134995383/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1057).1
  intro u hu
  exact (show (5915998361410316176869/1000000000000000000000000:ℝ) ≤ (1/4-6*(3118467099067/250000000000:ℝ)+4*(3118467099067/250000000000:ℝ)^2)*(134995383/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_353 :
    ∀ u ∈ Set.Icc (353/512:ℝ) (177/256:ℝ), (2843426264996510417569/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12522689736793/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(177/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(177/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (353/512:ℝ) (177/256:ℝ) (12522689736793/1000000000000:ℝ) (1029509059/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1062).1
  intro u hu
  exact (show (2843426264996510417569/500000000000000000000000:ℝ) ≤ (1/4-6*(12522689736793/1000000000000:ℝ)+4*(12522689736793/1000000000000:ℝ)^2)*(1029509059/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_354 :
    ∀ u ∈ Set.Icc (177/256:ℝ) (355/512:ℝ), (1366381270650438608911/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12571702158641/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(355/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(355/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (177/256:ℝ) (355/512:ℝ) (12571702158641/1000000000000:ℝ) (490612333/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1063).1
  intro u hu
  exact (show (1366381270650438608911/250000000000000000000000:ℝ) ≤ (1/4-6*(12571702158641/1000000000000:ℝ)+4*(12571702158641/1000000000000:ℝ)^2)*(490612333/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_355 :
    ∀ u ∈ Set.Icc (355/512:ℝ) (89/128:ℝ), (1312947952616355036517/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3155226602421/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(89/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (355/512:ℝ) (89/128:ℝ) (3155226602421/250000000000:ℝ) (935025449/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1068).1
  intro u hu
  exact (show (1312947952616355036517/250000000000000000000000:ℝ) ≤ (1/4-6*(3155226602421/250000000000:ℝ)+4*(3155226602421/250000000000:ℝ)^2)*(935025449/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_356 :
    ∀ u ∈ Set.Icc (89/128:ℝ) (357/512:ℝ), (2522716680051828661583/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6335151620361/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(357/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(357/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (89/128:ℝ) (357/512:ℝ) (6335151620361/500000000000:ℝ) (890829867/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1069).1
  intro u hu
  exact (show (2522716680051828661583/500000000000000000000000:ℝ) ≤ (1/4-6*(6335151620361/500000000000:ℝ)+4*(6335151620361/500000000000:ℝ)^2)*(890829867/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_357 :
    ∀ u ∈ Set.Icc (357/512:ℝ) (179/256:ℝ), (4846235194980276675629/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12719893405489/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(179/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(179/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (357/512:ℝ) (179/256:ℝ) (12719893405489/1000000000000:ℝ) (848559193/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1074).1
  intro u hu
  exact (show (4846235194980276675629/1000000000000000000000000:ℝ) ≤ (1/4-6*(12719893405489/1000000000000:ℝ)+4*(12719893405489/1000000000000:ℝ)^2)*(848559193/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_358 :
    ∀ u ∈ Set.Icc (179/256:ℝ) (359/512:ℝ), (930797510392505598467/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6384838830337/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(359/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(359/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (179/256:ℝ) (359/512:ℝ) (6384838830337/500000000000:ℝ) (404068717/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1075).1
  intro u hu
  exact (show (930797510392505598467/200000000000000000000000:ℝ) ≤ (1/4-6*(6384838830337/500000000000:ℝ)+4*(6384838830337/500000000000:ℝ)^2)*(404068717/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_359 :
    ∀ u ∈ Set.Icc (359/512:ℝ) (45/64:ℝ), (4468485357641962583949/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3204914191481/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (359/512:ℝ) (45/64:ℝ) (3204914191481/250000000000:ℝ) (384745623/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1080).1
  intro u hu
  exact (show (4468485357641962583949/1000000000000000000000000:ℝ) ≤ (1/4-6*(3204914191481/250000000000:ℝ)+4*(3204914191481/250000000000:ℝ)^2)*(384745623/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_360 :
    ∀ u ∈ Set.Icc (45/64:ℝ) (361/512:ℝ), (4289528190266634707247/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (12869831483861/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(361/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(361/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (45/64:ℝ) (361/512:ℝ) (12869831483861/1000000000000:ℝ) (732549859/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1081).1
  intro u hu
  exact (show (4289528190266634707247/1000000000000000000000000:ℝ) ≤ (1/4-6*(12869831483861/1000000000000:ℝ)+4*(12869831483861/1000000000000:ℝ)^2)*(732549859/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_361 :
    ∀ u ∈ Set.Icc (361/512:ℝ) (181/256:ℝ), (4116920219374762590193/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3230050645023/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(181/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(181/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (361/512:ℝ) (181/256:ℝ) (3230050645023/250000000000:ℝ) (139449/20000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1086).1
  intro u hu
  exact (show (4116920219374762590193/1000000000000000000000000:ℝ) ≤ (1/4-6*(3230050645023/250000000000:ℝ)+4*(3230050645023/250000000000:ℝ)^2)*(139449/20000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_362 :
    ∀ u ∈ Set.Icc (181/256:ℝ) (363/512:ℝ), (3950470151824047310243/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (648538541161/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(363/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(363/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (181/256:ℝ) (363/512:ℝ) (648538541161/50000000000:ℝ) (663510819/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1087).1
  intro u hu
  exact (show (3950470151824047310243/1000000000000000000000000:ℝ) ≤ (1/4-6*(648538541161/50000000000:ℝ)+4*(648538541161/50000000000:ℝ)^2)*(663510819/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_363 :
    ∀ u ∈ Set.Icc (363/512:ℝ) (91/128:ℝ), (3789991154824592371277/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2604307396971/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(91/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (363/512:ℝ) (91/128:ℝ) (2604307396971/200000000000:ℝ) (631283813/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1092).1
  intro u hu
  exact (show (3789991154824592371277/1000000000000000000000000:ℝ) ≤ (1/4-6*(2604307396971/200000000000:ℝ)+4*(2604307396971/200000000000:ℝ)^2)*(631283813/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_364 :
    ∀ u ∈ Set.Icc (91/128:ℝ) (365/512:ℝ), (908825205366282139397/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13072501839629/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(365/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(365/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (91/128:ℝ) (365/512:ℝ) (13072501839629/1000000000000:ℝ) (600502759/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1093).1
  intro u hu
  exact (show (908825205366282139397/250000000000000000000000:ℝ) ≤ (1/4-6*(13072501839629/1000000000000:ℝ)+4*(13072501839629/1000000000000:ℝ)^2)*(600502759/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_365 :
    ∀ u ∈ Set.Icc (365/512:ℝ) (183/256:ℝ), (435777636239628610867/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2624733233041/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(183/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(183/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (365/512:ℝ) (183/256:ℝ) (2624733233041/200000000000:ℝ) (571108641/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1098).1
  intro u hu
  exact (show (435777636239628610867/125000000000000000000000:ℝ) ≤ (1/4-6*(2624733233041/200000000000:ℝ)+4*(2624733233041/200000000000:ℝ)^2)*(571108641/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_366 :
    ∀ u ∈ Set.Icc (183/256:ℝ) (367/512:ℝ), (3342578199994124527397/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13175030742289/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(367/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(367/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (183/256:ℝ) (367/512:ℝ) (13175030742289/1000000000000:ℝ) (108608917/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1099).1
  intro u hu
  exact (show (3342578199994124527397/1000000000000000000000000:ℝ) ≤ (1/4-6*(13175030742289/1000000000000:ℝ)+4*(13175030742289/1000000000000:ℝ)^2)*(108608917/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_367 :
    ∀ u ∈ Set.Icc (367/512:ℝ) (23/32:ℝ), (640840523008283373147/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13226596354643/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (367/512:ℝ) (23/32:ℝ) (13226596354643/1000000000000:ℝ) (51625579/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1104).1
  intro u hu
  exact (show (640840523008283373147/200000000000000000000000:ℝ) ≤ (1/4-6*(13226596354643/1000000000000:ℝ)+4*(13226596354643/1000000000000:ℝ)^2)*(51625579/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_368 :
    ∀ u ∈ Set.Icc (23/32:ℝ) (369/512:ℝ), (614185791481402863651/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6639181894549/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(369/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(369/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (23/32:ℝ) (369/512:ℝ) (6639181894549/500000000000:ℝ) (490689463/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1105).1
  intro u hu
  exact (show (614185791481402863651/200000000000000000000000:ℝ) ≤ (1/4-6*(6639181894549/500000000000:ℝ)+4*(6639181894549/500000000000:ℝ)^2)*(490689463/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_369 :
    ∀ u ∈ Set.Icc (369/512:ℝ) (185/256:ℝ), (735648995948273803559/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13330333835563/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(185/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(185/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (369/512:ℝ) (185/256:ℝ) (13330333835563/1000000000000:ℝ) (233147381/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1110).1
  intro u hu
  exact (show (735648995948273803559/250000000000000000000000:ℝ) ≤ (1/4-6*(13330333835563/1000000000000:ℝ)+4*(13330333835563/1000000000000:ℝ)^2)*(233147381/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_370 :
    ∀ u ∈ Set.Icc (185/256:ℝ) (371/512:ℝ), (140952322835148533423/50000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13382507287039/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(371/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(371/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (185/256:ℝ) (371/512:ℝ) (13382507287039/1000000000000:ℝ) (110755681/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1111).1
  intro u hu
  exact (show (140952322835148533423/50000000000000000000000:ℝ) ≤ (1/4-6*(13382507287039/1000000000000:ℝ)+4*(13382507287039/1000000000000:ℝ)^2)*(110755681/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_371 :
    ∀ u ∈ Set.Icc (371/512:ℝ) (93/128:ℝ), (2700127143493966204823/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1343488493963/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(93/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (371/512:ℝ) (93/128:ℝ) (1343488493963/100000000000:ℝ) (84165243/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1116).1
  intro u hu
  exact (show (2700127143493966204823/1000000000000000000000000:ℝ) ≤ (1/4-6*(1343488493963/100000000000:ℝ)+4*(1343488493963/100000000000:ℝ)^2)*(84165243/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_372 :
    ∀ u ∈ Set.Icc (93/128:ℝ) (373/512:ℝ), (517137743580598619471/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13487467592557/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(373/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(373/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (93/128:ℝ) (373/512:ℝ) (13487467592557/1000000000000:ℝ) (199829933/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1117).1
  intro u hu
  exact (show (517137743580598619471/200000000000000000000000:ℝ) ≤ (1/4-6*(13487467592557/1000000000000:ℝ)+4*(13487467592557/1000000000000:ℝ)^2)*(199829933/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_373 :
    ∀ u ∈ Set.Icc (373/512:ℝ) (187/256:ℝ), (24755857020076652059/10000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13540256048169/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(187/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(187/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (373/512:ℝ) (187/256:ℝ) (13540256048169/1000000000000:ℝ) (379480017/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1122).1
  intro u hu
  exact (show (24755857020076652059/10000000000000000000000:ℝ) ≤ (1/4-6*(13540256048169/1000000000000:ℝ)+4*(13540256048169/1000000000000:ℝ)^2)*(379480017/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_374 :
    ∀ u ∈ Set.Icc (187/256:ℝ) (375/512:ℝ), (592419104592830041533/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6796625555977/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(375/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(375/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (187/256:ℝ) (375/512:ℝ) (6796625555977/500000000000:ℝ) (45030583/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1123).1
  intro u hu
  exact (show (592419104592830041533/250000000000000000000000:ℝ) ≤ (1/4-6*(6796625555977/500000000000:ℝ)+4*(6796625555977/500000000000:ℝ)^2)*(45030583/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_375 :
    ∀ u ∈ Set.Icc (375/512:ℝ) (47/64:ℝ), (2267822886854552488229/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2729290718511/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (375/512:ℝ) (47/64:ℝ) (2729290718511/200000000000:ℝ) (341913399/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1128).1
  intro u hu
  exact (show (2267822886854552488229/1000000000000000000000000:ℝ) ≤ (1/4-6*(2729290718511/200000000000:ℝ)+4*(2729290718511/200000000000:ℝ)^2)*(341913399/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_376 :
    ∀ u ∈ Set.Icc (47/64:ℝ) (377/512:ℝ), (2169890816883034985239/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13699864301777/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(377/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(377/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (47/64:ℝ) (377/512:ℝ) (13699864301777/1000000000000:ℝ) (162223683/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1129).1
  intro u hu
  exact (show (2169890816883034985239/1000000000000000000000000:ℝ) ≤ (1/4-6*(13699864301777/1000000000000:ℝ)+4*(13699864301777/1000000000000:ℝ)^2)*(162223683/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_377 :
    ∀ u ∈ Set.Icc (377/512:ℝ) (189/256:ℝ), (259468686495719689509/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2750696810921/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(189/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(189/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (377/512:ℝ) (189/256:ℝ) (2750696810921/200000000000:ℝ) (153904601/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1134).1
  intro u hu
  exact (show (259468686495719689509/125000000000000000000000:ℝ) ≤ (1/4-6*(2750696810921/200000000000:ℝ)+4*(2750696810921/200000000000:ℝ)^2)*(153904601/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_378 :
    ∀ u ∈ Set.Icc (189/256:ℝ) (379/512:ℝ), (397054344780609058479/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13807313669211/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(379/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(379/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (189/256:ℝ) (379/512:ℝ) (13807313669211/1000000000000:ℝ) (29196299/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1135).1
  intro u hu
  exact (show (397054344780609058479/200000000000000000000000:ℝ) ≤ (1/4-6*(13807313669211/1000000000000:ℝ)+4*(13807313669211/1000000000000:ℝ)^2)*(29196299/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_379 :
    ∀ u ∈ Set.Icc (379/512:ℝ) (95/128:ℝ), (379666759753091419853/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3465338491743/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(95/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (379/512:ℝ) (95/128:ℝ) (3465338491743/250000000000:ℝ) (69218553/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1140).1
  intro u hu
  exact (show (379666759753091419853/200000000000000000000000:ℝ) ≤ (1/4-6*(3465338491743/250000000000:ℝ)+4*(3465338491743/250000000000:ℝ)^2)*(69218553/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_380 :
    ∀ u ∈ Set.Icc (95/128:ℝ) (381/512:ℝ), (1814815400513528103253/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (13915605772479/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(381/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(381/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (95/128:ℝ) (381/512:ℝ) (13915605772479/1000000000000:ℝ) (2625097/1000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1141).1
  intro u hu
  exact (show (1814815400513528103253/1000000000000000000000000:ℝ) ≤ (1/4-6*(13915605772479/1000000000000:ℝ)+4*(13915605772479/1000000000000:ℝ)^2)*(2625097/1000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_381 :
    ∀ u ∈ Set.Icc (381/512:ℝ) (191/256:ℝ), (1734599552978536839827/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3492517478387/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(191/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(191/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (381/512:ℝ) (191/256:ℝ) (3492517478387/250000000000:ℝ) (248837591/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1146).1
  intro u hu
  exact (show (1734599552978536839827/1000000000000000000000000:ℝ) ≤ (1/4-6*(3492517478387/250000000000:ℝ)+4*(3492517478387/250000000000:ℝ)^2)*(248837591/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_382 :
    ∀ u ∈ Set.Icc (191/256:ℝ) (383/512:ℝ), (207196567415648073727/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14024747221239/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(383/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(383/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (191/256:ℝ) (383/512:ℝ) (14024747221239/1000000000000:ℝ) (2947841/1250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1147).1
  intro u hu
  exact (show (207196567415648073727/125000000000000000000000:ℝ) ≤ (1/4-6*(14024747221239/1000000000000:ℝ)+4*(14024747221239/1000000000000:ℝ)^2)*(2947841/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_383 :
    ∀ u ∈ Set.Icc (383/512:ℝ) (3/4:ℝ), (158362387583252580279/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (14079638529861/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/4:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/4:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (383/512:ℝ) (3/4:ℝ) (14079638529861/1000000000000:ℝ) (111724691/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1152).1
  intro u hu
  exact (show (158362387583252580279/100000000000000000000000:ℝ) ≤ (1/4-6*(14079638529861/1000000000000:ℝ)+4*(14079638529861/1000000000000:ℝ)^2)*(111724691/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

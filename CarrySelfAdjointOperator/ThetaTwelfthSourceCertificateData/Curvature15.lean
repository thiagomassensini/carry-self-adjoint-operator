import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_480 :
    ∀ u ∈ Set.Icc (15/16:ℝ) (481/512:ℝ), (5873422074674114321/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10282966076421/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(481/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(481/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (15/16:ℝ) (481/512:ℝ) (10282966076421/500000000000:ℝ) (374417/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1441).1
  intro u hu
  exact (show (5873422074674114321/1000000000000000000000000:ℝ) ≤ (1/4-6*(10282966076421/500000000000:ℝ)+4*(10282966076421/500000000000:ℝ)^2)*(374417/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_481 :
    ∀ u ∈ Set.Icc (481/512:ℝ) (241/256:ℝ), (2734347372851105041/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5161606233857/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(241/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(241/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (481/512:ℝ) (241/256:ℝ) (5161606233857/250000000000:ℝ) (172899/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1446).1
  intro u hu
  exact (show (2734347372851105041/500000000000000000000000:ℝ) ≤ (1/4-6*(5161606233857/250000000000:ℝ)+4*(5161606233857/250000000000:ℝ)^2)*(172899/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_482 :
    ∀ u ∈ Set.Icc (241/256:ℝ) (483/512:ℝ), (5090231265906272769/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10363616378929/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(483/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(483/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (241/256:ℝ) (483/512:ℝ) (10363616378929/500000000000:ℝ) (63853/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1447).1
  intro u hu
  exact (show (5090231265906272769/1000000000000000000000000:ℝ) ≤ (1/4-6*(10363616378929/500000000000:ℝ)+4*(10363616378929/500000000000:ℝ)^2)*(63853/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_483 :
    ∀ u ∈ Set.Icc (483/512:ℝ) (121/128:ℝ), (4736460730020299177/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10404178426581/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(121/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (483/512:ℝ) (121/128:ℝ) (10404178426581/500000000000:ℝ) (11787/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1452).1
  intro u hu
  exact (show (4736460730020299177/1000000000000000000000000:ℝ) ≤ (1/4-6*(10404178426581/500000000000:ℝ)+4*(10404178426581/500000000000:ℝ)^2)*(11787/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_484 :
    ∀ u ∈ Set.Icc (121/128:ℝ) (485/512:ℝ), (2202939523384069869/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10444899229599/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(485/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(485/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (121/128:ℝ) (485/512:ℝ) (10444899229599/500000000000:ℝ) (271893/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1453).1
  intro u hu
  exact (show (2202939523384069869/500000000000000000000000:ℝ) ≤ (1/4-6*(10444899229599/500000000000:ℝ)+4*(10444899229599/500000000000:ℝ)^2)*(271893/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_485 :
    ∀ u ∈ Set.Icc (485/512:ℝ) (243/256:ℝ), (4097052885021176591/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5242889704667/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(243/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(243/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (485/512:ℝ) (243/256:ℝ) (5242889704667/250000000000:ℝ) (31349/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1458).1
  intro u hu
  exact (show (4097052885021176591/1000000000000000000000000:ℝ) ≤ (1/4-6*(5242889704667/250000000000:ℝ)+4*(5242889704667/250000000000:ℝ)^2)*(31349/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_486 :
    ∀ u ∈ Set.Icc (243/256:ℝ) (487/512:ℝ), (761731332756242597/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (21053639179137/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(487/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(487/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (243/256:ℝ) (487/512:ℝ) (21053639179137/1000000000000:ℝ) (46251/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1459).1
  intro u hu
  exact (show (761731332756242597/200000000000000000000000:ℝ) ≤ (1/4-6*(21053639179137/1000000000000:ℝ)+4*(21053639179137/1000000000000:ℝ)^2)*(46251/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_487 :
    ∀ u ∈ Set.Icc (487/512:ℝ) (61/64:ℝ), (3539411636629536411/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (21136040793053/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (487/512:ℝ) (61/64:ℝ) (21136040793053/1000000000000:ℝ) (213171/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1464).1
  intro u hu
  exact (show (3539411636629536411/1000000000000000000000000:ℝ) ≤ (1/4-6*(21136040793053/1000000000000:ℝ)+4*(21136040793053/1000000000000:ℝ)^2)*(213171/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_488 :
    ∀ u ∈ Set.Icc (61/64:ℝ) (489/512:ℝ), (822034761104539841/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2652345614721/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(489/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(489/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (61/64:ℝ) (489/512:ℝ) (2652345614721/125000000000:ℝ) (98219/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1465).1
  intro u hu
  exact (show (822034761104539841/250000000000000000000000:ℝ) ≤ (1/4-6*(2652345614721/125000000000:ℝ)+4*(2652345614721/125000000000:ℝ)^2)*(98219/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_489 :
    ∀ u ∈ Set.Icc (489/512:ℝ) (245/256:ℝ), (610742909844803541/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (21301812815553/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(245/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(245/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (489/512:ℝ) (245/256:ℝ) (21301812815553/1000000000000:ℝ) (1131/625000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1470).1
  intro u hu
  exact (show (610742909844803541/200000000000000000000000:ℝ) ≤ (1/4-6*(21301812815553/1000000000000:ℝ)+4*(21301812815553/1000000000000:ℝ)^2)*(1131/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_490 :
    ∀ u ∈ Set.Icc (245/256:ℝ) (491/512:ℝ), (177191960167171811/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (21385185753619/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(491/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(491/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (245/256:ℝ) (491/512:ℝ) (21385185753619/1000000000000:ℝ) (166647/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1471).1
  intro u hu
  exact (show (177191960167171811/62500000000000000000000:ℝ) ≤ (1/4-6*(21385185753619/1000000000000:ℝ)+4*(21385185753619/1000000000000:ℝ)^2)*(166647/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_491 :
    ∀ u ∈ Set.Icc (491/512:ℝ) (123/128:ℝ), (2631237758612373687/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (21468885004139/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (491/512:ℝ) (123/128:ℝ) (21468885004139/1000000000000:ℝ) (153417/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1476).1
  intro u hu
  exact (show (2631237758612373687/1000000000000000000000000:ℝ) ≤ (1/4-6*(21468885004139/1000000000000:ℝ)+4*(21468885004139/1000000000000:ℝ)^2)*(153417/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_492 :
    ∀ u ∈ Set.Icc (123/128:ℝ) (493/512:ℝ), (2441238021041889237/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10776455922131/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(493/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(493/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (123/128:ℝ) (493/512:ℝ) (10776455922131/500000000000:ℝ) (14119/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1477).1
  intro u hu
  exact (show (2441238021041889237/1000000000000000000000000:ℝ) ≤ (1/4-6*(10776455922131/500000000000:ℝ)+4*(10776455922131/500000000000:ℝ)^2)*(14119/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_493 :
    ∀ u ∈ Set.Icc (493/512:ℝ) (247/256:ℝ), (2264215051628209499/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1081863377807/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(247/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(247/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (493/512:ℝ) (247/256:ℝ) (1081863377807/50000000000:ℝ) (25979/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1482).1
  intro u hu
  exact (show (2264215051628209499/1000000000000000000000000:ℝ) ≤ (1/4-6*(1081863377807/50000000000:ℝ)+4*(1081863377807/50000000000:ℝ)^2)*(25979/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_494 :
    ∀ u ∈ Set.Icc (247/256:ℝ) (495/512:ℝ), (2099330505113338621/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (21721953426939/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(495/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(495/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (247/256:ℝ) (495/512:ℝ) (21721953426939/1000000000000:ℝ) (14933/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1483).1
  intro u hu
  exact (show (2099330505113338621/1000000000000000000000000:ℝ) ≤ (1/4-6*(21721953426939/1000000000000:ℝ)+4*(21721953426939/1000000000000:ℝ)^2)*(14933/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_495 :
    ∀ u ∈ Set.Icc (495/512:ℝ) (31/32:ℝ), (1945819361608664979/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4361394149773/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (495/512:ℝ) (31/32:ℝ) (4361394149773/200000000000:ℝ) (21967/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1488).1
  intro u hu
  exact (show (1945819361608664979/1000000000000000000000000:ℝ) ≤ (1/4-6*(4361394149773/200000000000:ℝ)+4*(4361394149773/200000000000:ℝ)^2)*(21967/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_496 :
    ∀ u ∈ Set.Icc (31/32:ℝ) (497/512:ℝ), (225365264048970199/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1094616040959/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(497/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(497/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (31/32:ℝ) (497/512:ℝ) (1094616040959/50000000000:ℝ) (25237/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1489).1
  intro u hu
  exact (show (225365264048970199/125000000000000000000000:ℝ) ≤ (1/4-6*(1094616040959/50000000000:ℝ)+4*(1094616040959/50000000000:ℝ)^2)*(25237/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_497 :
    ∀ u ∈ Set.Icc (497/512:ℝ) (249/256:ℝ), (1669957593656032913/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (10989002470113/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(249/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(249/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (497/512:ℝ) (249/256:ℝ) (10989002470113/500000000000:ℝ) (92749/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1494).1
  intro u hu
  exact (show (1669957593656032913/1000000000000000000000000:ℝ) ≤ (1/4-6*(10989002470113/500000000000:ℝ)+4*(10989002470113/500000000000:ℝ)^2)*(92749/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_498 :
    ∀ u ∈ Set.Icc (249/256:ℝ) (499/512:ℝ), (1546272297162852323/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (275800305243/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(499/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(499/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (249/256:ℝ) (499/512:ℝ) (275800305243/12500000000:ℝ) (85187/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1495).1
  intro u hu
  exact (show (1546272297162852323/1000000000000000000000000:ℝ) ≤ (1/4-6*(275800305243/12500000000:ℝ)+4*(275800305243/12500000000:ℝ)^2)*(85187/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_499 :
    ∀ u ∈ Set.Icc (499/512:ℝ) (125/128:ℝ), (1431278615296834699/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (692199392793/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(125/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (499/512:ℝ) (125/128:ℝ) (692199392793/31250000000:ℝ) (9777/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1500).1
  intro u hu
  exact (show (1431278615296834699/1000000000000000000000000:ℝ) ≤ (1/4-6*(692199392793/31250000000:ℝ)+4*(692199392793/31250000000:ℝ)^2)*(9777/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_500 :
    ∀ u ∈ Set.Icc (125/128:ℝ) (501/512:ℝ), (165548028491786147/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (22237074707727/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(501/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(501/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (125/128:ℝ) (501/512:ℝ) (22237074707727/1000000000000:ℝ) (71791/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1501).1
  intro u hu
  exact (show (165548028491786147/125000000000000000000000:ℝ) ≤ (1/4-6*(22237074707727/1000000000000:ℝ)+4*(22237074707727/1000000000000:ℝ)^2)*(71791/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_501 :
    ∀ u ∈ Set.Icc (501/512:ℝ) (251/256:ℝ), (612524077747350281/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (22324108157341/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(251/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(251/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (501/512:ℝ) (251/256:ℝ) (22324108157341/1000000000000:ℝ) (65871/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1506).1
  intro u hu
  exact (show (612524077747350281/500000000000000000000000:ℝ) ≤ (1/4-6*(22324108157341/1000000000000:ℝ)+4*(22324108157341/1000000000000:ℝ)^2)*(65871/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_502 :
    ∀ u ∈ Set.Icc (251/256:ℝ) (503/512:ℝ), (70798955969898033/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (22411482246247/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(503/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(503/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (251/256:ℝ) (503/512:ℝ) (22411482246247/1000000000000:ℝ) (60419/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1507).1
  intro u hu
  exact (show (70798955969898033/62500000000000000000000:ℝ) ≤ (1/4-6*(22411482246247/1000000000000:ℝ)+4*(22411482246247/1000000000000:ℝ)^2)*(60419/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_503 :
    ∀ u ∈ Set.Icc (503/512:ℝ) (63/64:ℝ), (209420464077006753/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (22499198307667/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (503/512:ℝ) (63/64:ℝ) (22499198307667/1000000000000:ℝ) (55399/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1512).1
  intro u hu
  exact (show (209420464077006753/200000000000000000000000:ℝ) ≤ (1/4-6*(22499198307667/1000000000000:ℝ)+4*(22499198307667/1000000000000:ℝ)^2)*(55399/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_504 :
    ∀ u ∈ Set.Icc (63/64:ℝ) (505/512:ℝ), (967556150380563339/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5646814420011/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(505/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(505/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (63/64:ℝ) (505/512:ℝ) (5646814420011/250000000000:ℝ) (25389/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1513).1
  intro u hu
  exact (show (967556150380563339/1000000000000000000000000:ℝ) ≤ (1/4-6*(5646814420011/250000000000:ℝ)+4*(5646814420011/250000000000:ℝ)^2)*(25389/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_505 :
    ∀ u ∈ Set.Icc (505/512:ℝ) (253/256:ℝ), (223443573900565599/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (22675661707061/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(253/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(253/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (505/512:ℝ) (253/256:ℝ) (22675661707061/1000000000000:ℝ) (727/1562500000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1518).1
  intro u hu
  exact (show (223443573900565599/250000000000000000000000:ℝ) ≤ (1/4-6*(22675661707061/1000000000000:ℝ)+4*(22675661707061/1000000000000:ℝ)^2)*(727/1562500000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_506 :
    ∀ u ∈ Set.Icc (253/256:ℝ) (507/512:ℝ), (825313465073590469/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2845551467207/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(507/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(507/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (253/256:ℝ) (507/512:ℝ) (2845551467207/125000000000:ℝ) (21309/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1519).1
  intro u hu
  exact (show (825313465073590469/1000000000000000000000000:ℝ) ≤ (1/4-6*(2845551467207/125000000000:ℝ)+4*(2845551467207/125000000000:ℝ)^2)*(21309/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_507 :
    ∀ u ∈ Set.Icc (507/512:ℝ) (127/128:ℝ), (152366120075123307/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (457070182521/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(127/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(127/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (507/512:ℝ) (127/128:ℝ) (457070182521/20000000000:ℝ) (39023/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1524).1
  intro u hu
  exact (show (152366120075123307/200000000000000000000000:ℝ) ≤ (1/4-6*(457070182521/20000000000:ℝ)+4*(457070182521/20000000000:ℝ)^2)*(39023/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_508 :
    ∀ u ∈ Set.Icc (127/128:ℝ) (509/512:ℝ), (702988870739379477/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11471477615881/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(509/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(509/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (127/128:ℝ) (509/512:ℝ) (11471477615881/500000000000:ℝ) (35719/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1525).1
  intro u hu
  exact (show (702988870739379477/1000000000000000000000000:ℝ) ≤ (1/4-6*(11471477615881/500000000000:ℝ)+4*(11471477615881/500000000000:ℝ)^2)*(35719/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_509 :
    ∀ u ∈ Set.Icc (509/512:ℝ) (255/256:ℝ), (324229093938615553/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (11516375709817/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(255/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(255/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (509/512:ℝ) (255/256:ℝ) (11516375709817/500000000000:ℝ) (32683/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1530).1
  intro u hu
  exact (show (324229093938615553/500000000000000000000000:ℝ) ≤ (1/4-6*(11516375709817/500000000000:ℝ)+4*(11516375709817/500000000000:ℝ)^2)*(32683/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_510 :
    ∀ u ∈ Set.Icc (255/256:ℝ) (511/512:ℝ), (597955739038740007/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2890362382481/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(511/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(511/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (255/256:ℝ) (511/512:ℝ) (2890362382481/125000000000:ℝ) (5979/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1531).1
  intro u hu
  exact (show (597955739038740007/1000000000000000000000000:ℝ) ≤ (1/4-6*(2890362382481/125000000000:ℝ)+4*(2890362382481/125000000000:ℝ)^2)*(5979/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_511 :
    ∀ u ∈ Set.Icc (511/512:ℝ) (1/1:ℝ), (275593830843204751/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (464267990559/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/1:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/1:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (511/512:ℝ) (1/1:ℝ) (464267990559/20000000000:ℝ) (5467/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_1536).1
  intro u hu
  exact (show (275593830843204751/500000000000000000000000:ℝ) ≤ (1/4-6*(464267990559/20000000000:ℝ)+4*(464267990559/20000000000:ℝ)^2)*(5467/20000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

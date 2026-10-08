import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_096 :
    ∀ u ∈ Set.Icc (3/8:ℝ) (97/256:ℝ), (814502165006677/2000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (66507503159/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/8:ℝ)) := by
    calc
      (66507503159/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(3/8:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(3/8:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (3/8:ℝ) (97/256:ℝ) (66507503159/10000000000:ℝ) (1186668643/400000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0582).1
  intro u hu
  exact (show (814502165006677/2000000000000000:ℝ) ≤ (1/4-6*(66507503159/10000000000:ℝ)+4*(66507503159/10000000000:ℝ)^2)*(1186668643/400000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_097 :
    ∀ u ∈ Set.Icc (97/256:ℝ) (49/128:ℝ), (394124895899789529/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (67029127971/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/256:ℝ)) := by
    calc
      (67029127971/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(97/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(97/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (97/256:ℝ) (49/128:ℝ) (67029127971/10000000000:ℝ) (282024050041/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0588).1
  intro u hu
  exact (show (394124895899789529/1000000000000000000:ℝ) ≤ (1/4-6*(67029127971/10000000000:ℝ)+4*(67029127971/10000000000:ℝ)^2)*(282024050041/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_098 :
    ∀ u ∈ Set.Icc (49/128:ℝ) (99/256:ℝ), (76251226959833959/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (67554843937/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/128:ℝ)) := by
    calc
      (67554843937/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(49/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(49/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (49/128:ℝ) (99/256:ℝ) (67554843937/10000000000:ℝ) (133996590813/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0594).1
  intro u hu
  exact (show (76251226959833959/200000000000000000:ℝ) ≤ (1/4-6*(67554843937/10000000000:ℝ)+4*(67554843937/10000000000:ℝ)^2)*(133996590813/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_099 :
    ∀ u ∈ Set.Icc (99/256:ℝ) (25/64:ℝ), (368646294189955231/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (13616936629/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/256:ℝ)) := by
    calc
      (13616936629/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(99/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(99/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (99/256:ℝ) (25/64:ℝ) (13616936629/2000000000:ℝ) (12727727663/5000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0600).1
  intro u hu
  exact (show (368646294189955231/1000000000000000000:ℝ) ≤ (1/4-6*(13616936629/2000000000:ℝ)+4*(13616936629/2000000000:ℝ)^2)*(12727727663/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_100 :
    ∀ u ∈ Set.Icc (25/64:ℝ) (101/256:ℝ), (356296586964953583/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (17154669483/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(25/64:ℝ)) := by
    calc
      (17154669483/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(25/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(25/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (25/64:ℝ) (101/256:ℝ) (17154669483/2500000000:ℝ) (241688565857/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0606).1
  intro u hu
  exact (show (356296586964953583/1000000000000000000:ℝ) ≤ (1/4-6*(17154669483/2500000000:ℝ)+4*(17154669483/2500000000:ℝ)^2)*(241688565857/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_101 :
    ∀ u ∈ Set.Icc (101/256:ℝ) (51/128:ℝ), (34420794807094063/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (69156860893/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/256:ℝ)) := by
    calc
      (69156860893/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(101/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(101/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (101/256:ℝ) (51/128:ℝ) (69156860893/10000000000:ℝ) (22937602533/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0612).1
  intro u hu
  exact (show (34420794807094063/100000000000000000:ℝ) ≤ (1/4-6*(69156860893/10000000000:ℝ)+4*(69156860893/10000000000:ℝ)^2)*(22937602533/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_102 :
    ∀ u ∈ Set.Icc (51/128:ℝ) (103/256:ℝ), (332381038839280923/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (557594119/80000000:ℝ) ≤ Real.pi*Real.exp (2*(51/128:ℝ)) := by
    calc
      (557594119/80000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(51/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(51/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (51/128:ℝ) (103/256:ℝ) (557594119/80000000:ℝ) (3399971/1562500000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0618).1
  intro u hu
  exact (show (332381038839280923/1000000000000000000:ℝ) ≤ (1/4-6*(557594119/80000000:ℝ)+4*(557594119/80000000:ℝ)^2)*(3399971/1562500000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_103 :
    ∀ u ∈ Set.Icc (103/256:ℝ) (13/32:ℝ), (40102031478612231/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (8780740373/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(103/256:ℝ)) := by
    calc
      (8780740373/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(103/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(103/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (103/256:ℝ) (13/32:ℝ) (8780740373/1250000000:ℝ) (103168270791/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0624).1
  intro u hu
  exact (show (40102031478612231/125000000000000000:ℝ) ≤ (1/4-6*(8780740373/1250000000:ℝ)+4*(8780740373/1250000000:ℝ)^2)*(103168270791/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_104 :
    ∀ u ∈ Set.Icc (13/32:ℝ) (105/256:ℝ), (30951371593757961/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (35398434293/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/32:ℝ)) := by
    calc
      (35398434293/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(13/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(13/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (13/32:ℝ) (105/256:ℝ) (35398434293/5000000000:ℝ) (48893311439/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0630).1
  intro u hu
  exact (show (30951371593757961/100000000000000000:ℝ) ≤ (1/4-6*(35398434293/5000000000:ℝ)+4*(35398434293/5000000000:ℝ)^2)*(48893311439/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_105 :
    ∀ u ∈ Set.Icc (105/256:ℝ) (53/128:ℝ), (298473301835686887/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (17838033827/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(105/256:ℝ)) := by
    calc
      (17838033827/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(105/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(105/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (105/256:ℝ) (53/128:ℝ) (17838033827/2500000000:ℝ) (7411627693/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0636).1
  intro u hu
  exact (show (298473301835686887/1000000000000000000:ℝ) ≤ (1/4-6*(17838033827/2500000000:ℝ)+4*(17838033827/2500000000:ℝ)^2)*(7411627693/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_106 :
    ∀ u ∈ Set.Icc (53/128:ℝ) (107/256:ℝ), (143847313866595999/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (898896963/125000000:ℝ) ≤ Real.pi*Real.exp (2*(53/128:ℝ)) := by
    calc
      (898896963/125000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(53/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(53/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (53/128:ℝ) (107/256:ℝ) (898896963/125000000:ℝ) (175471724979/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0642).1
  intro u hu
  exact (show (143847313866595999/500000000000000000:ℝ) ≤ (1/4-6*(898896963/125000000:ℝ)+4*(898896963/125000000:ℝ)^2)*(175471724979/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_107 :
    ∀ u ∈ Set.Icc (107/256:ℝ) (27/64:ℝ), (55435413091796449/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (3623788397/500000000:ℝ) ≤ Real.pi*Real.exp (2*(107/256:ℝ)) := by
    calc
      (3623788397/500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(107/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(107/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (107/256:ℝ) (27/64:ℝ) (3623788397/500000000:ℝ) (166099594661/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0648).1
  intro u hu
  exact (show (55435413091796449/200000000000000000:ℝ) ≤ (1/4-6*(3623788397/500000000:ℝ)+4*(3623788397/500000000:ℝ)^2)*(166099594661/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_108 :
    ∀ u ∈ Set.Icc (27/64:ℝ) (109/256:ℝ), (133459873385764947/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (1141315663/156250000:ℝ) ≤ Real.pi*Real.exp (2*(27/64:ℝ)) := by
    calc
      (1141315663/156250000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(27/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(27/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (27/64:ℝ) (109/256:ℝ) (1141315663/156250000:ℝ) (982237241/625000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0654).1
  intro u hu
  exact (show (133459873385764947/500000000000000000:ℝ) ≤ (1/4-6*(1141315663/156250000:ℝ)+4*(1141315663/156250000:ℝ)^2)*(982237241/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_109 :
    ∀ u ∈ Set.Icc (109/256:ℝ) (55/128:ℝ), (256921569980402861/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (73617095211/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(109/256:ℝ)) := by
    calc
      (73617095211/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(109/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(109/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (109/256:ℝ) (55/128:ℝ) (73617095211/10000000000:ℝ) (58058937/39062500000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0660).1
  intro u hu
  exact (show (256921569980402861/1000000000000000000:ℝ) ≤ (1/4-6*(73617095211/10000000000:ℝ)+4*(73617095211/10000000000:ℝ)^2)*(58058937/39062500000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_110 :
    ∀ u ∈ Set.Icc (55/128:ℝ) (111/256:ℝ), (247181206801729151/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (18548620311/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(55/128:ℝ)) := by
    calc
      (18548620311/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(55/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(55/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (55/128:ℝ) (111/256:ℝ) (18548620311/2500000000:ℝ) (1405028203/1000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0666).1
  intro u hu
  exact (show (247181206801729151/1000000000000000000:ℝ) ≤ (1/4-6*(18548620311/2500000000:ℝ)+4*(18548620311/2500000000:ℝ)^2)*(1405028203/1000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_111 :
    ∀ u ∈ Set.Icc (111/256:ℝ) (7/16:ℝ), (59424277358972619/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (74776395771/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(111/256:ℝ)) := by
    calc
      (74776395771/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(111/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(111/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (111/256:ℝ) (7/16:ℝ) (74776395771/10000000000:ℝ) (5310345979/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0672).1
  intro u hu
  exact (show (59424277358972619/250000000000000000:ℝ) ≤ (1/4-6*(74776395771/10000000000:ℝ)+4*(74776395771/10000000000:ℝ)^2)*(5310345979/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_112 :
    ∀ u ∈ Set.Icc (7/16:ℝ) (113/256:ℝ), (57116879476505503/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (75362874311/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/16:ℝ)) := by
    calc
      (75362874311/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(7/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(7/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (7/16:ℝ) (113/256:ℝ) (75362874311/10000000000:ℝ) (62691815501/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0678).1
  intro u hu
  exact (show (57116879476505503/250000000000000000:ℝ) ≤ (1/4-6*(75362874311/10000000000:ℝ)+4*(75362874311/10000000000:ℝ)^2)*(62691815501/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_113 :
    ∀ u ∈ Set.Icc (113/256:ℝ) (57/128:ℝ), (219490467503629413/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (37976976329/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/256:ℝ)) := by
    calc
      (37976976329/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(113/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(113/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (113/256:ℝ) (57/128:ℝ) (37976976329/5000000000:ℝ) (118363425447/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0684).1
  intro u hu
  exact (show (219490467503629413/1000000000000000000:ℝ) ≤ (1/4-6*(37976976329/5000000000:ℝ)+4*(37976976329/5000000000:ℝ)^2)*(118363425447/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_114 :
    ∀ u ∈ Set.Icc (57/128:ℝ) (115/256:ℝ), (105381898272623603/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (7654966689/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/128:ℝ)) := by
    calc
      (7654966689/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(57/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(57/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (57/128:ℝ) (115/256:ℝ) (7654966689/1000000000:ℝ) (27921021529/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0690).1
  intro u hu
  exact (show (105381898272623603/500000000000000000:ℝ) ≤ (1/4-6*(7654966689/1000000000:ℝ)+4*(7654966689/1000000000:ℝ)^2)*(27921021529/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_115 :
    ∀ u ∈ Set.Icc (115/256:ℝ) (29/64:ℝ), (4045703083264843/20000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (77150053367/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/256:ℝ)) := by
    calc
      (77150053367/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(115/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(115/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (115/256:ℝ) (29/64:ℝ) (77150053367/10000000000:ℝ) (105332055653/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0696).1
  intro u hu
  exact (show (4045703083264843/20000000000000000:ℝ) ≤ (1/4-6*(77150053367/10000000000:ℝ)+4*(77150053367/10000000000:ℝ)^2)*(105332055653/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_116 :
    ∀ u ∈ Set.Icc (29/64:ℝ) (117/256:ℝ), (97026004163419267/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (77755148733/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/64:ℝ)) := by
    calc
      (77755148733/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(29/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(29/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (29/64:ℝ) (117/256:ℝ) (77755148733/10000000000:ℝ) (794353299/800000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0702).1
  intro u hu
  exact (show (97026004163419267/500000000000000000:ℝ) ≤ (1/4-6*(77755148733/10000000000:ℝ)+4*(77755148733/10000000000:ℝ)^2)*(794353299/800000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_117 :
    ∀ u ∈ Set.Icc (117/256:ℝ) (59/128:ℝ), (186061653955860893/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (78364989921/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(117/256:ℝ)) := by
    calc
      (78364989921/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(117/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(117/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (117/256:ℝ) (59/128:ℝ) (78364989921/10000000000:ℝ) (935576163/1000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0708).1
  intro u hu
  exact (show (186061653955860893/1000000000000000000:ℝ) ≤ (1/4-6*(78364989921/10000000000:ℝ)+4*(78364989921/10000000000:ℝ)^2)*(935576163/1000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_118 :
    ∀ u ∈ Set.Icc (59/128:ℝ) (119/256:ℝ), (89155610570721081/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (9872451769/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(59/128:ℝ)) := by
    calc
      (9872451769/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(59/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(59/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (59/128:ℝ) (119/256:ℝ) (9872451769/1250000000:ℝ) (3524400197/4000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0714).1
  intro u hu
  exact (show (89155610570721081/500000000000000000:ℝ) ≤ (1/4-6*(9872451769/1250000000:ℝ)+4*(9872451769/1250000000:ℝ)^2)*(3524400197/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_119 :
    ∀ u ∈ Set.Icc (119/256:ℝ) (15/32:ℝ), (42699420868835591/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (3979952947/500000000:ℝ) ≤ Real.pi*Real.exp (2*(119/256:ℝ)) := by
    calc
      (3979952947/500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(119/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(119/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (119/256:ℝ) (15/32:ℝ) (3979952947/500000000:ℝ) (82939288741/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0720).1
  intro u hu
  exact (show (42699420868835591/250000000000000000:ℝ) ≤ (1/4-6*(3979952947/500000000:ℝ)+4*(3979952947/500000000:ℝ)^2)*(82939288741/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_120 :
    ∀ u ∈ Set.Icc (15/32:ℝ) (121/256:ℝ), (3270357328822397/20000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (40111681047/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/32:ℝ)) := by
    calc
      (40111681047/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(15/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(15/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (15/32:ℝ) (121/256:ℝ) (40111681047/5000000000:ℝ) (7803379651/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0726).1
  intro u hu
  exact (show (3270357328822397/20000000000000000:ℝ) ≤ (1/4-6*(40111681047/5000000000:ℝ)+4*(40111681047/5000000000:ℝ)^2)*(7803379651/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_121 :
    ∀ u ∈ Set.Icc (121/256:ℝ) (61/128:ℝ), (156468455838422989/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (40426280859/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/256:ℝ)) := by
    calc
      (40426280859/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(121/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(121/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (121/256:ℝ) (61/128:ℝ) (40426280859/5000000000:ℝ) (73382220307/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0732).1
  intro u hu
  exact (show (156468455838422989/1000000000000000000:ℝ) ≤ (1/4-6*(40426280859/5000000000:ℝ)+4*(40426280859/5000000000:ℝ)^2)*(73382220307/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_122 :
    ∀ u ∈ Set.Icc (61/128:ℝ) (123/256:ℝ), (149646006282575861/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (10185837027/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(61/128:ℝ)) := by
    calc
      (10185837027/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(61/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(61/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (61/128:ℝ) (123/256:ℝ) (10185837027/1250000000:ℝ) (34486805177/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0738).1
  intro u hu
  exact (show (149646006282575861/1000000000000000000:ℝ) ≤ (1/4-6*(10185837027/1250000000:ℝ)+4*(10185837027/1250000000:ℝ)^2)*(34486805177/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_123 :
    ∀ u ∈ Set.Icc (123/256:ℝ) (31/64:ℝ), (35761737420459491/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (82125804291/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/256:ℝ)) := by
    calc
      (82125804291/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(123/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(123/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (123/256:ℝ) (31/64:ℝ) (82125804291/10000000000:ℝ) (12959473929/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0744).1
  intro u hu
  exact (show (35761737420459491/250000000000000000:ℝ) ≤ (1/4-6*(82125804291/10000000000:ℝ)+4*(82125804291/10000000000:ℝ)^2)*(12959473929/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_124 :
    ∀ u ∈ Set.Icc (31/64:ℝ) (125/256:ℝ), (68333801879586489/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (82769924953/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/64:ℝ)) := by
    calc
      (82769924953/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(31/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(31/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (31/64:ℝ) (125/256:ℝ) (82769924953/10000000000:ℝ) (12168649677/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0750).1
  intro u hu
  exact (show (68333801879586489/500000000000000000:ℝ) ≤ (1/4-6*(82769924953/10000000000:ℝ)+4*(82769924953/10000000000:ℝ)^2)*(12168649677/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_125 :
    ∀ u ∈ Set.Icc (125/256:ℝ) (63/128:ℝ), (130504180498755121/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (20854774379/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(125/256:ℝ)) := by
    calc
      (20854774379/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(125/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(125/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (125/256:ℝ) (63/128:ℝ) (20854774379/2500000000:ℝ) (57101338247/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0756).1
  intro u hu
  exact (show (130504180498755121/1000000000000000000:ℝ) ≤ (1/4-6*(20854774379/2500000000:ℝ)+4*(20854774379/2500000000:ℝ)^2)*(57101338247/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_126 :
    ∀ u ∈ Set.Icc (63/128:ℝ) (127/256:ℝ), (24910558921058049/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (42036680801/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/128:ℝ)) := by
    calc
      (42036680801/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(63/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(63/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (63/128:ℝ) (127/256:ℝ) (42036680801/5000000000:ℝ) (26781033237/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0762).1
  intro u hu
  exact (show (24910558921058049/200000000000000000:ℝ) ≤ (1/4-6*(42036680801/5000000000:ℝ)+4*(42036680801/5000000000:ℝ)^2)*(26781033237/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_127 :
    ∀ u ∈ Set.Icc (127/256:ℝ) (1/2:ℝ), (118809471896163623/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (10591594643/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(127/256:ℝ)) := by
    calc
      (10591594643/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(127/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(127/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (127/256:ℝ) (1/2:ℝ) (10591594643/1250000000:ℝ) (25108094913/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0768).1
  intro u hu
  exact (show (118809471896163623/1000000000000000000:ℝ) ≤ (1/4-6*(10591594643/1250000000:ℝ)+4*(10591594643/1250000000:ℝ)^2)*(25108094913/50000000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

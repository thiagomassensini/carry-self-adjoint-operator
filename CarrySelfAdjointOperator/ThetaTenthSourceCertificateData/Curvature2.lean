import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_064 :
    ∀ u ∈ Set.Icc (1/4:ℝ) (65/256:ℝ), (938914864620939517/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (25898047771/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/4:ℝ)) := by
    calc
      (25898047771/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(1/4:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(1/4:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (1/4:ℝ) (65/256:ℝ) (25898047771/5000000000:ℝ) (1227568144983/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0390).1
  intro u hu
  exact (show (938914864620939517/1000000000000000000:ℝ) ≤ (1/4-6*(25898047771/5000000000:ℝ)+4*(25898047771/5000000000:ℝ)^2)*(1227568144983/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_065 :
    ∀ u ∈ Set.Icc (65/256:ℝ) (33/128:ℝ), (184017103411496703/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (26101168677/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(65/256:ℝ)) := by
    calc
      (26101168677/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(65/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(65/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (65/256:ℝ) (33/128:ℝ) (26101168677/5000000000:ℝ) (36894584617/3125000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0396).1
  intro u hu
  exact (show (184017103411496703/200000000000000000:ℝ) ≤ (1/4-6*(26101168677/5000000000:ℝ)+4*(26101168677/5000000000:ℝ)^2)*(36894584617/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_066 :
    ∀ u ∈ Set.Icc (33/128:ℝ) (67/256:ℝ), (901314286011735199/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (52611765361/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/128:ℝ)) := by
    calc
      (52611765361/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(33/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(33/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (33/128:ℝ) (67/256:ℝ) (52611765361/10000000000:ℝ) (567557858261/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0402).1
  intro u hu
  exact (show (901314286011735199/1000000000000000000:ℝ) ≤ (1/4-6*(52611765361/10000000000:ℝ)+4*(52611765361/10000000000:ℝ)^2)*(567557858261/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_067 :
    ∀ u ∈ Set.Icc (67/256:ℝ) (17/64:ℝ), (88261133131181809/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (53024404551/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/256:ℝ)) := by
    calc
      (53024404551/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(67/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(67/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (67/256:ℝ) (17/64:ℝ) (53024404551/10000000000:ℝ) (545502971679/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0408).1
  intro u hu
  exact (show (88261133131181809/100000000000000000:ℝ) ≤ (1/4-6*(53024404551/10000000000:ℝ)+4*(53024404551/10000000000:ℝ)^2)*(545502971679/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_068 :
    ∀ u ∈ Set.Icc (17/64:ℝ) (69/256:ℝ), (107998327769847/125000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (5344028011/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/64:ℝ)) := by
    calc
      (5344028011/1000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(17/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(17/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (17/64:ℝ) (69/256:ℝ) (5344028011/1000000000:ℝ) (52413413447/5000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0414).1
  intro u hu
  exact (show (107998327769847/125000000000000:ℝ) ≤ (1/4-6*(5344028011/1000000000:ℝ)+4*(5344028011/1000000000:ℝ)^2)*(52413413447/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_069 :
    ∀ u ∈ Set.Icc (69/256:ℝ) (35/128:ℝ), (845449928069915711/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (53859417421/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(69/256:ℝ)) := by
    calc
      (53859417421/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(69/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(69/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (69/256:ℝ) (35/128:ℝ) (53859417421/10000000000:ℝ) (251718424509/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0420).1
  intro u hu
  exact (show (845449928069915711/1000000000000000000:ℝ) ≤ (1/4-6*(53859417421/10000000000:ℝ)+4*(53859417421/10000000000:ℝ)^2)*(251718424509/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_070 :
    ∀ u ∈ Set.Icc (35/128:ℝ) (71/256:ℝ), (103376351291781417/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (13570460517/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(35/128:ℝ)) := by
    calc
      (13570460517/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(35/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(35/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (35/128:ℝ) (71/256:ℝ) (13570460517/2500000000:ℝ) (966793374627/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0426).1
  intro u hu
  exact (show (103376351291781417/125000000000000000:ℝ) ≤ (1/4-6*(13570460517/2500000000:ℝ)+4*(13570460517/2500000000:ℝ)^2)*(966793374627/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_071 :
    ∀ u ∈ Set.Icc (71/256:ℝ) (9/32:ℝ), (808678613472023763/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (6838447479/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(71/256:ℝ)) := by
    calc
      (6838447479/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(71/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(71/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (71/256:ℝ) (9/32:ℝ) (6838447479/1250000000:ℝ) (115999824587/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0432).1
  intro u hu
  exact (show (808678613472023763/1000000000000000000:ℝ) ≤ (1/4-6*(6838447479/1250000000:ℝ)+4*(6838447479/1250000000:ℝ)^2)*(115999824587/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_072 :
    ∀ u ∈ Set.Icc (9/32:ℝ) (73/256:ℝ), (24701951795471107/31250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (27568328349/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/32:ℝ)) := by
    calc
      (27568328349/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(9/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(9/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (9/32:ℝ) (73/256:ℝ) (27568328349/5000000000:ℝ) (445230415351/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0438).1
  intro u hu
  exact (show (24701951795471107/31250000000000000:ℝ) ≤ (1/4-6*(27568328349/5000000000:ℝ)+4*(27568328349/5000000000:ℝ)^2)*(445230415351/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_073 :
    ∀ u ∈ Set.Icc (73/256:ℝ) (37/128:ℝ), (386185615014076073/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (6946137357/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(73/256:ℝ)) := by
    calc
      (6946137357/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(73/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(73/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (73/256:ℝ) (37/128:ℝ) (6946137357/1250000000:ℝ) (854151725693/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0444).1
  intro u hu
  exact (show (386185615014076073/500000000000000000:ℝ) ≤ (1/4-6*(6946137357/1250000000:ℝ)+4*(6946137357/1250000000:ℝ)^2)*(854151725693/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_074 :
    ∀ u ∈ Set.Icc (37/128:ℝ) (75/256:ℝ), (75441357932300963/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (560049327/100000000:ℝ) ≤ Real.pi*Real.exp (2*(37/128:ℝ)) := by
    calc
      (560049327/100000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(37/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(37/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (37/128:ℝ) (75/256:ℝ) (560049327/100000000:ℝ) (819043127053/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0450).1
  intro u hu
  exact (show (75441357932300963/100000000000000000:ℝ) ≤ (1/4-6*(560049327/100000000:ℝ)+4*(560049327/100000000:ℝ)^2)*(819043127053/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_075 :
    ∀ u ∈ Set.Icc (75/256:ℝ) (19/64:ℝ), (23018684593509581/31250000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (56444184831/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/256:ℝ)) := by
    calc
      (56444184831/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(75/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(75/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (75/256:ℝ) (19/64:ℝ) (56444184831/10000000000:ℝ) (78510708989/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0456).1
  intro u hu
  exact (show (23018684593509581/31250000000000000:ℝ) ≤ (1/4-6*(56444184831/10000000000:ℝ)+4*(56444184831/10000000000:ℝ)^2)*(78510708989/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_076 :
    ∀ u ∈ Set.Icc (19/64:ℝ) (77/256:ℝ), (718932361707831433/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (2844344103/500000000:ℝ) ≤ Real.pi*Real.exp (2*(19/64:ℝ)) := by
    calc
      (2844344103/500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(19/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(19/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (19/64:ℝ) (77/256:ℝ) (2844344103/500000000:ℝ) (376157946017/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0462).1
  intro u hu
  exact (show (718932361707831433/1000000000000000000:ℝ) ≤ (1/4-6*(2844344103/500000000:ℝ)+4*(2844344103/500000000:ℝ)^2)*(376157946017/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_077 :
    ∀ u ∈ Set.Icc (77/256:ℝ) (39/128:ℝ), (701424832893595261/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (28666525703/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/256:ℝ)) := by
    calc
      (28666525703/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(77/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(77/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (77/256:ℝ) (39/128:ℝ) (28666525703/5000000000:ℝ) (720642046639/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0468).1
  intro u hu
  exact (show (701424832893595261/1000000000000000000:ℝ) ≤ (1/4-6*(28666525703/5000000000:ℝ)+4*(28666525703/5000000000:ℝ)^2)*(720642046639/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_078 :
    ∀ u ∈ Set.Icc (39/128:ℝ) (79/256:ℝ), (342041472533647013/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (57782720101/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/128:ℝ)) := by
    calc
      (57782720101/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(39/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(39/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (39/128:ℝ) (79/256:ℝ) (57782720101/10000000000:ℝ) (86257289297/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0474).1
  intro u hu
  exact (show (342041472533647013/500000000000000000:ℝ) ≤ (1/4-6*(57782720101/10000000000:ℝ)+4*(57782720101/10000000000:ℝ)^2)*(86257289297/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_079 :
    ∀ u ∈ Set.Icc (79/256:ℝ) (5/16:ℝ), (166728513122296977/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (58235915591/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/256:ℝ)) := by
    calc
      (58235915591/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(79/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(79/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (79/256:ℝ) (5/16:ℝ) (58235915591/10000000000:ℝ) (330268857621/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0480).1
  intro u hu
  exact (show (166728513122296977/250000000000000000:ℝ) ≤ (1/4-6*(58235915591/10000000000:ℝ)+4*(58235915591/10000000000:ℝ)^2)*(330268857621/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_080 :
    ∀ u ∈ Set.Icc (5/16:ℝ) (81/256:ℝ), (649925234224416177/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (29346332769/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/16:ℝ)) := by
    calc
      (29346332769/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(5/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(5/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (5/16:ℝ) (81/256:ℝ) (29346332769/5000000000:ℝ) (158013384979/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0486).1
  intro u hu
  exact (show (649925234224416177/1000000000000000000:ℝ) ≤ (1/4-6*(29346332769/5000000000:ℝ)+4*(29346332769/5000000000:ℝ)^2)*(158013384979/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_081 :
    ∀ u ∈ Set.Icc (81/256:ℝ) (41/128:ℝ), (126624657912986459/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (59152997819/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/256:ℝ)) := by
    calc
      (59152997819/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(81/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(81/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (81/256:ℝ) (41/128:ℝ) (59152997819/10000000000:ℝ) (302289680351/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0492).1
  intro u hu
  exact (show (126624657912986459/200000000000000000:ℝ) ≤ (1/4-6*(59152997819/10000000000:ℝ)+4*(59152997819/10000000000:ℝ)^2)*(302289680351/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_082 :
    ∀ u ∈ Set.Icc (41/128:ℝ) (83/256:ℝ), (154128683512619971/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (59616940531/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/128:ℝ)) := by
    calc
      (59616940531/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(41/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(41/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (41/128:ℝ) (83/256:ℝ) (59616940531/10000000000:ℝ) (4516320641/781250000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0498).1
  intro u hu
  exact (show (154128683512619971/250000000000000000:ℝ) ≤ (1/4-6*(59616940531/10000000000:ℝ)+4*(59616940531/10000000000:ℝ)^2)*(4516320641/781250000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_083 :
    ∀ u ∈ Set.Icc (83/256:ℝ) (21/64:ℝ), (300052897882409501/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (60084521991/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(83/256:ℝ)) := by
    calc
      (60084521991/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(83/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(83/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (83/256:ℝ) (21/64:ℝ) (60084521991/10000000000:ℝ) (2762783753/500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0504).1
  intro u hu
  exact (show (300052897882409501/500000000000000000:ℝ) ≤ (1/4-6*(60084521991/10000000000:ℝ)+4*(60084521991/10000000000:ℝ)^2)*(2762783753/500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_084 :
    ∀ u ∈ Set.Icc (21/64:ℝ) (85/256:ℝ), (291951206062636471/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (60555770737/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/64:ℝ)) := by
    calc
      (60555770737/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(21/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(21/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (21/64:ℝ) (85/256:ℝ) (60555770737/10000000000:ℝ) (16498655151/3125000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0510).1
  intro u hu
  exact (show (291951206062636471/500000000000000000:ℝ) ≤ (1/4-6*(60555770737/10000000000:ℝ)+4*(60555770737/10000000000:ℝ)^2)*(16498655151/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_085 :
    ∀ u ∈ Set.Icc (85/256:ℝ) (43/128:ℝ), (56791022721725001/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (30515357767/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/256:ℝ)) := by
    calc
      (30515357767/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(85/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(85/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (85/256:ℝ) (43/128:ℝ) (30515357767/5000000000:ℝ) (63033060527/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0516).1
  intro u hu
  exact (show (56791022721725001/100000000000000000:ℝ) ≤ (1/4-6*(30515357767/5000000000:ℝ)+4*(30515357767/5000000000:ℝ)^2)*(63033060527/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_086 :
    ∀ u ∈ Set.Icc (43/128:ℝ) (87/256:ℝ), (55213458929619209/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (7688673171/1250000000:ℝ) ≤ Real.pi*Real.exp (2*(43/128:ℝ)) := by
    calc
      (7688673171/1250000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(43/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(43/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (43/128:ℝ) (87/256:ℝ) (7688673171/1250000000:ℝ) (48145443793/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0522).1
  intro u hu
  exact (show (55213458929619209/100000000000000000:ℝ) ≤ (1/4-6*(7688673171/1250000000:ℝ)+4*(7688673171/1250000000:ℝ)^2)*(48145443793/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_087 :
    ∀ u ∈ Set.Icc (87/256:ℝ) (11/32:ℝ), (536580549127126453/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (61991809457/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/256:ℝ)) := by
    calc
      (61991809457/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(87/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(87/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (87/256:ℝ) (11/32:ℝ) (61991809457/10000000000:ℝ) (459502293119/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0528).1
  intro u hu
  exact (show (536580549127126453/1000000000000000000:ℝ) ≤ (1/4-6*(61991809457/10000000000:ℝ)+4*(61991809457/10000000000:ℝ)^2)*(459502293119/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_088 :
    ∀ u ∈ Set.Icc (11/32:ℝ) (89/256:ℝ), (521252858377755433/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (15619504311/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(11/32:ℝ)) := by
    calc
      (15619504311/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(11/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(11/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (11/32:ℝ) (89/256:ℝ) (15619504311/2500000000:ℝ) (43838386269/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0534).1
  intro u hu
  exact (show (521252858377755433/1000000000000000000:ℝ) ≤ (1/4-6*(15619504311/2500000000:ℝ)+4*(15619504311/2500000000:ℝ)^2)*(43838386269/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_089 :
    ∀ u ∈ Set.Icc (89/256:ℝ) (45/128:ℝ), (506155968807570953/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (62968038407/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/256:ℝ)) := by
    calc
      (62968038407/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(89/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(89/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (89/256:ℝ) (45/128:ℝ) (62968038407/10000000000:ℝ) (418075312637/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0540).1
  intro u hu
  exact (show (506155968807570953/1000000000000000000:ℝ) ≤ (1/4-6*(62968038407/10000000000:ℝ)+4*(62968038407/10000000000:ℝ)^2)*(418075312637/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_090 :
    ∀ u ∈ Set.Icc (45/128:ℝ) (91/256:ℝ), (245647015792921217/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (63461902853/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/128:ℝ)) := by
    calc
      (63461902853/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(45/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(45/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (45/128:ℝ) (91/256:ℝ) (63461902853/10000000000:ℝ) (49819146113/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0546).1
  intro u hu
  exact (show (245647015792921217/500000000000000000:ℝ) ≤ (1/4-6*(63461902853/10000000000:ℝ)+4*(63461902853/10000000000:ℝ)^2)*(49819146113/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_091 :
    ∀ u ∈ Set.Icc (91/256:ℝ) (23/64:ℝ), (476670897321257883/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (2558385629/400000000:ℝ) ≤ Real.pi*Real.exp (2*(91/256:ℝ)) := by
    calc
      (2558385629/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(91/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(91/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (91/256:ℝ) (23/64:ℝ) (2558385629/400000000:ℝ) (37979432379/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0552).1
  intro u hu
  exact (show (476670897321257883/1000000000000000000:ℝ) ≤ (1/4-6*(2558385629/400000000:ℝ)+4*(2558385629/400000000:ℝ)^2)*(37979432379/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_092 :
    ∀ u ∈ Set.Icc (23/64:ℝ) (93/256:ℝ), (231145058214661231/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (12892256481/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/64:ℝ)) := by
    calc
      (12892256481/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(23/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(23/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (23/64:ℝ) (93/256:ℝ) (12892256481/2000000000:ℝ) (180888020937/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0558).1
  intro u hu
  exact (show (231145058214661231/500000000000000000:ℝ) ≤ (1/4-6*(12892256481/2000000000:ℝ)+4*(12892256481/2000000000:ℝ)^2)*(180888020937/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_093 :
    ∀ u ∈ Set.Icc (93/256:ℝ) (47/128:ℝ), (224077469909545329/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (64966858509/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/256:ℝ)) := by
    calc
      (64966858509/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(93/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(93/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (93/256:ℝ) (47/128:ℝ) (64966858509/10000000000:ℝ) (86118991371/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0564).1
  intro u hu
  exact (show (224077469909545329/500000000000000000:ℝ) ≤ (1/4-6*(64966858509/10000000000:ℝ)+4*(64966858509/10000000000:ℝ)^2)*(86118991371/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_094 :
    ∀ u ∈ Set.Icc (47/128:ℝ) (95/256:ℝ), (217134160115492507/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (13095279979/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/128:ℝ)) := by
    calc
      (13095279979/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(47/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(47/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (47/128:ℝ) (95/256:ℝ) (13095279979/2000000000:ℝ) (20492007481/6250000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0570).1
  intro u hu
  exact (show (217134160115492507/500000000000000000:ℝ) ≤ (1/4-6*(13095279979/2000000000:ℝ)+4*(13095279979/2000000000:ℝ)^2)*(20492007481/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_095 :
    ∀ u ∈ Set.Icc (95/256:ℝ) (3/8:ℝ), (52579114235318267/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (128886597/19531250:ℝ) ≤ Real.pi*Real.exp (2*(95/256:ℝ)) := by
    calc
      (128886597/19531250:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(95/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(95/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (95/256:ℝ) (3/8:ℝ) (128886597/19531250:ℝ) (499108667/160000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0576).1
  intro u hu
  exact (show (52579114235318267/125000000000000000:ℝ) ≤ (1/4-6*(128886597/19531250:ℝ)+4*(128886597/19531250:ℝ)^2)*(499108667/160000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

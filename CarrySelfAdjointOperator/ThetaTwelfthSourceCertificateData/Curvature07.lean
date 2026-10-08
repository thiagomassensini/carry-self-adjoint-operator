import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_224 :
    ∀ u ∈ Set.Icc (7/16:ℝ) (225/512:ℝ), (237174929639550312532283/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7565783627557/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(225/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(225/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (7/16:ℝ) (225/512:ℝ) (7565783627557/1000000000000:ℝ) (129025901651/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0673).1
  intro u hu
  exact (show (237174929639550312532283/1000000000000000000000000:ℝ) ≤ (1/4-6*(7565783627557/1000000000000:ℝ)+4*(7565783627557/1000000000000:ℝ)^2)*(129025901651/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_225 :
    ∀ u ∈ Set.Icc (225/512:ℝ) (113/256:ℝ), (232508578518001713709071/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7595395267433/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(113/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (225/512:ℝ) (113/256:ℝ) (7595395267433/1000000000000:ℝ) (62691815501/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0678).1
  intro u hu
  exact (show (232508578518001713709071/1000000000000000000000000:ℝ) ≤ (1/4-6*(7595395267433/1000000000000:ℝ)+4*(7595395267433/1000000000000:ℝ)^2)*(62691815501/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_226 :
    ∀ u ∈ Set.Icc (113/256:ℝ) (227/512:ℝ), (45581315990209583114587/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7625122803991/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(227/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(227/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (113/256:ℝ) (227/512:ℝ) (7625122803991/1000000000000:ℝ) (24366011489/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0679).1
  intro u hu
  exact (show (45581315990209583114587/200000000000000000000000:ℝ) ≤ (1/4-6*(7625122803991/1000000000000:ℝ)+4*(7625122803991/1000000000000:ℝ)^2)*(24366011489/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_227 :
    ∀ u ∈ Set.Icc (227/512:ℝ) (57/128:ℝ), (223368662450383723085043/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7654966690837/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (227/512:ℝ) (57/128:ℝ) (7654966690837/1000000000000:ℝ) (118363425447/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0684).1
  intro u hu
  exact (show (223368662450383723085043/1000000000000000000000000:ℝ) ≤ (1/4-6*(7654966690837/1000000000000:ℝ)+4*(7654966690837/1000000000000:ℝ)^2)*(118363425447/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_228 :
    ∀ u ∈ Set.Icc (57/128:ℝ) (229/512:ℝ), (21889454228660761080593/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3842463691677/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(229/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(229/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (57/128:ℝ) (229/512:ℝ) (3842463691677/500000000000:ℝ) (57491001961/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0685).1
  intro u hu
  exact (show (21889454228660761080593/100000000000000000000000:ℝ) ≤ (1/4-6*(3842463691677/500000000000:ℝ)+4*(3842463691677/500000000000:ℝ)^2)*(57491001961/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_229 :
    ∀ u ∈ Set.Icc (229/512:ℝ) (115/256:ℝ), (107241961863557872347559/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1543001067741/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (229/512:ℝ) (115/256:ℝ) (1543001067741/200000000000:ℝ) (27921021529/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0690).1
  intro u hu
  exact (show (107241961863557872347559/500000000000000000000000:ℝ) ≤ (1/4-6*(1543001067741/200000000000:ℝ)+4*(1543001067741/200000000000:ℝ)^2)*(27921021529/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_230 :
    ∀ u ∈ Set.Icc (115/256:ℝ) (231/512:ℝ), (210136499300608906084773/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3872600507923/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(231/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(231/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (115/256:ℝ) (231/512:ℝ) (3872600507923/500000000000:ℝ) (216935979/200000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0691).1
  intro u hu
  exact (show (210136499300608906084773/1000000000000000000000000:ℝ) ≤ (1/4-6*(3872600507923/500000000000:ℝ)+4*(3872600507923/500000000000:ℝ)^2)*(216935979/200000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_231 :
    ∀ u ∈ Set.Icc (231/512:ℝ) (29/64:ℝ), (102925975026324974068149/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (311020595021/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (231/512:ℝ) (29/64:ℝ) (311020595021/40000000000:ℝ) (105332055653/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0696).1
  intro u hu
  exact (show (102925975026324974068149/500000000000000000000000:ℝ) ≤ (1/4-6*(311020595021/40000000000:ℝ)+4*(311020595021/40000000000:ℝ)^2)*(105332055653/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_232 :
    ∀ u ∈ Set.Icc (29/64:ℝ) (233/512:ℝ), (20162994579908353988699/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7805947380297/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(233/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(233/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (29/64:ℝ) (233/512:ℝ) (7805947380297/1000000000000:ℝ) (51137325069/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0697).1
  intro u hu
  exact (show (20162994579908353988699/100000000000000000000000:ℝ) ≤ (1/4-6*(7805947380297/1000000000000:ℝ)+4*(7805947380297/1000000000000:ℝ)^2)*(51137325069/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_233 :
    ∀ u ∈ Set.Icc (233/512:ℝ) (117/256:ℝ), (49367536345676385970299/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1959124748631/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(117/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(117/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (233/512:ℝ) (117/256:ℝ) (1959124748631/250000000000:ℝ) (794353299/800000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0702).1
  intro u hu
  exact (show (49367536345676385970299/250000000000000000000000:ℝ) ≤ (1/4-6*(1959124748631/250000000000:ℝ)+4*(1959124748631/250000000000:ℝ)^2)*(794353299/800000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_234 :
    ∀ u ∈ Set.Icc (117/256:ℝ) (235/512:ℝ), (96686098471378599211639/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (7867170184389/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(235/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(235/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (117/256:ℝ) (235/512:ℝ) (7867170184389/1000000000000:ℝ) (19277801103/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0703).1
  intro u hu
  exact (show (96686098471378599211639/500000000000000000000000:ℝ) ≤ (1/4-6*(7867170184389/1000000000000:ℝ)+4*(7867170184389/1000000000000:ℝ)^2)*(19277801103/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_235 :
    ∀ u ∈ Set.Icc (235/512:ℝ) (59/128:ℝ), (189335738165537923296437/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (987245177237/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (235/512:ℝ) (59/128:ℝ) (987245177237/125000000000:ℝ) (935576163/1000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0708).1
  intro u hu
  exact (show (189335738165537923296437/1000000000000000000000000:ℝ) ≤ (1/4-6*(987245177237/125000000000:ℝ)+4*(987245177237/125000000000:ℝ)^2)*(935576163/1000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_236 :
    ∀ u ∈ Set.Icc (59/128:ℝ) (237/512:ℝ), (23170049570396535778647/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1585774632977/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(237/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(237/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (59/128:ℝ) (237/512:ℝ) (1585774632977/200000000000:ℝ) (22699613733/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0709).1
  intro u hu
  exact (show (23170049570396535778647/125000000000000000000000:ℝ) ≤ (1/4-6*(1585774632977/200000000000:ℝ)+4*(1585774632977/200000000000:ℝ)^2)*(22699613733/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_237 :
    ∀ u ∈ Set.Icc (237/512:ℝ) (119/256:ℝ), (7257831589058902139443/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (795990589703/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(119/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(119/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (237/512:ℝ) (119/256:ℝ) (795990589703/100000000000:ℝ) (3524400197/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0714).1
  intro u hu
  exact (show (7257831589058902139443/40000000000000000000000:ℝ) ≤ (1/4-6*(795990589703/100000000000:ℝ)+4*(795990589703/100000000000:ℝ)^2)*(3524400197/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_238 :
    ∀ u ∈ Set.Icc (119/256:ℝ) (239/512:ℝ), (277486758742776341103/1562500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3995530043927/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(239/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(239/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (119/256:ℝ) (239/512:ℝ) (3995530043927/500000000000:ℝ) (85490772961/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0715).1
  intro u hu
  exact (show (277486758742776341103/1562500000000000000000:ℝ) ≤ (1/4-6*(3995530043927/500000000000:ℝ)+4*(3995530043927/500000000000:ℝ)^2)*(85490772961/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_239 :
    ∀ u ∈ Set.Icc (239/512:ℝ) (15/32:ℝ), (173797202727257609725889/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4011168106367/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (239/512:ℝ) (15/32:ℝ) (4011168106367/500000000000:ℝ) (82939288741/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0720).1
  intro u hu
  exact (show (173797202727257609725889/1000000000000000000000000:ℝ) ≤ (1/4-6*(4011168106367/500000000000:ℝ)+4*(4011168106367/500000000000:ℝ)^2)*(82939288741/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_240 :
    ∀ u ∈ Set.Icc (15/32:ℝ) (241/512:ℝ), (21257801320656550687273/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4026867374453/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(241/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(241/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (15/32:ℝ) (241/512:ℝ) (4026867374453/500000000000:ℝ) (314273847/390625000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0721).1
  intro u hu
  exact (show (21257801320656550687273/125000000000000000000000:ℝ) ≤ (1/4-6*(4026867374453/500000000000:ℝ)+4*(4026867374453/500000000000:ℝ)^2)*(314273847/390625000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_241 :
    ∀ u ∈ Set.Icc (241/512:ℝ) (121/256:ℝ), (166386729706384735163781/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4042628087737/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(121/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (241/512:ℝ) (121/256:ℝ) (4042628087737/500000000000:ℝ) (7803379651/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0726).1
  intro u hu
  exact (show (166386729706384735163781/1000000000000000000000000:ℝ) ≤ (1/4-6*(4042628087737/500000000000:ℝ)+4*(4042628087737/500000000000:ℝ)^2)*(7803379651/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_242 :
    ∀ u ∈ Set.Icc (121/256:ℝ) (243/512:ℝ), (162769732164439016177603/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8116900973417/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(243/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(243/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (121/256:ℝ) (243/512:ℝ) (8116900973417/1000000000000:ℝ) (75676961597/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0727).1
  intro u hu
  exact (show (162769732164439016177603/1000000000000000000000000:ℝ) ≤ (1/4-6*(8116900973417/1000000000000:ℝ)+4*(8116900973417/1000000000000:ℝ)^2)*(75676961597/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_243 :
    ∀ u ∈ Set.Icc (243/512:ℝ) (61/128:ℝ), (79605490829785045476271/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8148669625597/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (243/512:ℝ) (61/128:ℝ) (8148669625597/1000000000000:ℝ) (73382220307/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0732).1
  intro u hu
  exact (show (79605490829785045476271/500000000000000000000000:ℝ) ≤ (1/4-6*(8148669625597/1000000000000:ℝ)+4*(8148669625597/1000000000000:ℝ)^2)*(73382220307/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_244 :
    ∀ u ∈ Set.Icc (61/128:ℝ) (245/512:ℝ), (77855016929602072670317/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4090281308383/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(245/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(245/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (61/128:ℝ) (245/512:ℝ) (4090281308383/500000000000:ℝ) (35574107533/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0733).1
  intro u hu
  exact (show (77855016929602072670317/500000000000000000000000:ℝ) ≤ (1/4-6*(4090281308383/500000000000:ℝ)+4*(4090281308383/500000000000:ℝ)^2)*(35574107533/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_245 :
    ∀ u ∈ Set.Icc (245/512:ℝ) (123/256:ℝ), (152266436672900064453399/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4106290216787/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (245/512:ℝ) (123/256:ℝ) (4106290216787/500000000000:ℝ) (34486805177/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0738).1
  intro u hu
  exact (show (152266436672900064453399/1000000000000000000000000:ℝ) ≤ (1/4-6*(4106290216787/500000000000:ℝ)+4*(4106290216787/500000000000:ℝ)^2)*(34486805177/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_246 :
    ∀ u ∈ Set.Icc (123/256:ℝ) (247/512:ℝ), (9304983157038940266393/62500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8244723564573/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(247/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(247/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (123/256:ℝ) (247/512:ℝ) (8244723564573/1000000000000:ℝ) (4178568283/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0739).1
  intro u hu
  exact (show (9304983157038940266393/62500000000000000000000:ℝ) ≤ (1/4-6*(8244723564573/1000000000000:ℝ)+4*(8244723564573/1000000000000:ℝ)^2)*(4178568283/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_247 :
    ∀ u ∈ Set.Icc (247/512:ℝ) (31/64:ℝ), (2910988971182741418701/20000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (827699250023/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (247/512:ℝ) (31/64:ℝ) (827699250023/100000000000:ℝ) (12959473929/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0744).1
  intro u hu
  exact (show (2910988971182741418701/20000000000000000000000:ℝ) ≤ (1/4-6*(827699250023/100000000000:ℝ)+4*(827699250023/100000000000:ℝ)^2)*(12959473929/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_248 :
    ∀ u ∈ Set.Icc (31/64:ℝ) (249/512:ℝ), (17784389630349450598609/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (830938773293/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(249/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(249/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (31/64:ℝ) (249/512:ℝ) (830938773293/100000000000:ℝ) (62793171289/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0745).1
  intro u hu
  exact (show (17784389630349450598609/125000000000000000000000:ℝ) ≤ (1/4-6*(830938773293/100000000000:ℝ)+4*(830938773293/100000000000:ℝ)^2)*(62793171289/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_249 :
    ∀ u ∈ Set.Icc (249/512:ℝ) (125/256:ℝ), (139056255501134619079639/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4170954878493/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(125/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (249/512:ℝ) (125/256:ℝ) (4170954878493/500000000000:ℝ) (12168649677/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0750).1
  intro u hu
  exact (show (139056255501134619079639/1000000000000000000000000:ℝ) ≤ (1/4-6*(4170954878493/500000000000:ℝ)+4*(4170954878493/500000000000:ℝ)^2)*(12168649677/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_250 :
    ∀ u ∈ Set.Icc (125/256:ℝ) (251/512:ℝ), (67946188525127259059713/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4187279534323/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(251/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(251/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (125/256:ℝ) (251/512:ℝ) (4187279534323/500000000000:ℝ) (58946373017/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0751).1
  intro u hu
  exact (show (67946188525127259059713/500000000000000000000000:ℝ) ≤ (1/4-6*(4187279534323/500000000000:ℝ)+4*(4187279534323/500000000000:ℝ)^2)*(58946373017/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_251 :
    ∀ u ∈ Set.Icc (251/512:ℝ) (63/128:ℝ), (33195747165900068609343/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4203668083049/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (251/512:ℝ) (63/128:ℝ) (4203668083049/500000000000:ℝ) (57101338247/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0756).1
  intro u hu
  exact (show (33195747165900068609343/250000000000000000000000:ℝ) ≤ (1/4-6*(4203668083049/500000000000:ℝ)+4*(4203668083049/500000000000:ℝ)^2)*(57101338247/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_252 :
    ∀ u ∈ Set.Icc (63/128:ℝ) (253/512:ℝ), (64863795709352060631953/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4220120774741/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(253/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(253/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (63/128:ℝ) (253/512:ℝ) (4220120774741/500000000000:ℝ) (27653478959/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0757).1
  intro u hu
  exact (show (64863795709352060631953/500000000000000000000000:ℝ) ≤ (1/4-6*(4220120774741/500000000000:ℝ)+4*(4220120774741/500000000000:ℝ)^2)*(27653478959/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_253 :
    ∀ u ∈ Set.Icc (253/512:ℝ) (127/256:ℝ), (316814201967971705613/2500000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (132394933139/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(127/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(127/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (253/512:ℝ) (127/256:ℝ) (132394933139/15625000000:ℝ) (26781033237/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0762).1
  intro u hu
  exact (show (316814201967971705613/2500000000000000000000:ℝ) ≤ (1/4-6*(132394933139/15625000000:ℝ)+4*(132394933139/15625000000:ℝ)^2)*(26781033237/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_254 :
    ∀ u ∈ Set.Icc (127/256:ℝ) (255/512:ℝ), (24755349375981761440733/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8506439184401/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(255/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(255/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (127/256:ℝ) (255/512:ℝ) (8506439184401/1000000000000:ℝ) (51865518759/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0763).1
  intro u hu
  exact (show (24755349375981761440733/200000000000000000000000:ℝ) ≤ (1/4-6*(8506439184401/1000000000000:ℝ)+4*(8506439184401/1000000000000:ℝ)^2)*(51865518759/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_255 :
    ∀ u ∈ Set.Icc (255/512:ℝ) (1/2:ℝ), (60440137359506429916117/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (533733277877/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(1/2:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/2:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (255/512:ℝ) (1/2:ℝ) (533733277877/62500000000:ℝ) (25108094913/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0768).1
  intro u hu
  exact (show (60440137359506429916117/500000000000000000000000:ℝ) ≤ (1/4-6*(533733277877/62500000000:ℝ)+4*(533733277877/62500000000:ℝ)^2)*(25108094913/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

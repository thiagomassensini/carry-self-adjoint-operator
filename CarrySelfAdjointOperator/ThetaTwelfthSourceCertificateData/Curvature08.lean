import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_256 :
    ∀ u ∈ Set.Icc (1/2:ℝ) (257/512:ℝ), (118035744506376289043701/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1714631202761/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(257/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(257/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (1/2:ℝ) (257/512:ℝ) (1714631202761/200000000000:ℝ) (48612974743/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0769).1
  intro u hu
  exact (show (118035744506376289043701/1000000000000000000000000:ℝ) ≤ (1/4-6*(1714631202761/200000000000:ℝ)+4*(1714631202761/200000000000:ℝ)^2)*(48612974743/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_257 :
    ∀ u ∈ Set.Icc (257/512:ℝ) (129/256:ℝ), (3601332245964550280819/31250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8606710397723/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(129/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(129/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (257/512:ℝ) (129/256:ℝ) (8606710397723/1000000000000:ℝ) (47054788389/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0774).1
  intro u hu
  exact (show (3601332245964550280819/31250000000000000000000:ℝ) ≤ (1/4-6*(8606710397723/1000000000000:ℝ)+4*(8606710397723/1000000000000:ℝ)^2)*(47054788389/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_258 :
    ∀ u ∈ Set.Icc (129/256:ℝ) (259/512:ℝ), (14062551017188329061533/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8640396109787/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(259/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(259/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (129/256:ℝ) (259/512:ℝ) (8640396109787/1000000000000:ℝ) (22770282629/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0775).1
  intro u hu
  exact (show (14062551017188329061533/125000000000000000000000:ℝ) ≤ (1/4-6*(8640396109787/1000000000000:ℝ)+4*(8640396109787/1000000000000:ℝ)^2)*(22770282629/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_259 :
    ∀ u ∈ Set.Icc (259/512:ℝ) (65/128:ℝ), (21961708117872834527779/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (271069177/31250000:ℝ) ≤ Real.pi*Real.exp (2*(65/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (259/512:ℝ) (65/128:ℝ) (271069177/31250000:ℝ) (44069259259/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0780).1
  intro u hu
  exact (show (21961708117872834527779/200000000000000000000000:ℝ) ≤ (1/4-6*(271069177/31250000:ℝ)+4*(271069177/31250000:ℝ)^2)*(44069259259/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_260 :
    ∀ u ∈ Set.Icc (65/128:ℝ) (261/512:ℝ), (107166492709281556516387/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4354081788189/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(261/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(261/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (65/128:ℝ) (261/512:ℝ) (4354081788189/500000000000:ℝ) (42639843507/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0781).1
  intro u hu
  exact (show (107166492709281556516387/1000000000000000000000000:ℝ) ≤ (1/4-6*(4354081788189/500000000000:ℝ)+4*(4354081788189/500000000000:ℝ)^2)*(42639843507/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_261 :
    ∀ u ∈ Set.Icc (261/512:ℝ) (131/256:ℝ), (20914744888545789878073/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2185561591239/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(131/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(131/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (261/512:ℝ) (131/256:ℝ) (2185561591239/250000000000:ℝ) (20625655061/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0786).1
  intro u hu
  exact (show (20914744888545789878073/200000000000000000000000:ℝ) ≤ (1/4-6*(2185561591239/250000000000:ℝ)+4*(2185561591239/250000000000:ℝ)^2)*(20625655061/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_262 :
    ∀ u ∈ Set.Icc (131/256:ℝ) (263/512:ℝ), (10202969245493449972949/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8776462549797/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(263/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(263/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (131/256:ℝ) (263/512:ℝ) (8776462549797/1000000000000:ℝ) (1596106801/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0787).1
  intro u hu
  exact (show (10202969245493449972949/100000000000000000000000:ℝ) ≤ (1/4-6*(8776462549797/1000000000000:ℝ)+4*(8776462549797/1000000000000:ℝ)^2)*(1596106801/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_263 :
    ∀ u ∈ Set.Icc (263/512:ℝ) (33/64:ℝ), (99533850368687691784589/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8810812653/1000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (263/512:ℝ) (33/64:ℝ) (8810812653/1000000000:ℝ) (19296476363/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0792).1
  intro u hu
  exact (show (99533850368687691784589/1000000000000000000000000:ℝ) ≤ (1/4-6*(8810812653/1000000000:ℝ)+4*(8810812653/1000000000:ℝ)^2)*(19296476363/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_264 :
    ∀ u ∈ Set.Icc (33/64:ℝ) (265/512:ℝ), (24271412255091984402549/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (552831074919/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(265/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(265/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (33/64:ℝ) (265/512:ℝ) (552831074919/62500000000:ℝ) (37321206119/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0793).1
  intro u hu
  exact (show (24271412255091984402549/250000000000000000000000:ℝ) ≤ (1/4-6*(552831074919/62500000000:ℝ)+4*(552831074919/62500000000:ℝ)^2)*(37321206119/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_265 :
    ∀ u ∈ Set.Icc (265/512:ℝ) (133/256:ℝ), (47342268350709783552843/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1775983342621/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(133/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(133/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (265/512:ℝ) (133/256:ℝ) (1775983342621/200000000000:ℝ) (36086496271/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0798).1
  intro u hu
  exact (show (47342268350709783552843/500000000000000000000000:ℝ) ≤ (1/4-6*(1775983342621/200000000000:ℝ)+4*(1775983342621/200000000000:ℝ)^2)*(36086496271/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_266 :
    ∀ u ∈ Set.Icc (133/256:ℝ) (267/512:ℝ), (18465991880377238857269/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4457335862227/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(267/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(267/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (133/256:ℝ) (267/512:ℝ) (4457335862227/500000000000:ℝ) (8721976803/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0799).1
  intro u hu
  exact (show (18465991880377238857269/200000000000000000000000:ℝ) ≤ (1/4-6*(4457335862227/500000000000:ℝ)+4*(4457335862227/500000000000:ℝ)^2)*(8721976803/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_267 :
    ∀ u ∈ Set.Icc (267/512:ℝ) (67/128:ℝ), (11252670131103088141523/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (8949562763071/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (267/512:ℝ) (67/128:ℝ) (8949562763071/1000000000000:ℝ) (33724540723/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0804).1
  intro u hu
  exact (show (11252670131103088141523/125000000000000000000000:ℝ) ≤ (1/4-6*(8949562763071/1000000000000:ℝ)+4*(8949562763071/1000000000000:ℝ)^2)*(33724540723/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_268 :
    ∀ u ∈ Set.Icc (67/128:ℝ) (269/512:ℝ), (3510327349971007052127/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1123073795169/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(269/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(269/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (67/128:ℝ) (269/512:ℝ) (1123073795169/125000000000:ℝ) (16297758063/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0805).1
  intro u hu
  exact (show (3510327349971007052127/40000000000000000000000:ℝ) ≤ (1/4-6*(1123073795169/125000000000:ℝ)+4*(1123073795169/125000000000:ℝ)^2)*(16297758063/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_269 :
    ∀ u ∈ Set.Icc (269/512:ℝ) (135/256:ℝ), (42769934010901444689157/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9019755053777/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(135/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(135/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (269/512:ℝ) (135/256:ℝ) (9019755053777/1000000000000:ℝ) (3149997007/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0810).1
  intro u hu
  exact (show (42769934010901444689157/500000000000000000000000:ℝ) ≤ (1/4-6*(9019755053777/1000000000000:ℝ)+4*(9019755053777/1000000000000:ℝ)^2)*(3149997007/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_270 :
    ∀ u ∈ Set.Icc (135/256:ℝ) (271/512:ℝ), (41682926509208098725461/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2263764344229/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(271/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(271/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (135/256:ℝ) (271/512:ℝ) (2263764344229/250000000000:ℝ) (15218528157/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0811).1
  intro u hu
  exact (show (41682926509208098725461/500000000000000000000000:ℝ) ≤ (1/4-6*(2263764344229/250000000000:ℝ)+4*(2263764344229/250000000000:ℝ)^2)*(15218528157/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_271 :
    ∀ u ∈ Set.Icc (271/512:ℝ) (17/32:ℝ), (10154447096528143514649/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4545248934721/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (271/512:ℝ) (17/32:ℝ) (4545248934721/500000000000:ℝ) (367574319/1250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0816).1
  intro u hu
  exact (show (10154447096528143514649/125000000000000000000000:ℝ) ≤ (1/4-6*(4545248934721/500000000000:ℝ)+4*(4545248934721/500000000000:ℝ)^2)*(367574319/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_272 :
    ∀ u ∈ Set.Icc (17/32:ℝ) (273/512:ℝ), (79148476410576933329473/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9126077072133/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(273/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(273/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (17/32:ℝ) (273/512:ℝ) (9126077072133/1000000000000:ℝ) (14202912517/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0817).1
  intro u hu
  exact (show (79148476410576933329473/1000000000000000000000000:ℝ) ≤ (1/4-6*(9126077072133/1000000000000:ℝ)+4*(9126077072133/1000000000000:ℝ)^2)*(14202912517/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_273 :
    ∀ u ∈ Set.Icc (273/512:ℝ) (137/256:ℝ), (602374909194395511409/7812500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9161795527887/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(137/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(137/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (273/512:ℝ) (137/256:ℝ) (9161795527887/1000000000000:ℝ) (27435898671/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0822).1
  intro u hu
  exact (show (602374909194395511409/7812500000000000000000:ℝ) ≤ (1/4-6*(9161795527887/1000000000000:ℝ)+4*(9161795527887/1000000000000:ℝ)^2)*(27435898671/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_274 :
    ∀ u ∈ Set.Icc (137/256:ℝ) (275/512:ℝ), (37550774327671734593993/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2299413445431/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(275/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(275/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (137/256:ℝ) (275/512:ℝ) (2299413445431/250000000000:ℝ) (13247693251/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0823).1
  intro u hu
  exact (show (37550774327671734593993/500000000000000000000000:ℝ) ≤ (1/4-6*(2299413445431/250000000000:ℝ)+4*(2299413445431/250000000000:ℝ)^2)*(13247693251/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_275 :
    ∀ u ∈ Set.Icc (275/512:ℝ) (69/128:ℝ), (73140592990518585524131/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4616826190399/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(69/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (275/512:ℝ) (69/128:ℝ) (4616826190399/500000000000:ℝ) (159897029/625000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0828).1
  intro u hu
  exact (show (73140592990518585524131/1000000000000000000000000:ℝ) ≤ (1/4-6*(4616826190399/500000000000:ℝ)+4*(4616826190399/500000000000:ℝ)^2)*(159897029/625000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_276 :
    ∀ u ∈ Set.Icc (69/128:ℝ) (277/512:ℝ), (14244111417319293862651/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1853958374881/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(277/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(277/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (69/128:ℝ) (277/512:ℝ) (1853958374881/200000000000:ℝ) (1234978251/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0829).1
  intro u hu
  exact (show (14244111417319293862651/200000000000000000000000:ℝ) ≤ (1/4-6*(1853958374881/200000000000:ℝ)+4*(1853958374881/200000000000:ℝ)^2)*(1234978251/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_277 :
    ∀ u ∈ Set.Icc (277/512:ℝ) (139/256:ℝ), (69340876828747818639333/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9306072813991/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(139/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(139/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (277/512:ℝ) (139/256:ℝ) (9306072813991/1000000000000:ℝ) (5960693797/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0834).1
  intro u hu
  exact (show (69340876828747818639333/1000000000000000000000000:ℝ) ≤ (1/4-6*(9306072813991/1000000000000:ℝ)+4*(9306072813991/1000000000000:ℝ)^2)*(5960693797/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_278 :
    ∀ u ∈ Set.Icc (139/256:ℝ) (279/512:ℝ), (67500988483814460076399/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (233562393829/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(279/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(279/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (139/256:ℝ) (279/512:ℝ) (233562393829/25000000000:ℝ) (5753109521/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0835).1
  intro u hu
  exact (show (67500988483814460076399/1000000000000000000000000:ℝ) ≤ (1/4-6*(233562393829/25000000000:ℝ)+4*(233562393829/25000000000:ℝ)^2)*(5753109521/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_279 :
    ∀ u ∈ Set.Icc (279/512:ℝ) (35/64:ℝ), (16425082227878102517147/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9379061247681/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (279/512:ℝ) (35/64:ℝ) (9379061247681/1000000000000:ℝ) (2220785183/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0840).1
  intro u hu
  exact (show (16425082227878102517147/250000000000000000000000:ℝ) ≤ (1/4-6*(9379061247681/1000000000000:ℝ)+4*(9379061247681/1000000000000:ℝ)^2)*(2220785183/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_280 :
    ∀ u ∈ Set.Icc (35/64:ℝ) (281/512:ℝ), (63938335742076520490131/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4707884927751/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(281/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(281/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (35/64:ℝ) (281/512:ℝ) (4707884927751/500000000000:ℝ) (5357082377/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0841).1
  intro u hu
  exact (show (63938335742076520490131/1000000000000000000000000:ℝ) ≤ (1/4-6*(4707884927751/500000000000:ℝ)+4*(4707884927751/500000000000:ℝ)^2)*(5357082377/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_281 :
    ∀ u ∈ Set.Icc (281/512:ℝ) (141/256:ℝ), (2488577903967947656307/40000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (590788883547/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(141/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(141/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (281/512:ℝ) (141/256:ℝ) (590788883547/62500000000:ℝ) (4134639791/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0846).1
  intro u hu
  exact (show (2488577903967947656307/40000000000000000000000:ℝ) ≤ (1/4-6*(590788883547/62500000000:ℝ)+4*(590788883547/62500000000:ℝ)^2)*(4134639791/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_282 :
    ∀ u ∈ Set.Icc (141/256:ℝ) (283/512:ℝ), (12105620852408334193683/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9489618653753/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(283/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(283/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (141/256:ℝ) (283/512:ℝ) (9489618653753/1000000000000:ℝ) (19941802539/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0847).1
  intro u hu
  exact (show (12105620852408334193683/200000000000000000000000:ℝ) ≤ (1/4-6*(9489618653753/1000000000000:ℝ)+4*(9489618653753/1000000000000:ℝ)^2)*(19941802539/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_283 :
    ∀ u ∈ Set.Icc (283/512:ℝ) (71/128:ℝ), (58878746881719483552821/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9526759971027/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(71/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (283/512:ℝ) (71/128:ℝ) (9526759971027/1000000000000:ℝ) (3846699391/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0852).1
  intro u hu
  exact (show (58878746881719483552821/1000000000000000000000000:ℝ) ≤ (1/4-6*(9526759971027/1000000000000:ℝ)+4*(9526759971027/1000000000000:ℝ)^2)*(3846699391/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_284 :
    ∀ u ∈ Set.Icc (71/128:ℝ) (285/512:ℝ), (57265818141404537455609/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4782023327653/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(285/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(285/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (71/128:ℝ) (285/512:ℝ) (4782023327653/500000000000:ℝ) (4636913251/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0853).1
  intro u hu
  exact (show (57265818141404537455609/1000000000000000000000000:ℝ) ≤ (1/4-6*(4782023327653/500000000000:ℝ)+4*(4782023327653/500000000000:ℝ)^2)*(4636913251/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_285 :
    ∀ u ∈ Set.Icc (285/512:ℝ) (143/256:ℝ), (6961095306246018997793/125000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4800739637771/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(143/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(143/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (285/512:ℝ) (143/256:ℝ) (4800739637771/500000000000:ℝ) (3576731077/20000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0858).1
  intro u hu
  exact (show (6961095306246018997793/125000000000000000000000:ℝ) ≤ (1/4-6*(4800739637771/500000000000:ℝ)+4*(4800739637771/500000000000:ℝ)^2)*(3576731077/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_286 :
    ∀ u ∈ Set.Icc (143/256:ℝ) (287/512:ℝ), (54147026108292183625617/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (9639058402911/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(287/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(287/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (143/256:ℝ) (287/512:ℝ) (9639058402911/1000000000000:ℝ) (215511281/1250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0859).1
  intro u hu
  exact (show (54147026108292183625617/1000000000000000000000000:ℝ) ≤ (1/4-6*(9639058402911/1000000000000:ℝ)+4*(9639058402911/1000000000000:ℝ)^2)*(215511281/1250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_287 :
    ∀ u ∈ Set.Icc (287/512:ℝ) (9/16:ℝ), (52640057491119030578101/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (4838392305413/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (287/512:ℝ) (9/16:ℝ) (4838392305413/500000000000:ℝ) (8309403073/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0864).1
  intro u hu
  exact (show (52640057491119030578101/1000000000000000000000000:ℝ) ≤ (1/4-6*(4838392305413/500000000000:ℝ)+4*(4838392305413/500000000000:ℝ)^2)*(8309403073/50000000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

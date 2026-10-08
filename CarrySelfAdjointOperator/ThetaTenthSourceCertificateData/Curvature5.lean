import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaCurvatureQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000

theorem thetaSource_cell_curvature_160 :
    ∀ u ∈ Set.Icc (5/8:ℝ) (161/256:ℝ), (4513506200394323/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (109652334069/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/8:ℝ)) := by
    calc
      (109652334069/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(5/8:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(5/8:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (5/8:ℝ) (161/256:ℝ) (109652334069/10000000000:ℝ) (2173068377/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0966).1
  intro u hu
  exact (show (4513506200394323/250000000000000000:ℝ) ≤ (1/4-6*(109652334069/10000000000:ℝ)+4*(109652334069/10000000000:ℝ)^2)*(2173068377/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_161 :
    ∀ u ∈ Set.Icc (161/256:ℝ) (81/128:ℝ), (16869263981906327/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (110512347909/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(161/256:ℝ)) := by
    calc
      (110512347909/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(161/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(161/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (161/256:ℝ) (81/128:ℝ) (110512347909/10000000000:ℝ) (99827167/2500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0972).1
  intro u hu
  exact (show (16869263981906327/1000000000000000000:ℝ) ≤ (1/4-6*(110512347909/10000000000:ℝ)+4*(110512347909/10000000000:ℝ)^2)*(99827167/2500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_162 :
    ∀ u ∈ Set.Icc (81/128:ℝ) (163/256:ℝ), (15751367210440041/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (111379106917/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/128:ℝ)) := by
    calc
      (111379106917/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(81/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(81/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (81/128:ℝ) (163/256:ℝ) (111379106917/10000000000:ℝ) (458277847/12500000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0978).1
  intro u hu
  exact (show (15751367210440041/1000000000000000000:ℝ) ≤ (1/4-6*(111379106917/10000000000:ℝ)+4*(111379106917/10000000000:ℝ)^2)*(458277847/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_163 :
    ∀ u ∈ Set.Icc (163/256:ℝ) (41/64:ℝ), (14697319411579383/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (56126331997/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(163/256:ℝ)) := by
    calc
      (56126331997/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(163/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(163/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (163/256:ℝ) (41/64:ℝ) (56126331997/5000000000:ℝ) (67276193/2000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0984).1
  intro u hu
  exact (show (14697319411579383/1000000000000000000:ℝ) ≤ (1/4-6*(56126331997/5000000000:ℝ)+4*(56126331997/5000000000:ℝ)^2)*(67276193/2000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_164 :
    ∀ u ∈ Set.Icc (41/64:ℝ) (165/256:ℝ), (6852096667522953/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (56566536229/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/64:ℝ)) := by
    calc
      (56566536229/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(41/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(41/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (41/64:ℝ) (165/256:ℝ) (56566536229/5000000000:ℝ) (1542105519/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0990).1
  intro u hu
  exact (show (6852096667522953/500000000000000000:ℝ) ≤ (1/4-6*(56566536229/5000000000:ℝ)+4*(56566536229/5000000000:ℝ)^2)*(1542105519/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_165 :
    ∀ u ∈ Set.Icc (165/256:ℝ) (83/128:ℝ), (1276914985091137/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (22804077209/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(165/256:ℝ)) := by
    calc
      (22804077209/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(165/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(165/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (165/256:ℝ) (83/128:ℝ) (22804077209/2000000000:ℝ) (2825885259/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_0996).1
  intro u hu
  exact (show (1276914985091137/100000000000000000:ℝ) ≤ (1/4-6*(22804077209/2000000000:ℝ)+4*(22804077209/2000000000:ℝ)^2)*(2825885259/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_166 :
    ∀ u ∈ Set.Icc (83/128:ℝ) (167/256:ℝ), (5944719025535047/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (3591083091/312500000:ℝ) ≤ Real.pi*Real.exp (2*(83/128:ℝ)) := by
    calc
      (3591083091/312500000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(83/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(83/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (83/128:ℝ) (167/256:ℝ) (3591083091/312500000:ℝ) (2587380807/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1002).1
  intro u hu
  exact (show (5944719025535047/500000000000000000:ℝ) ≤ (1/4-6*(3591083091/312500000:ℝ)+4*(3591083091/312500000:ℝ)^2)*(2587380807/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_167 :
    ∀ u ∈ Set.Icc (167/256:ℝ) (21/32:ℝ), (5531197575076283/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (115815945641/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(167/256:ℝ)) := by
    calc
      (115815945641/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(167/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(167/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (167/256:ℝ) (21/32:ℝ) (115815945641/10000000000:ℝ) (2367332077/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1008).1
  intro u hu
  exact (show (5531197575076283/500000000000000000:ℝ) ≤ (1/4-6*(115815945641/10000000000:ℝ)+4*(115815945641/10000000000:ℝ)^2)*(2367332077/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_168 :
    ∀ u ∈ Set.Icc (21/32:ℝ) (169/256:ℝ), (10285446230792657/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (58362150621/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/32:ℝ)) := by
    calc
      (58362150621/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(21/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(21/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (21/32:ℝ) (169/256:ℝ) (58362150621/5000000000:ℝ) (2164455233/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1014).1
  intro u hu
  exact (show (10285446230792657/1000000000000000000:ℝ) ≤ (1/4-6*(58362150621/5000000000:ℝ)+4*(58362150621/5000000000:ℝ)^2)*(2164455233/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_169 :
    ∀ u ∈ Set.Icc (169/256:ℝ) (85/128:ℝ), (9556103793799823/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (29409945289/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(169/256:ℝ)) := by
    calc
      (29409945289/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(169/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(169/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (169/256:ℝ) (85/128:ℝ) (29409945289/2500000000:ℝ) (1977544207/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1020).1
  intro u hu
  exact (show (9556103793799823/1000000000000000000:ℝ) ≤ (1/4-6*(29409945289/2500000000:ℝ)+4*(29409945289/2500000000:ℝ)^2)*(1977544207/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_170 :
    ∀ u ∈ Set.Icc (85/128:ℝ) (171/256:ℝ), (2217991790435067/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (118562441259/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/128:ℝ)) := by
    calc
      (118562441259/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(85/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(85/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (85/128:ℝ) (171/256:ℝ) (118562441259/10000000000:ℝ) (1805466837/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1026).1
  intro u hu
  exact (show (2217991790435067/250000000000000000:ℝ) ≤ (1/4-6*(118562441259/10000000000:ℝ)+4*(118562441259/10000000000:ℝ)^2)*(1805466837/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_171 :
    ∀ u ∈ Set.Icc (171/256:ℝ) (43/64:ℝ), (65845773848071/8000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (59746168933/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(171/256:ℝ)) := by
    calc
      (59746168933/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(171/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(171/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (171/256:ℝ) (43/64:ℝ) (59746168933/5000000000:ℝ) (82358057/5000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1032).1
  intro u hu
  exact (show (65845773848071/8000000000000000:ℝ) ≤ (1/4-6*(59746168933/5000000000:ℝ)+4*(59746168933/5000000000:ℝ)^2)*(82358057/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_172 :
    ∀ u ∈ Set.Icc (43/64:ℝ) (173/256:ℝ), (7630138077098641/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (60214763867/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/64:ℝ)) := by
    calc
      (60214763867/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(43/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(43/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (43/64:ℝ) (173/256:ℝ) (60214763867/5000000000:ℝ) (750815859/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1038).1
  intro u hu
  exact (show (7630138077098641/1000000000000000000:ℝ) ≤ (1/4-6*(60214763867/5000000000:ℝ)+4*(60214763867/5000000000:ℝ)^2)*(750815859/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_173 :
    ∀ u ∈ Set.Icc (173/256:ℝ) (87/128:ℝ), (7068070913210319/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (60687034031/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(173/256:ℝ)) := by
    calc
      (60687034031/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(173/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(173/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (173/256:ℝ) (87/128:ℝ) (60687034031/5000000000:ℝ) (683973147/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1044).1
  intro u hu
  exact (show (7068070913210319/1000000000000000000:ℝ) ≤ (1/4-6*(60687034031/5000000000:ℝ)+4*(60687034031/5000000000:ℝ)^2)*(683973147/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_174 :
    ∀ u ∈ Set.Icc (87/128:ℝ) (175/256:ℝ), (1308491592392887/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (122326016501/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/128:ℝ)) := by
    calc
      (122326016501/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(87/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(87/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (87/128:ℝ) (175/256:ℝ) (122326016501/10000000000:ℝ) (622616193/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1050).1
  intro u hu
  exact (show (1308491592392887/200000000000000000:ℝ) ≤ (1/4-6*(122326016501/10000000000:ℝ)+4*(122326016501/10000000000:ℝ)^2)*(622616193/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_175 :
    ∀ u ∈ Set.Icc (175/256:ℝ) (11/16:ℝ), (6051318664087119/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (7705339447/625000000:ℝ) ≤ Real.pi*Real.exp (2*(175/256:ℝ)) := by
    calc
      (7705339447/625000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(175/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(175/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (175/256:ℝ) (11/16:ℝ) (7705339447/625000000:ℝ) (1132674101/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1056).1
  intro u hu
  exact (show (6051318664087119/1000000000000000000:ℝ) ≤ (1/4-6*(7705339447/625000000:ℝ)+4*(7705339447/625000000:ℝ)^2)*(1132674101/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_176 :
    ∀ u ∈ Set.Icc (11/16:ℝ) (177/256:ℝ), (1118550559120073/200000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (62126185287/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/16:ℝ)) := by
    calc
      (62126185287/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(11/16:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(11/16:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (11/16:ℝ) (177/256:ℝ) (62126185287/5000000000:ℝ) (1029509059/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1062).1
  intro u hu
  exact (show (1118550559120073/200000000000000000:ℝ) ≤ (1/4-6*(62126185287/5000000000:ℝ)+4*(62126185287/5000000000:ℝ)^2)*(1029509059/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_177 :
    ∀ u ∈ Set.Icc (177/256:ℝ) (89/128:ℝ), (516493902482609/100000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (125226893783/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(177/256:ℝ)) := by
    calc
      (125226893783/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(177/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(177/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (177/256:ℝ) (89/128:ℝ) (125226893783/10000000000:ℝ) (935025449/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1068).1
  intro u hu
  exact (show (516493902482609/100000000000000000:ℝ) ≤ (1/4-6*(125226893783/10000000000:ℝ)+4*(125226893783/10000000000:ℝ)^2)*(935025449/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_178 :
    ∀ u ∈ Set.Icc (89/128:ℝ) (179/256:ℝ), (4766133302660349/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (126209060259/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/128:ℝ)) := by
    calc
      (126209060259/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(89/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(89/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (89/128:ℝ) (179/256:ℝ) (126209060259/10000000000:ℝ) (848559193/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1074).1
  intro u hu
  exact (show (4766133302660349/1000000000000000000:ℝ) ≤ (1/4-6*(126209060259/10000000000:ℝ)+4*(126209060259/10000000000:ℝ)^2)*(848559193/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_179 :
    ∀ u ∈ Set.Icc (179/256:ℝ) (45/64:ℝ), (2197333628875833/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (127198929947/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(179/256:ℝ)) := by
    calc
      (127198929947/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(179/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(179/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (179/256:ℝ) (45/64:ℝ) (127198929947/10000000000:ℝ) (384745623/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1080).1
  intro u hu
  exact (show (2197333628875833/500000000000000000:ℝ) ≤ (1/4-6*(127198929947/10000000000:ℝ)+4*(127198929947/10000000000:ℝ)^2)*(384745623/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_180 :
    ∀ u ∈ Set.Icc (45/64:ℝ) (181/256:ℝ), (1012236611442963/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (25639312653/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/64:ℝ)) := by
    calc
      (25639312653/2000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(45/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(45/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (45/64:ℝ) (181/256:ℝ) (25639312653/2000000000:ℝ) (139449/20000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1086).1
  intro u hu
  exact (show (1012236611442963/250000000000000000:ℝ) ≤ (1/4-6*(25639312653/2000000000:ℝ)+4*(25639312653/2000000000:ℝ)^2)*(139449/20000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_181 :
    ∀ u ∈ Set.Icc (181/256:ℝ) (91/128:ℝ), (465931073813781/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (129202021101/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(181/256:ℝ)) := by
    calc
      (129202021101/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(181/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(181/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (181/256:ℝ) (91/128:ℝ) (129202021101/10000000000:ℝ) (631283813/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1092).1
  intro u hu
  exact (show (465931073813781/125000000000000000:ℝ) ≤ (1/4-6*(129202021101/10000000000:ℝ)+4*(129202021101/10000000000:ℝ)^2)*(631283813/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_182 :
    ∀ u ∈ Set.Icc (91/128:ℝ) (183/256:ℝ), (857180429569033/250000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (5208614593/400000000:ℝ) ≤ Real.pi*Real.exp (2*(91/128:ℝ)) := by
    calc
      (5208614593/400000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(91/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(91/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (91/128:ℝ) (183/256:ℝ) (5208614593/400000000:ℝ) (571108641/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1098).1
  intro u hu
  exact (show (857180429569033/250000000000000000:ℝ) ≤ (1/4-6*(5208614593/400000000:ℝ)+4*(5208614593/400000000:ℝ)^2)*(571108641/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_183 :
    ∀ u ∈ Set.Icc (183/256:ℝ) (23/32:ℝ), (3151382306242499/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (131236656283/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(183/256:ℝ)) := by
    calc
      (131236656283/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(183/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(183/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (183/256:ℝ) (23/32:ℝ) (131236656283/10000000000:ℝ) (51625579/10000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1104).1
  intro u hu
  exact (show (3151382306242499/1000000000000000000:ℝ) ≤ (1/4-6*(131236656283/10000000000:ℝ)+4*(131236656283/10000000000:ℝ)^2)*(51625579/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_184 :
    ∀ u ∈ Set.Icc (23/32:ℝ) (185/256:ℝ), (2894113319235649/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (132265957811/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/32:ℝ)) := by
    calc
      (132265957811/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(23/32:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(23/32:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (23/32:ℝ) (185/256:ℝ) (132265957811/10000000000:ℝ) (233147381/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1110).1
  intro u hu
  exact (show (2894113319235649/1000000000000000000:ℝ) ≤ (1/4-6*(132265957811/10000000000:ℝ)+4*(132265957811/10000000000:ℝ)^2)*(233147381/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_185 :
    ∀ u ∈ Set.Icc (185/256:ℝ) (93/128:ℝ), (2655662276511767/1000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (133303332231/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(185/256:ℝ)) := by
    calc
      (133303332231/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(185/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(185/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (185/256:ℝ) (93/128:ℝ) (133303332231/10000000000:ℝ) (84165243/20000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1116).1
  intro u hu
  exact (show (2655662276511767/1000000000000000000:ℝ) ≤ (1/4-6*(133303332231/10000000000:ℝ)+4*(133303332231/10000000000:ℝ)^2)*(84165243/20000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_186 :
    ∀ u ∈ Set.Icc (93/128:ℝ) (187/256:ℝ), (1217419628144391/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (67174421429/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/128:ℝ)) := by
    calc
      (67174421429/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(93/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(93/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (93/128:ℝ) (187/256:ℝ) (67174421429/5000000000:ℝ) (379480017/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1122).1
  intro u hu
  exact (show (1217419628144391/500000000000000000:ℝ) ≤ (1/4-6*(67174421429/5000000000:ℝ)+4*(67174421429/5000000000:ℝ)^2)*(379480017/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_187 :
    ∀ u ∈ Set.Icc (187/256:ℝ) (47/64:ℝ), (278814361538547/125000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (4231329797/312500000:ℝ) ≤ Real.pi*Real.exp (2*(187/256:ℝ)) := by
    calc
      (4231329797/312500000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(187/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(187/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (187/256:ℝ) (47/64:ℝ) (4231329797/312500000:ℝ) (341913399/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1128).1
  intro u hu
  exact (show (278814361538547/125000000000000000:ℝ) ≤ (1/4-6*(4231329797/312500000:ℝ)+4*(4231329797/312500000:ℝ)^2)*(341913399/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_188 :
    ∀ u ∈ Set.Icc (47/64:ℝ) (189/256:ℝ), (1020809179017363/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (68232264241/5000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/64:ℝ)) := by
    calc
      (68232264241/5000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(47/64:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(47/64:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (47/64:ℝ) (189/256:ℝ) (68232264241/5000000000:ℝ) (153904601/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1134).1
  intro u hu
  exact (show (1020809179017363/500000000000000000:ℝ) ≤ (1/4-6*(68232264241/5000000000:ℝ)+4*(68232264241/5000000000:ℝ)^2)*(153904601/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_189 :
    ∀ u ∈ Set.Icc (189/256:ℝ) (95/128:ℝ), (933567662673261/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (4297963519/312500000:ℝ) ≤ Real.pi*Real.exp (2*(189/256:ℝ)) := by
    calc
      (4297963519/312500000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(189/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(189/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (189/256:ℝ) (95/128:ℝ) (4297963519/312500000:ℝ) (69218553/25000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1140).1
  intro u hu
  exact (show (933567662673261/500000000000000000:ℝ) ≤ (1/4-6*(4297963519/312500000:ℝ)+4*(4297963519/312500000:ℝ)^2)*(69218553/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_190 :
    ∀ u ∈ Set.Icc (95/128:ℝ) (191/256:ℝ), (85305298899/50000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (138613531207/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/128:ℝ)) := by
    calc
      (138613531207/10000000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(95/128:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(95/128:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (95/128:ℝ) (191/256:ℝ) (138613531207/10000000000:ℝ) (248837591/100000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1146).1
  intro u hu
  exact (show (85305298899/50000000000000:ℝ) ≤ (1/4-6*(138613531207/10000000000:ℝ)+4*(138613531207/10000000000:ℝ)^2)*(248837591/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaSource_cell_curvature_191 :
    ∀ u ∈ Set.Icc (191/256:ℝ) (3/4:ℝ), (778811480076807/500000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hQ : (34925172529/2500000000:ℝ) ≤ Real.pi*Real.exp (2*(191/256:ℝ)) := by
    calc
      (34925172529/2500000000:ℝ) ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 12,
          (2*(191/256:ℝ))^i/i.factorial := by norm_num [Finset.sum_range_succ]
      _ ≤ Real.pi*Real.exp (2*(191/256:ℝ)) := by
        apply mul_le_mul (by linarith [Real.pi_gt_d6])
          (Real.sum_le_exp_of_nonneg (by norm_num) 12)
          (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_cell_lower (191/256:ℝ) (3/4:ℝ) (34925172529/2500000000:ℝ) (111724691/50000000000000:ℝ)
    (by norm_num) (by norm_num) hQ (by norm_num) (thetaFirstMode_refined_node_1152).1
  intro u hu
  exact (show (778811480076807/500000000000000000:ℝ) ≤ (1/4-6*(34925172529/2500000000:ℝ)+4*(34925172529/2500000000:ℝ)^2)*(111724691/50000000000000:ℝ) by norm_num).trans (h u hu)

end
end CarrySelfAdjointOperator

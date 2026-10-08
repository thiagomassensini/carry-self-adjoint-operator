import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
theorem thetaTwelfth_cell_curvature_160 :
    ∀ u ∈ Set.Icc (5/16:ℝ) (161/512:ℝ), (134106239829891427230371/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (589223821369/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(161/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(161/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (5/16:ℝ) (161/512:ℝ) (589223821369/100000000000:ℝ) (32308386653/5000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0481).1
  intro u hu
  exact (show (134106239829891427230371/200000000000000000000000:ℝ) ≤ (1/4-6*(589223821369/100000000000:ℝ)+4*(589223821369/100000000000:ℝ)^2)*(32308386653/5000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_161 :
    ∀ u ∈ Set.Icc (161/512:ℝ) (81/256:ℝ), (661894603755790120841153/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (2957649891007/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(81/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (161/512:ℝ) (81/256:ℝ) (2957649891007/500000000000:ℝ) (158013384979/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0486).1
  intro u hu
  exact (show (661894603755790120841153/1000000000000000000000000:ℝ) ≤ (1/4-6*(2957649891007/500000000000:ℝ)+4*(2957649891007/500000000000:ℝ)^2)*(158013384979/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_162 :
    ∀ u ∈ Set.Icc (81/256:ℝ) (163/512:ℝ), (653305882545361917059969/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1484612902691/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(163/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(163/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (81/256:ℝ) (163/512:ℝ) (1484612902691/250000000000:ℝ) (309095920617/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0487).1
  intro u hu
  exact (show (653305882545361917059969/1000000000000000000000000:ℝ) ≤ (1/4-6*(1484612902691/250000000000:ℝ)+4*(1484612902691/250000000000:ℝ)^2)*(309095920617/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_163 :
    ∀ u ∈ Set.Icc (163/512:ℝ) (41/128:ℝ), (644765869408293189826321/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5961694053209/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (163/512:ℝ) (41/128:ℝ) (5961694053209/1000000000000:ℝ) (302289680351/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0492).1
  intro u hu
  exact (show (644765869408293189826321/1000000000000000000000000:ℝ) ≤ (1/4-6*(5961694053209/1000000000000:ℝ)+4*(5961694053209/1000000000000:ℝ)^2)*(302289680351/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_164 :
    ∀ u ∈ Set.Icc (41/128:ℝ) (165/512:ℝ), (19883605626830067726437/31250000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (5985027464003/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(165/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(165/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (41/128:ℝ) (165/512:ℝ) (5985027464003/1000000000000:ℝ) (591212840587/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0493).1
  intro u hu
  exact (show (19883605626830067726437/31250000000000000000000:ℝ) ≤ (1/4-6*(5985027464003/1000000000000:ℝ)+4*(5985027464003/1000000000000:ℝ)^2)*(591212840587/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_165 :
    ∀ u ∈ Set.Icc (165/512:ℝ) (83/256:ℝ), (313917605961490248176989/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (375528262449/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(83/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(83/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (165/512:ℝ) (83/256:ℝ) (375528262449/62500000000:ℝ) (4516320641/781250000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0498).1
  intro u hu
  exact (show (313917605961490248176989/500000000000000000000000:ℝ) ≤ (1/4-6*(375528262449/62500000000:ℝ)+4*(375528262449/62500000000:ℝ)^2)*(4516320641/781250000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_166 :
    ∀ u ∈ Set.Icc (83/256:ℝ) (167/512:ℝ), (61944614403501519343567/100000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3015984308093/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(167/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(167/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (83/256:ℝ) (167/512:ℝ) (3015984308093/500000000000:ℝ) (565204745437/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0499).1
  intro u hu
  exact (show (61944614403501519343567/100000000000000000000000:ℝ) ≤ (1/4-6*(3015984308093/500000000000:ℝ)+4*(3015984308093/500000000000:ℝ)^2)*(565204745437/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_167 :
    ∀ u ∈ Set.Icc (167/512:ℝ) (21/64:ℝ), (611108936940896103336437/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3027788536921/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (167/512:ℝ) (21/64:ℝ) (3027788536921/500000000000:ℝ) (2762783753/500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0504).1
  intro u hu
  exact (show (611108936940896103336437/1000000000000000000000000:ℝ) ≤ (1/4-6*(3027788536921/500000000000:ℝ)+4*(3027788536921/500000000000:ℝ)^2)*(2762783753/500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_168 :
    ∀ u ∈ Set.Icc (21/64:ℝ) (169/512:ℝ), (301412166304549438383623/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6079277932389/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(169/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(169/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (21/64:ℝ) (169/512:ℝ) (6079277932389/1000000000000:ℝ) (540141877167/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0505).1
  intro u hu
  exact (show (301412166304549438383623/500000000000000000000000:ℝ) ≤ (1/4-6*(6079277932389/1000000000000:ℝ)+4*(6079277932389/1000000000000:ℝ)^2)*(540141877167/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_169 :
    ∀ u ∈ Set.Icc (169/512:ℝ) (85/256:ℝ), (594593054343830348494757/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3051535776737/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(85/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (169/512:ℝ) (85/256:ℝ) (3051535776737/500000000000:ℝ) (16498655151/3125000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0510).1
  intro u hu
  exact (show (594593054343830348494757/1000000000000000000000000:ℝ) ≤ (1/4-6*(3051535776737/500000000000:ℝ)+4*(3051535776737/500000000000:ℝ)^2)*(16498655151/3125000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_170 :
    ∀ u ∈ Set.Icc (85/256:ℝ) (171/512:ℝ), (586415806713032535282343/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3063479150079/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(171/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(171/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (85/256:ℝ) (171/512:ℝ) (3063479150079/500000000000:ℝ) (515998873633/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0511).1
  intro u hu
  exact (show (586415806713032535282343/1000000000000000000000000:ℝ) ≤ (1/4-6*(3063479150079/500000000000:ℝ)+4*(3063479150079/500000000000:ℝ)^2)*(515998873633/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_171 :
    ∀ u ∈ Set.Icc (171/512:ℝ) (43/128:ℝ), (9035832429292167225019/15625000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (246037541477/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (171/512:ℝ) (43/128:ℝ) (246037541477/40000000000:ℝ) (63033060527/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0516).1
  intro u hu
  exact (show (9035832429292167225019/15625000000000000000000:ℝ) ≤ (1/4-6*(246037541477/40000000000:ℝ)+4*(246037541477/40000000000:ℝ)^2)*(63033060527/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_172 :
    ∀ u ∈ Set.Icc (43/128:ℝ) (173/512:ℝ), (570226127518297911390171/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3087506314843/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(173/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(173/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (43/128:ℝ) (173/512:ℝ) (3087506314843/500000000000:ℝ) (4927506981/1000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0517).1
  intro u hu
  exact (show (570226127518297911390171/1000000000000000000000000:ℝ) ≤ (1/4-6*(3087506314843/500000000000:ℝ)+4*(3087506314843/500000000000:ℝ)^2)*(4927506981/1000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_173 :
    ∀ u ∈ Set.Icc (173/512:ℝ) (87/256:ℝ), (562215010807529520582331/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6199180945781/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(87/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (173/512:ℝ) (87/256:ℝ) (6199180945781/1000000000000:ℝ) (48145443793/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0522).1
  intro u hu
  exact (show (562215010807529520582331/1000000000000000000000000:ℝ) ≤ (1/4-6*(6199180945781/1000000000000:ℝ)+4*(6199180945781/1000000000000:ℝ)^2)*(48145443793/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_174 :
    ∀ u ∈ Set.Icc (87/256:ℝ) (175/512:ℝ), (277130277167533315632323/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (777930481749/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(175/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(175/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (87/256:ℝ) (175/512:ℝ) (777930481749/125000000000:ℝ) (18814905909/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0523).1
  intro u hu
  exact (show (277130277167533315632323/500000000000000000000000:ℝ) ≤ (1/4-6*(777930481749/125000000000:ℝ)+4*(777930481749/125000000000:ℝ)^2)*(18814905909/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_175 :
    ∀ u ∈ Set.Icc (175/512:ℝ) (11/32:ℝ), (109272673616227367408399/200000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6247801724539/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (175/512:ℝ) (11/32:ℝ) (6247801724539/1000000000000:ℝ) (459502293119/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0528).1
  intro u hu
  exact (show (109272673616227367408399/200000000000000000000000:ℝ) ≤ (1/4-6*(6247801724539/1000000000000:ℝ)+4*(6247801724539/1000000000000:ℝ)^2)*(459502293119/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_176 :
    ∀ u ∈ Set.Icc (11/32:ℝ) (177/512:ℝ), (538524042979173877513599/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6272254929097/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(177/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(177/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (11/32:ℝ) (177/512:ℝ) (6272254929097/1000000000000:ℝ) (448840361591/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0529).1
  intro u hu
  exact (show (538524042979173877513599/1000000000000000000000000:ℝ) ≤ (1/4-6*(6272254929097/1000000000000:ℝ)+4*(6272254929097/1000000000000:ℝ)^2)*(448840361591/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_177 :
    ∀ u ∈ Set.Icc (177/512:ℝ) (89/256:ℝ), (530743150886797466724179/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (787100480099/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(89/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (177/512:ℝ) (89/256:ℝ) (787100480099/125000000000:ℝ) (43838386269/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0534).1
  intro u hu
  exact (show (530743150886797466724179/1000000000000000000000000:ℝ) ≤ (1/4-6*(787100480099/125000000000:ℝ)+4*(787100480099/125000000000:ℝ)^2)*(43838386269/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_178 :
    ∀ u ∈ Set.Icc (89/256:ℝ) (179/512:ℝ), (523021244573003219654143/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (632144883421/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(179/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(179/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (89/256:ℝ) (179/512:ℝ) (632144883421/100000000000:ℝ) (214064914129/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0535).1
  intro u hu
  exact (show (523021244573003219654143/1000000000000000000000000:ℝ) ≤ (1/4-6*(632144883421/100000000000:ℝ)+4*(632144883421/100000000000:ℝ)^2)*(214064914129/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_179 :
    ∀ u ∈ Set.Icc (179/512:ℝ) (45/128:ℝ), (257679428850872338749071/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1269238057081/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (179/512:ℝ) (45/128:ℝ) (1269238057081/200000000000:ℝ) (418075312637/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0540).1
  intro u hu
  exact (show (257679428850872338749071/500000000000000000000000:ℝ) ≤ (1/4-6*(1269238057081/200000000000:ℝ)+4*(1269238057081/200000000000:ℝ)^2)*(418075312637/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_180 :
    ∀ u ∈ Set.Icc (45/128:ℝ) (181/512:ℝ), (507756504821714887282653/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (3185514285951/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(181/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(181/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (45/128:ℝ) (181/512:ℝ) (3185514285951/500000000000:ℝ) (408217392869/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0541).1
  intro u hu
  exact (show (507756504821714887282653/1000000000000000000000000:ℝ) ≤ (1/4-6*(3185514285951/500000000000:ℝ)+4*(3185514285951/500000000000:ℝ)^2)*(408217392869/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_181 :
    ∀ u ∈ Set.Icc (181/512:ℝ) (91/256:ℝ), (250107340691448839721707/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (24984234659/3906250000:ℝ) ≤ Real.pi*Real.exp (2*(91/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (181/512:ℝ) (91/256:ℝ) (24984234659/3906250000:ℝ) (49819146113/12500000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0546).1
  intro u hu
  exact (show (250107340691448839721707/500000000000000000000000:ℝ) ≤ (1/4-6*(24984234659/3906250000:ℝ)+4*(24984234659/3906250000:ℝ)^2)*(49819146113/12500000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_182 :
    ∀ u ∈ Set.Icc (91/256:ℝ) (183/512:ℝ), (492733863727986470362623/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6420997168297/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(183/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(183/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (91/256:ℝ) (183/512:ℝ) (6420997168297/1000000000000:ℝ) (15563190551/4000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0547).1
  intro u hu
  exact (show (492733863727986470362623/1000000000000000000000000:ℝ) ≤ (1/4-6*(6420997168297/1000000000000:ℝ)+4*(6420997168297/1000000000000:ℝ)^2)*(15563190551/4000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_183 :
    ∀ u ∈ Set.Icc (183/512:ℝ) (23/64:ℝ), (485314509120892510886041/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1289225648131/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (183/512:ℝ) (23/64:ℝ) (1289225648131/200000000000:ℝ) (37979432379/10000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0552).1
  intro u hu
  exact (show (485314509120892510886041/1000000000000000000000000:ℝ) ≤ (1/4-6*(1289225648131/200000000000:ℝ)+4*(1289225648131/200000000000:ℝ)^2)*(37979432379/10000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_184 :
    ∀ u ∈ Set.Icc (23/64:ℝ) (185/512:ℝ), (119489263940876827368961/250000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (25885430693/4000000000:ℝ) ≤ Real.pi*Real.exp (2*(185/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(185/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (23/64:ℝ) (185/512:ℝ) (25885430693/4000000000:ℝ) (370694018701/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0553).1
  intro u hu
  exact (show (119489263940876827368961/250000000000000000000000:ℝ) ≤ (1/4-6*(25885430693/4000000000:ℝ)+4*(25885430693/4000000000:ℝ)^2)*(370694018701/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_185 :
    ∀ u ∈ Set.Icc (185/512:ℝ) (93/256:ℝ), (235330961414012658325869/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (1624171462763/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(93/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (185/512:ℝ) (93/256:ℝ) (1624171462763/250000000000:ℝ) (180888020937/50000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0558).1
  intro u hu
  exact (show (235330961414012658325869/500000000000000000000000:ℝ) ≤ (1/4-6*(1624171462763/250000000000:ℝ)+4*(1624171462763/250000000000:ℝ)^2)*(180888020937/50000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_186 :
    ∀ u ∈ Set.Icc (93/256:ℝ) (187/512:ℝ), (463429510493183864685853/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6522113160539/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(187/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(187/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (93/256:ℝ) (187/512:ℝ) (6522113160539/1000000000000:ℝ) (22064850653/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0559).1
  intro u hu
  exact (show (463429510493183864685853/1000000000000000000000000:ℝ) ≤ (1/4-6*(6522113160539/1000000000000:ℝ)+4*(6522113160539/1000000000000:ℝ)^2)*(22064850653/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_187 :
    ∀ u ∈ Set.Icc (187/512:ℝ) (47/128:ℝ), (228130099991295207900149/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6547639989701/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (187/512:ℝ) (47/128:ℝ) (6547639989701/1000000000000:ℝ) (86118991371/25000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0564).1
  intro u hu
  exact (show (228130099991295207900149/500000000000000000000000:ℝ) ≤ (1/4-6*(6547639989701/1000000000000:ℝ)+4*(6547639989701/1000000000000:ℝ)^2)*(86118991371/25000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_188 :
    ∀ u ∈ Set.Icc (47/128:ℝ) (189/512:ℝ), (449154353626588056695189/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (410829170503/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(189/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(189/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (47/128:ℝ) (189/512:ℝ) (410829170503/62500000000:ℝ) (336088372119/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0565).1
  intro u hu
  exact (show (449154353626588056695189/1000000000000000000000000:ℝ) ≤ (1/4-6*(410829170503/62500000000:ℝ)+4*(410829170503/62500000000:ℝ)^2)*(336088372119/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_189 :
    ∀ u ∈ Set.Icc (189/512:ℝ) (95/256:ℝ), (442112314908028931533417/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (6598993766613/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(95/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (189/512:ℝ) (95/256:ℝ) (6598993766613/1000000000000:ℝ) (20492007481/6250000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0570).1
  intro u hu
  exact (show (442112314908028931533417/1000000000000000000000000:ℝ) ≤ (1/4-6*(6598993766613/1000000000000:ℝ)+4*(6598993766613/1000000000000:ℝ)^2)*(20492007481/6250000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_190 :
    ∀ u ∈ Set.Icc (95/256:ℝ) (191/512:ℝ), (217567204265768439319323/500000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (165620537449/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(191/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(191/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (95/256:ℝ) (191/512:ℝ) (165620537449/25000000000:ℝ) (319824521899/100000000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0571).1
  intro u hu
  exact (show (217567204265768439319323/500000000000000000000000:ℝ) ≤ (1/4-6*(165620537449/25000000000:ℝ)+4*(165620537449/25000000000:ℝ)^2)*(319824521899/100000000000000:ℝ) by norm_num).trans (h u hu)

theorem thetaTwelfth_cell_curvature_191 :
    ∀ u ∈ Set.Icc (191/512:ℝ) (3/8:ℝ), (428220940491343599539703/1000000000000000000000000:ℝ) ≤ thetaFirstModeSecond u := by
  have hlo : (665075031619/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have h := thetaFirstModeSecond_endpoint_cell_lower (191/512:ℝ) (3/8:ℝ) (665075031619/100000000000:ℝ) (499108667/160000000000:ℝ)
    (by norm_num) (by norm_num) hlo (by norm_num) (thetaFirstMode_refined_node_0576).1
  intro u hu
  exact (show (428220940491343599539703/1000000000000000000000000:ℝ) ≤ (1/4-6*(665075031619/100000000000:ℝ)+4*(665075031619/100000000000:ℝ)^2)*(499108667/160000000000:ℝ) by norm_num).trans (h u hu)

end CarrySelfAdjointOperator

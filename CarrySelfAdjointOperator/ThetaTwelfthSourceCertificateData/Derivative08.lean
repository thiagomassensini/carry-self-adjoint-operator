import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0256 :
    (-80197951294933113354738958311/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21/64:ℝ) ∧ thetaFirstModeFirst (21/64:ℝ) ≤ (-8019777008199979444513/125000000000000000000000:ℝ) := by
  have hlo : (3027788536921/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21/64:ℝ)) ≤ (240943806271/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21/64:ℝ)) (by norm_num : 2*(21/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21/64:ℝ)) ≤ (756947375174329703/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21/64:ℝ) (3027788536921/500000000000:ℝ) (756947375174329703/125000000000000000:ℝ) (2762783753/500000000000:ℝ) (110511563137/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0504).1 (thetaFirstMode_refined_node_0504).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0257 :
    (-196790266442989743421619161517/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (169/512:ℝ) ∧ thetaFirstModeFirst (169/512:ℝ) ≤ (-3148637124928762968861963/50000000000000000000000000:ℝ) := by
  have hlo : (6079277932389/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(169/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(169/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(169/512:ℝ)) ≤ (483773667331/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(169/512:ℝ)) (by norm_num : 2*(169/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(169/512:ℝ)) ≤ (1519819966871398283/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (169/512:ℝ) (6079277932389/1000000000000:ℝ) (1519819966871398283/250000000000000000:ℝ) (540141877167/100000000000000:ℝ) (135035730599/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0505).1 (thetaFirstMode_refined_node_0505).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0258 :
    (-786928904987340141143637617033/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19775858017267564641/59907066245820060160:ℝ) ∧ thetaFirstModeFirst (19775858017267564641/59907066245820060160:ℝ) ≤ (-78692712088077579217473/1250000000000000000000000:ℝ) := by
  have hlo : (1519913146387/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(19775858017267564641/59907066245820060160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19775858017267564641/59907066245820060160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19775858017267564641/59907066245820060160:ℝ)) ≤ (1935213925153/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19775858017267564641/59907066245820060160:ℝ)) (by norm_num : 2*(19775858017267564641/59907066245820060160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19775858017267564641/59907066245820060160:ℝ)) ≤ (6079654520763188729/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19775858017267564641/59907066245820060160:ℝ) (1519913146387/250000000000:ℝ) (6079654520763188729/1000000000000000000:ℝ) (53994786779/10000000000000:ℝ) (134987228177/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0509).1 (thetaFirstMode_refined_node_0509).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0259 :
    (-3090176921161734740166798406527/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (85/256:ℝ) ∧ thetaFirstModeFirst (85/256:ℝ) ≤ (-48283904567447691022287/781250000000000000000000:ℝ) := by
  have hlo : (3051535776737/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(85/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(85/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(85/256:ℝ)) ≤ (1942668415719/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(85/256:ℝ)) (by norm_num : 2*(85/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(85/256:ℝ)) ≤ (6103073496143900367/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (85/256:ℝ) (3051535776737/500000000000:ℝ) (6103073496143900367/1000000000000000000:ℝ) (16498655151/3125000000000:ℝ) (527957990481/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0510).1 (thetaFirstMode_refined_node_0510).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0260 :
    (-121300431353607530440148462433/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (171/512:ℝ) ∧ thetaFirstModeFirst (171/512:ℝ) ≤ (-1516251931634819162967007/25000000000000000000000000:ℝ) := by
  have hlo : (3063479150079/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(171/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(171/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(171/512:ℝ)) ≤ (1950271804919/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(171/512:ℝ)) (by norm_num : 2*(171/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(171/512:ℝ)) ≤ (6126960250430895967/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (171/512:ℝ) (3063479150079/500000000000:ℝ) (6126960250430895967/1000000000000000000:ℝ) (515998873633/100000000000000:ℝ) (20639995199/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0511).1 (thetaFirstMode_refined_node_0511).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0261 :
    (-121264719200422566392135829323/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21984457092577248159/65818805832858856960:ℝ) ∧ thetaFirstModeFirst (21984457092577248159/65818805832858856960:ℝ) ≤ (-3031611061125279411910131/50000000000000000000000000:ℝ) := by
  have hlo : (6127331476907/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(21984457092577248159/65818805832858856960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21984457092577248159/65818805832858856960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21984457092577248159/65818805832858856960:ℝ)) ≤ (1950390590793/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21984457092577248159/65818805832858856960:ℝ)) (by norm_num : 2*(21984457092577248159/65818805832858856960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21984457092577248159/65818805832858856960:ℝ)) ≤ (6127333427301153249/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21984457092577248159/65818805832858856960:ℝ) (6127331476907/1000000000000:ℝ) (6127333427301153249/1000000000000000000:ℝ) (515814204633/100000000000000:ℝ) (20632608427/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0515).1 (thetaFirstMode_refined_node_0515).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0262 :
    (-1487820270524623783224479554439/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (43/128:ℝ) ∧ thetaFirstModeFirst (43/128:ℝ) ≤ (-14878168638564013978379/250000000000000000000000:ℝ) := by
  have hlo : (246037541477/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(43/128:ℝ)) ≤ (1957904952943/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(43/128:ℝ)) (by norm_num : 2*(43/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(43/128:ℝ)) ≤ (6150940494831058199/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (43/128:ℝ) (246037541477/40000000000:ℝ) (6150940494831058199/1000000000000000000:ℝ) (63033060527/12500000000000:ℝ) (252132735761/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0516).1 (thetaFirstMode_refined_node_0516).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0263 :
    (-182472551041653090990517025511/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (173/512:ℝ) ∧ thetaFirstModeFirst (173/512:ℝ) ≤ (-14597770547645466418983/250000000000000000000000:ℝ) := by
  have hlo : (3087506314843/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(173/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(173/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(173/512:ℝ)) ≤ (245695997033/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(173/512:ℝ)) (by norm_num : 2*(173/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(173/512:ℝ)) ≤ (771876824406893569/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (173/512:ℝ) (3087506314843/500000000000:ℝ) (771876824406893569/125000000000000000:ℝ) (4927506981/1000000000000:ℝ) (246375833319/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0517).1 (thetaFirstMode_refined_node_0517).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0264 :
    (-583740538898351447989147005929/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (24409651773064480857/72234846544296732160:ℝ) ∧ thetaFirstModeFirst (24409651773064480857/72234846544296732160:ℝ) ≤ (-2918695988975457029067707/50000000000000000000000000:ℝ) := by
  have hlo : (6175384386647/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(24409651773064480857/72234846544296732160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(24409651773064480857/72234846544296732160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(24409651773064480857/72234846544296732160:ℝ)) ≤ (393137262041/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(24409651773064480857/72234846544296732160:ℝ)) (by norm_num : 2*(24409651773064480857/72234846544296732160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(24409651773064480857/72234846544296732160:ℝ)) ≤ (1235077270467171313/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (24409651773064480857/72234846544296732160:ℝ) (6175384386647/1000000000000:ℝ) (1235077270467171313/200000000000000000:ℝ) (492574961981/100000000000000:ℝ) (492575930233/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0521).1 (thetaFirstMode_refined_node_0521).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0265 :
    (-286426617038656559582589808677/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (87/256:ℝ) ∧ thetaFirstModeFirst (87/256:ℝ) ≤ (-286425956839485715987333/5000000000000000000000000:ℝ) := by
  have hlo : (6199180945781/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(87/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(87/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(87/256:ℝ)) ≤ (197326099181/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(87/256:ℝ)) (by norm_num : 2*(87/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(87/256:ℝ)) ≤ (619918291904335333/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (87/256:ℝ) (6199180945781/1000000000000:ℝ) (619918291904335333/100000000000000000:ℝ) (48145443793/10000000000000:ℝ) (481455387969/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0522).1 (thetaFirstMode_refined_node_0522).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0266 :
    (-351218887440140943527174819837/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (175/512:ℝ) ∧ thetaFirstModeFirst (175/512:ℝ) ≤ (-14048723008194226754841/250000000000000000000000:ℝ) := by
  have hlo : (777930481749/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(175/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(175/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(175/512:ℝ)) ≤ (247623014621/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(175/512:ℝ)) (by norm_num : 2*(175/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(175/512:ℝ)) ≤ (777930729372231253/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (175/512:ℝ) (777930481749/125000000000:ℝ) (777930729372231253/125000000000000000:ℝ) (18814905909/4000000000000:ℝ) (470373579529/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0523).1 (thetaFirstMode_refined_node_0523).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0267 :
    (-2808926533174888998017826497601/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5413961127233958075/15838324523948298752:ℝ) ∧ thetaFirstModeFirst (5413961127233958075/15838324523948298752:ℝ) ≤ (-702230009216556732849043/12500000000000000000000000:ℝ) := by
  have hlo : (6223814246021/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5413961127233958075/15838324523948298752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5413961127233958075/15838324523948298752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5413961127233958075/15838324523948298752:ℝ)) ≤ (1981102016437/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5413961127233958075/15838324523948298752:ℝ)) (by norm_num : 2*(5413961127233958075/15838324523948298752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5413961127233958075/15838324523948298752:ℝ)) ≤ (6223816227124364141/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5413961127233958075/15838324523948298752:ℝ) (6223814246021/1000000000000:ℝ) (6223816227124364141/1000000000000000000:ℝ) (117551363383/25000000000000:ℝ) (470206385061/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0527).1 (thetaFirstMode_refined_node_0527).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0268 :
    (-344501255115077538441379609811/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11/32:ℝ) ∧ thetaFirstModeFirst (11/32:ℝ) ≤ (-2756003646098763273147141/50000000000000000000000000:ℝ) := by
  have hlo : (6247801724539/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11/32:ℝ)) ≤ (1988737469583/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11/32:ℝ)) (by norm_num : 2*(11/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11/32:ℝ)) ≤ (6247803713279665719/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11/32:ℝ) (6247801724539/1000000000000:ℝ) (6247803713279665719/1000000000000000000:ℝ) (459502293119/100000000000000:ℝ) (57437900869/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0528).1 (thetaFirstMode_refined_node_0528).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0269 :
    (-1351518686383331805575211676629/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (177/512:ℝ) ∧ thetaFirstModeFirst (177/512:ℝ) ≤ (-2703031079969079547113327/50000000000000000000000000:ℝ) := by
  have hlo : (6272254929097/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(177/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(177/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(177/512:ℝ)) ≤ (998260583981/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(177/512:ℝ)) (by norm_num : 2*(177/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(177/512:ℝ)) ≤ (3136128462810621733/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (177/512:ℝ) (6272254929097/1000000000000:ℝ) (3136128462810621733/500000000000000000:ℝ) (448840361591/100000000000000:ℝ) (448841257713/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0529).1 (thetaFirstMode_refined_node_0529).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0270 :
    (-67556131681634168817799078999/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29984600961233742393/86727736009265052160:ℝ) ∧ thetaFirstModeFirst (29984600961233742393/86727736009265052160:ℝ) ≤ (-540447795199615643518381/10000000000000000000000000:ℝ) := by
  have hlo : (6272624009367/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(29984600961233742393/86727736009265052160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29984600961233742393/86727736009265052160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29984600961233742393/86727736009265052160:ℝ)) ≤ (399327729977/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29984600961233742393/86727736009265052160:ℝ)) (by norm_num : 2*(29984600961233742393/86727736009265052160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29984600961233742393/86727736009265052160:ℝ)) ≤ (1254525201201633361/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29984600961233742393/86727736009265052160:ℝ) (6272624009367/1000000000000:ℝ) (1254525201201633361/200000000000000000:ℝ) (89736266843/20000000000000:ℝ) (56085278759/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0533).1 (thetaFirstMode_refined_node_0533).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0271 :
    (-10603309665933449817666242951/200000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (89/256:ℝ) ∧ thetaFirstModeFirst (89/256:ℝ) ≤ (-33135265308189059360631/625000000000000000000000:ℝ) := by
  have hlo : (787100480099/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(89/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(89/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(89/256:ℝ)) ≤ (16034682647/8000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(89/256:ℝ)) (by norm_num : 2*(89/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(89/256:ℝ)) ≤ (50374446761036671/8000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (89/256:ℝ) (787100480099/125000000000:ℝ) (50374446761036671/8000000000000000:ℝ) (43838386269/10000000000000:ℝ) (219192370681/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0534).1 (thetaFirstMode_refined_node_0534).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0272 :
    (-324921804820531766113003777317/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (179/512:ℝ) ∧ thetaFirstModeFirst (179/512:ℝ) ≤ (-129968417333378080755309/2500000000000000000000000:ℝ) := by
  have hlo : (632144883421/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(179/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(179/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(179/512:ℝ)) ≤ (2012180077557/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(179/512:ℝ)) (by norm_num : 2*(179/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(179/512:ℝ)) ≤ (6321450846392528301/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (179/512:ℝ) (632144883421/100000000000:ℝ) (6321450846392528301/1000000000000000000:ℝ) (214064914129/50000000000000:ℝ) (53516336217/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0535).1 (thetaFirstMode_refined_node_0535).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0273 :
    (-2598613728867339888637141347023/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (33175116720304347591/94884058348837864960:ℝ) ∧ thetaFirstModeFirst (33175116720304347591/94884058348837864960:ℝ) ≤ (-51972152769140600757603/1000000000000000000000000:ℝ) := by
  have hlo : (1264363330857/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(33175116720304347591/94884058348837864960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33175116720304347591/94884058348837864960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(33175116720304347591/94884058348837864960:ℝ)) ≤ (2012297158347/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(33175116720304347591/94884058348837864960:ℝ)) (by norm_num : 2*(33175116720304347591/94884058348837864960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(33175116720304347591/94884058348837864960:ℝ)) ≤ (6321818666582826771/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (33175116720304347591/94884058348837864960:ℝ) (1264363330857/200000000000:ℝ) (6321818666582826771/1000000000000000000:ℝ) (42797860779/10000000000000:ℝ) (427979469013/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0539).1 (thetaFirstMode_refined_node_0539).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0274 :
    (-101946906098692603922936527419/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (45/128:ℝ) ∧ thetaFirstModeFirst (45/128:ℝ) ≤ (-509733331893067526632597/10000000000000000000000000:ℝ) := by
  have hlo : (1269238057081/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(45/128:ℝ)) ≤ (2020055527709/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(45/128:ℝ)) (by norm_num : 2*(45/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(45/128:ℝ)) ≤ (6346192305461900437/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (45/128:ℝ) (1269238057081/200000000000:ℝ) (6346192305461900437/1000000000000000000:ℝ) (418075312637/100000000000000:ℝ) (16723046287/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0540).1 (thetaFirstMode_refined_node_0540).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0275 :
    (-624679055115561130843210849823/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (181/512:ℝ) ∧ thetaFirstModeFirst (181/512:ℝ) ≤ (-1249355162649246374283419/25000000000000000000000000:ℝ) := by
  have hlo : (3185514285951/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(181/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(181/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(181/512:ℝ)) ≤ (1013980900751/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(181/512:ℝ)) (by norm_num : 2*(181/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(181/512:ℝ)) ≤ (3185515299933036343/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (181/512:ℝ) (3185514285951/500000000000:ℝ) (3185515299933036343/500000000000000000:ℝ) (408217392869/100000000000000:ℝ) (204109110361/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0541).1 (thetaFirstMode_refined_node_0541).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0276 :
    (-499597174110084443344472835261/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (36663910216296708609/103703836492258332160:ℝ) ∧ thetaFirstModeFirst (36663910216296708609/103703836492258332160:ℝ) ≤ (-624494994206708968724769/12500000000000000000000000:ℝ) := by
  have hlo : (1592848795453/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(36663910216296708609/103703836492258332160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(36663910216296708609/103703836492258332160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(36663910216296708609/103703836492258332160:ℝ)) ≤ (405615699417/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(36663910216296708609/103703836492258332160:ℝ)) (by norm_num : 2*(36663910216296708609/103703836492258332160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(36663910216296708609/103703836492258332160:ℝ)) ≤ (1274279441978551281/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (36663910216296708609/103703836492258332160:ℝ) (1592848795453/250000000000:ℝ) (1274279441978551281/200000000000000000:ℝ) (408073633973/100000000000000:ℝ) (408074461581/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0545).1 (thetaFirstMode_refined_node_0545).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0277 :
    (-97979970220078608528250909399/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (91/256:ℝ) ∧ thetaFirstModeFirst (91/256:ℝ) ≤ (-1196041727122223167967/24414062500000000000000:ℝ) := by
  have hlo : (24984234659/3906250000:ℝ) ≤ Real.pi*Real.exp (2*(91/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(91/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(91/256:ℝ)) ≤ (81435960783/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(91/256:ℝ)) (by norm_num : 2*(91/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(91/256:ℝ)) ≤ (255838644344147319/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (91/256:ℝ) (24984234659/3906250000:ℝ) (255838644344147319/40000000000000000:ℝ) (49819146113/12500000000000:ℝ) (398553980321/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0546).1 (thetaFirstMode_refined_node_0546).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0278 :
    (-240101582308881632415218958353/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (183/512:ℝ) ∧ thetaFirstModeFirst (183/512:ℝ) ≤ (-96040404819887627161647/2000000000000000000000000:ℝ) := by
  have hlo : (6420997168297/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(183/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(183/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(183/512:ℝ)) ≤ (1021933651521/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(183/512:ℝ)) (by norm_num : 2*(183/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(183/512:ℝ)) ≤ (3210499606082812953/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (183/512:ℝ) (6420997168297/1000000000000:ℝ) (3210499606082812953/500000000000000000:ℝ) (15563190551/4000000000000:ℝ) (77816111801/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0547).1 (thetaFirstMode_refined_node_0547).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0279 :
    (-192025186013557212285758283/4000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (40475102494972215807/113232801681326748160:ℝ) ∧ thetaFirstModeFirst (40475102494972215807/113232801681326748160:ℝ) ≤ (-1200154561979317638390003/25000000000000000000000000:ℝ) := by
  have hlo : (3210681308301/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(40475102494972215807/113232801681326748160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(40475102494972215807/113232801681326748160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(40475102494972215807/113232801681326748160:ℝ)) ≤ (16351869031/8000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(40475102494972215807/113232801681326748160:ℝ)) (by norm_num : 2*(40475102494972215807/113232801681326748160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(40475102494972215807/113232801681326748160:ℝ)) ≤ (51370917284706383/8000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (40475102494972215807/113232801681326748160:ℝ) (3210681308301/500000000000:ℝ) (51370917284706383/8000000000000000:ℝ) (388943135103/100000000000000:ℝ) (3889439301/1000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0551).1 (thetaFirstMode_refined_node_0551).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0280 :
    (-147078746446992774982606184319/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23/64:ℝ) ∧ thetaFirstModeFirst (23/64:ℝ) ≤ (-47065086705513762233649/1000000000000000000000000:ℝ) := by
  have hlo : (1289225648131/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23/64:ℝ)) ≤ (128241673343/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23/64:ℝ)) (by norm_num : 2*(23/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23/64:ℝ)) ≤ (402883143282655399/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23/64:ℝ) (1289225648131/200000000000:ℝ) (402883143282655399/62500000000000000:ℝ) (37979432379/10000000000000:ℝ) (379795103081/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0552).1 (thetaFirstMode_refined_node_0552).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0281 :
    (-288278198983127306280577915107/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (185/512:ℝ) ∧ thetaFirstModeFirst (185/512:ℝ) ≤ (-9224880310693381389793/200000000000000000000000:ℝ) := by
  have hlo : (25885430693/4000000000:ℝ) ≤ Real.pi*Real.exp (2*(185/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(185/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(185/512:ℝ)) ≤ (2059897552977/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(185/512:ℝ)) (by norm_num : 2*(185/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(185/512:ℝ)) ≤ (6471359733149672361/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (185/512:ℝ) (25885430693/4000000000:ℝ) (6471359733149672361/1000000000000000000:ℝ) (370694018701/100000000000000:ℝ) (46336847787/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0553).1 (thetaFirstMode_refined_node_0553).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0282 :
    (-2305552965535923343311592752203/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8926893532018987965/24703856487388477952:ℝ) ∧ thetaFirstModeFirst (8926893532018987965/24703856487388477952:ℝ) ≤ (-288193431586335823622259/6250000000000000000000000:ℝ) := by
  have hlo : (808965250889/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(8926893532018987965/24703856487388477952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8926893532018987965/24703856487388477952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8926893532018987965/24703856487388477952:ℝ)) ≤ (2060013524071/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8926893532018987965/24703856487388477952:ℝ)) (by norm_num : 2*(8926893532018987965/24703856487388477952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8926893532018987965/24703856487388477952:ℝ)) ≤ (6471724067126785103/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8926893532018987965/24703856487388477952:ℝ) (808965250889/125000000000:ℝ) (6471724067126785103/1000000000000000000:ℝ) (370564202331/100000000000000:ℝ) (370564965701/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0557).1 (thetaFirstMode_refined_node_0557).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0283 :
    (-28248833794583401980344666087/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (93/256:ℝ) ∧ thetaFirstModeFirst (93/256:ℝ) ≤ (-282487660252988959868931/6250000000000000000000000:ℝ) := by
  have hlo : (1624171462763/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(93/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(93/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(93/256:ℝ)) ≤ (129247485253/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(93/256:ℝ)) (by norm_num : 2*(93/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(93/256:ℝ)) ≤ (406042994938428029/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (93/256:ℝ) (1624171462763/250000000000:ℝ) (406042994938428029/62500000000000000:ℝ) (180888020937/50000000000000:ℝ) (72355358003/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0558).1 (thetaFirstMode_refined_node_0558).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0284 :
    (-442859434516823248338594953/10000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (187/512:ℝ) ∧ thetaFirstModeFirst (187/512:ℝ) ≤ (-138393240166008847981967/3125000000000000000000000:ℝ) := by
  have hlo : (6522113160539/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(187/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(187/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(187/512:ℝ)) ≤ (51901338243/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(187/512:ℝ)) (by norm_num : 2*(187/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(187/512:ℝ)) ≤ (163052880914841099/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (187/512:ℝ) (6522113160539/1000000000000:ℝ) (163052880914841099/25000000000000000:ℝ) (22064850653/6250000000000:ℝ) (2824306747/800000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0559).1 (thetaFirstMode_refined_node_0559).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0285 :
    (-276706495516334150202936321061/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (49169526224045867343/134614321254731292160:ℝ) ∧ thetaFirstModeFirst (49169526224045867343/134614321254731292160:ℝ) ≤ (-4323528584959858033287/97656250000000000000000:ℝ) := by
  have hlo : (407654776611/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(49169526224045867343/134614321254731292160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49169526224045867343/134614321254731292160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(49169526224045867343/134614321254731292160:ℝ)) ≤ (2076169160661/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(49169526224045867343/134614321254731292160:ℝ)) (by norm_num : 2*(49169526224045867343/134614321254731292160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(49169526224045867343/134614321254731292160:ℝ)) ≤ (6522478501948472973/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (49169526224045867343/134614321254731292160:ℝ) (407654776611/62500000000:ℝ) (6522478501948472973/1000000000000000000:ℝ) (11028571917/3125000000000:ℝ) (44114379257/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0563).1 (thetaFirstMode_refined_node_0563).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0286 :
    (-271173856885532170522390272867/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (47/128:ℝ) ∧ thetaFirstModeFirst (47/128:ℝ) ≤ (-542346403930724947870071/12500000000000000000000000:ℝ) := by
  have hlo : (6547639989701/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(47/128:ℝ)) ≤ (260522371687/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(47/128:ℝ)) (by norm_num : 2*(47/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(47/128:ℝ)) ≤ (818455259235277391/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (47/128:ℝ) (6547639989701/1000000000000:ℝ) (818455259235277391/125000000000000000:ℝ) (86118991371/25000000000000:ℝ) (344476683437/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0564).1 (thetaFirstMode_refined_node_0564).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0287 :
    (-3320596204562212025842998499/78125000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (189/512:ℝ) ∧ thetaFirstModeFirst (189/512:ℝ) ≤ (-132823526318992987405857/3125000000000000000000000:ℝ) := by
  have hlo : (410829170503/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(189/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(189/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(189/512:ℝ)) ≤ (13077101371/6250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(189/512:ℝ)) (by norm_num : 2*(189/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(189/512:ℝ)) ≤ (41082930127424003/6250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (189/512:ℝ) (410829170503/62500000000:ℝ) (41082930127424003/6250000000000000:ℝ) (336088372119/100000000000000:ℝ) (84022268833/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0565).1 (thetaFirstMode_refined_node_0565).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

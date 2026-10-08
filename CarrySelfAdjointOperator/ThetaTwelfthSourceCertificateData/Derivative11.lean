import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0352 :
    (-99085021786989147418756438851/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29/64:ℝ) ∧ thetaFirstModeFirst (29/64:ℝ) ≤ (-31707118067451146703713/2000000000000000000000000:ℝ) := by
  have hlo : (311020595021/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29/64:ℝ)) ≤ (618755942491/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29/64:ℝ)) (by norm_num : 2*(29/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29/64:ℝ)) ≤ (1943879337638128163/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29/64:ℝ) (311020595021/40000000000:ℝ) (1943879337638128163/250000000000000000:ℝ) (105332055653/100000000000000:ℝ) (52666158177/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0696).1 (thetaFirstMode_refined_node_0696).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0353 :
    (-772784049059890815219294595531/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (233/512:ℝ) ∧ thetaFirstModeFirst (233/512:ℝ) ≤ (-386390937390506654765493/25000000000000000000000000:ℝ) := by
  have hlo : (7805947380297/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(233/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(233/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(233/512:ℝ)) ≤ (2484710739109/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(233/512:ℝ)) (by norm_num : 2*(233/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(233/512:ℝ)) ≤ (7805949865009660637/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (233/512:ℝ) (7805947380297/1000000000000:ℝ) (7805949865009660637/1000000000000000000:ℝ) (51137325069/50000000000000:ℝ) (102274904263/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0697).1 (thetaFirstMode_refined_node_0697).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0354 :
    (-193139685293226991086776294873/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (355853979535385553057/781923988453504668160:ℝ) ∧ thetaFirstModeFirst (355853979535385553057/781923988453504668160:ℝ) ≤ (-193139141861666295847827/12500000000000000000000000:ℝ) := by
  have hlo : (7806296333437/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(355853979535385553057/781923988453504668160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(355853979535385553057/781923988453504668160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(355853979535385553057/781923988453504668160:ℝ)) ≤ (1242410907183/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(355853979535385553057/781923988453504668160:ℝ)) (by norm_num : 2*(355853979535385553057/781923988453504668160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(355853979535385553057/781923988453504668160:ℝ)) ≤ (3903149409129762519/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (355853979535385553057/781923988453504668160:ℝ) (7806296333437/1000000000000:ℝ) (3903149409129762519/500000000000000000:ℝ) (25560027471/25000000000000:ℝ) (51120181967/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0701).1 (thetaFirstMode_refined_node_0701).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0355 :
    (-1883242974414735225476845621/125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (117/256:ℝ) ∧ thetaFirstModeFirst (117/256:ℝ) ≤ (-1506590126040080583669/100000000000000000000000:ℝ) := by
  have hlo : (1959124748631/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(117/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(117/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(117/256:ℝ)) ≤ (124721781099/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(117/256:ℝ)) (by norm_num : 2*(117/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(117/256:ℝ)) ≤ (391825074448150707/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (117/256:ℝ) (1959124748631/250000000000:ℝ) (391825074448150707/50000000000000000:ℝ) (794353299/800000000000:ℝ) (4964720503/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0702).1 (thetaFirstMode_refined_node_0702).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0356 :
    (-367106769453579146375883192167/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (235/512:ℝ) ∧ thetaFirstModeFirst (235/512:ℝ) ≤ (-146842291782352977581067/10000000000000000000000000:ℝ) := by
  have hlo : (7867170184389/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(235/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(235/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(235/512:ℝ)) ≤ (1252099283483/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(235/512:ℝ)) (by norm_num : 2*(235/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(235/512:ℝ)) ≤ (3933586344295208419/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (235/512:ℝ) (7867170184389/1000000000000:ℝ) (3933586344295208419/500000000000000000:ℝ) (19277801103/20000000000000:ℝ) (96389246893/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0703).1 (thetaFirstMode_refined_node_0703).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0357 :
    (-366999648611183604840449837287/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (76861289619680304915/167451405549299389952:ℝ) ∧ thetaFirstModeFirst (76861289619680304915/167451405549299389952:ℝ) ≤ (-183499304436740517354021/12500000000000000000000000:ℝ) := by
  have hlo : (1966879720447/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(76861289619680304915/167451405549299389952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(76861289619680304915/167451405549299389952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(76861289619680304915/167451405549299389952:ℝ)) ≤ (1252154780409/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(76861289619680304915/167451405549299389952:ℝ)) (by norm_num : 2*(76861289619680304915/167451405549299389952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(76861289619680304915/167451405549299389952:ℝ)) ≤ (3933760693049451537/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (76861289619680304915/167451405549299389952:ℝ) (1966879720447/250000000000:ℝ) (3933760693049451537/500000000000000000:ℝ) (96356468443/100000000000000:ℝ) (96356709751/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0707).1 (thetaFirstMode_refined_node_0707).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0358 :
    (-178881768465942041020652479551/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (59/128:ℝ) ∧ thetaFirstModeFirst (59/128:ℝ) ≤ (-894406299765897401631/62500000000000000000000:ℝ) := by
  have hlo : (987245177237/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(59/128:ℝ)) ≤ (1256999861519/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(59/128:ℝ)) (by norm_num : 2*(59/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(59/128:ℝ)) ≤ (3948981965949059767/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (59/128:ℝ) (987245177237/125000000000:ℝ) (3948981965949059767/500000000000000000:ℝ) (935576163/1000000000000:ℝ) (46778925753/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0708).1 (thetaFirstMode_refined_node_0708).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0359 :
    (-139446361573100835431622325917/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (237/512:ℝ) ∧ thetaFirstModeFirst (237/512:ℝ) ≤ (-34861490949517743873141/2500000000000000000000000:ℝ) := by
  have hlo : (1585774632977/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(237/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(237/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(237/512:ℝ)) ≤ (2523839239751/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(237/512:ℝ)) (by norm_num : 2*(237/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(237/512:ℝ)) ≤ (7928875688727063343/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (237/512:ℝ) (1585774632977/200000000000:ℝ) (7928875688727063343/1000000000000000000:ℝ) (22699613733/25000000000000:ℝ) (18159736819/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0709).1 (thetaFirstMode_refined_node_0709).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0360 :
    (-10891065241194907652113405457/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (414763412687601229593/895986442171253532160:ℝ) ∧ thetaFirstModeFirst (414763412687601229593/895986442171253532160:ℝ) ≤ (-348513093535516366266033/25000000000000000000000000:ℝ) := by
  have hlo : (3964610815979/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(414763412687601229593/895986442171253532160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(414763412687601229593/895986442171253532160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(414763412687601229593/895986442171253532160:ℝ)) ≤ (78873442509/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(414763412687601229593/895986442171253532160:ℝ)) (by norm_num : 2*(414763412687601229593/895986442171253532160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(414763412687601229593/895986442171253532160:ℝ)) ≤ (247788254872176837/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (414763412687601229593/895986442171253532160:ℝ) (3964610815979/500000000000:ℝ) (247788254872176837/31250000000000000:ℝ) (90767817427/100000000000000:ℝ) (45384023261/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0713).1 (thetaFirstMode_refined_node_0713).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0361 :
    (-169830447754646471233032881257/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (119/256:ℝ) ∧ thetaFirstModeFirst (119/256:ℝ) ≤ (-2717279386234399371491/200000000000000000000000:ℝ) := by
  have hlo : (795990589703/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(119/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(119/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(119/256:ℝ)) ≤ (2533717267243/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(119/256:ℝ)) (by norm_num : 2*(119/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(119/256:ℝ)) ≤ (7959908430749738099/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (119/256:ℝ) (795990589703/100000000000:ℝ) (7959908430749738099/1000000000000000000:ℝ) (3524400197/4000000000000:ℝ) (22027557043/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0714).1 (thetaFirstMode_refined_node_0714).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0362 :
    (-33089555563462440880467863673/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (239/512:ℝ) ∧ thetaFirstModeFirst (239/512:ℝ) ≤ (-330894605224092513857847/25000000000000000000000000:ℝ) := by
  have hlo : (3995530043927/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(239/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(239/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(239/512:ℝ)) ≤ (2543633956241/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(239/512:ℝ)) (by norm_num : 2*(239/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(239/512:ℝ)) ≤ (7991062631489031913/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (239/512:ℝ) (3995530043927/500000000000:ℝ) (7991062631489031913/1000000000000000000:ℝ) (85490772961/100000000000000:ℝ) (4274549521/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0715).1 (thetaFirstMode_refined_node_0715).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0363 :
    (-330798822964787710104386273439/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (447347369053687618791/958289379521344821760:ℝ) ∧ thetaFirstModeFirst (447347369053687618791/958289379521344821760:ℝ) ≤ (-330797872795963279861077/25000000000000000000000000:ℝ) := by
  have hlo : (3995704174771/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(447347369053687618791/958289379521344821760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(447347369053687618791/958289379521344821760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(447347369053687618791/958289379521344821760:ℝ)) ≤ (2543744811403/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(447347369053687618791/958289379521344821760:ℝ)) (by norm_num : 2*(447347369053687618791/958289379521344821760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(447347369053687618791/958289379521344821760:ℝ)) ≤ (7991410893289984979/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (447347369053687618791/958289379521344821760:ℝ) (3995704174771/500000000000:ℝ) (7991410893289984979/1000000000000000000:ℝ) (85461936087/100000000000000:ℝ) (42731076741/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0719).1 (thetaFirstMode_refined_node_0719).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0364 :
    (-80579236909443204678527524553/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15/32:ℝ) ∧ thetaFirstModeFirst (15/32:ℝ) ≤ (-322316018670037813513947/25000000000000000000000000:ℝ) := by
  have hlo : (4011168106367/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15/32:ℝ)) ≤ (2553589458063/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15/32:ℝ)) (by norm_num : 2*(15/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15/32:ℝ)) ≤ (8022338766324514359/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15/32:ℝ) (4011168106367/500000000000:ℝ) (8022338766324514359/1000000000000000000:ℝ) (82939288741/100000000000000:ℝ) (10367437567/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0720).1 (thetaFirstMode_refined_node_0720).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0365 :
    (-78480538669635575434538009727/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (241/512:ℝ) ∧ thetaFirstModeFirst (241/512:ℝ) ≤ (-1226254870253133830691/97656250000000000000000:ℝ) := by
  have hlo : (4026867374453/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(241/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(241/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(241/512:ℝ)) ≤ (1281791962309/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(241/512:ℝ)) (by norm_num : 2*(241/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(241/512:ℝ)) ≤ (4026868656246218237/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (241/512:ℝ) (4026867374453/500000000000:ℝ) (4026868656246218237/500000000000000000:ℝ) (314273847/390625000000:ℝ) (20113577771/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0721).1 (thetaFirstMode_refined_node_0721).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0366 :
    (-78457572921199105839656228361/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (482187174233040082809/1024350621420112591360:ℝ) ∧ thetaFirstModeFirst (482187174233040082809/1024350621420112591360:ℝ) ≤ (-125531753609407464727221/10000000000000000000000000:ℝ) := by
  have hlo : (8054082829691/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(482187174233040082809/1024350621420112591360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(482187174233040082809/1024350621420112591360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(482187174233040082809/1024350621420112591360:ℝ)) ≤ (640923680549/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(482187174233040082809/1024350621420112591360:ℝ)) (by norm_num : 2*(482187174233040082809/1024350621420112591360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(482187174233040082809/1024350621420112591360:ℝ)) ≤ (2013521348346974557/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (482187174233040082809/1024350621420112591360:ℝ) (8054082829691/1000000000000:ℝ) (2013521348346974557/250000000000000000:ℝ) (16085394831/20000000000000:ℝ) (40213590173/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0725).1 (thetaFirstMode_refined_node_0725).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0367 :
    (-3821353502405362147008368181/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (121/256:ℝ) ∧ thetaFirstModeFirst (121/256:ℝ) ≤ (-30570739300032948439787/2500000000000000000000000:ℝ) := by
  have hlo : (4042628087737/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(121/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(121/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(121/256:ℝ)) ≤ (321702188551/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(121/256:ℝ)) (by norm_num : 2*(121/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(121/256:ℝ)) ≤ (1010657343636501743/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (121/256:ℝ) (4042628087737/500000000000:ℝ) (1010657343636501743/125000000000000000:ℝ) (7803379651/10000000000000:ℝ) (3901699867/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0726).1 (thetaFirstMode_refined_node_0726).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0368 :
    (-595344896578677248613812117/50000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (243/512:ℝ) ∧ thetaFirstModeFirst (243/512:ℝ) ≤ (-595343162852680226866949/50000000000000000000000000:ℝ) := by
  have hlo : (8116900973417/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(243/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(243/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(243/512:ℝ)) ≤ (322961295317/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(243/512:ℝ)) (by norm_num : 2*(243/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(243/512:ℝ)) ≤ (1014612944638819981/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (243/512:ℝ) (8116900973417/1000000000000:ℝ) (1014612944638819981/125000000000000000:ℝ) (75676961597/100000000000000:ℝ) (605417257/800000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0727).1 (thetaFirstMode_refined_node_0727).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0369 :
    (-2975852481562964065820771911/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (519418319492085968007/1094362844259452700160:ℝ) ∧ thetaFirstModeFirst (519418319492085968007/1094362844259452700160:ℝ) ≤ (-1859902384476763441421/156250000000000000000000:ℝ) := by
  have hlo : (126832014021/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(519418319492085968007/1094362844259452700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(519418319492085968007/1094362844259452700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(519418319492085968007/1094362844259452700160:ℝ)) ≤ (322975138773/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(519418319492085968007/1094362844259452700160:ℝ)) (by norm_num : 2*(519418319492085968007/1094362844259452700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(519418319492085968007/1094362844259452700160:ℝ)) ≤ (1014656435143285389/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (519418319492085968007/1094362844259452700160:ℝ) (126832014021/15625000000:ℝ) (1014656435143285389/125000000000000000:ℝ) (15130289401/20000000000000:ℝ) (3026065699/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0731).1 (thetaFirstMode_refined_node_0731).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0370 :
    (-579623608370171277095778169029/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (61/128:ℝ) ∧ thetaFirstModeFirst (61/128:ℝ) ≤ (-579621914597768260398279/50000000000000000000000000:ℝ) := by
  have hlo : (8148669625597/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(61/128:ℝ)) ≤ (2593802640699/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(61/128:ℝ)) (by norm_num : 2*(61/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(61/128:ℝ)) ≤ (8148672219401493507/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (61/128:ℝ) (8148669625597/1000000000000:ℝ) (8148672219401493507/1000000000000000000:ℝ) (73382220307/100000000000000:ℝ) (73382410647/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0732).1 (thetaFirstMode_refined_node_0732).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0371 :
    (-705308786498535932497251533/62500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (245/512:ℝ) ∧ thetaFirstModeFirst (245/512:ℝ) ≤ (-141061343663011776349139/12500000000000000000000000:ℝ) := by
  have hlo : (4090281308383/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(245/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(245/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(245/512:ℝ)) ≤ (6509886243/2500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(245/512:ℝ)) (by norm_num : 2*(245/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(245/512:ℝ)) ≤ (20451413051805099/2500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (245/512:ℝ) (4090281308383/500000000000:ℝ) (20451413051805099/2500000000000000:ℝ) (35574107533/50000000000000:ℝ) (35574200167/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0733).1 (thetaFirstMode_refined_node_0733).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0372 :
    (-35255097177004543258948341059/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (111836642512315217805/233705377354370135552:ℝ) ∧ thetaFirstModeFirst (111836642512315217805/233705377354370135552:ℝ) ≤ (-141019975175890018926827/12500000000000000000000000:ℝ) := by
  have hlo : (4090455203727/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(111836642512315217805/233705377354370135552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(111836642512315217805/233705377354370135552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(111836642512315217805/233705377354370135552:ℝ)) ≤ (1302032601219/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(111836642512315217805/233705377354370135552:ℝ)) (by norm_num : 2*(111836642512315217805/233705377354370135552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(111836642512315217805/233705377354370135552:ℝ)) ≤ (4090456505761401867/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (111836642512315217805/233705377354370135552:ℝ) (4090455203727/500000000000:ℝ) (4090456505761401867/500000000000000000:ℝ) (35562115301/50000000000000:ℝ) (8890551977/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0737).1 (thetaFirstMode_refined_node_0737).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0373 :
    (-8581399004098045042086090411/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (123/256:ℝ) ∧ thetaFirstModeFirst (123/256:ℝ) ≤ (-137301980059429363906299/12500000000000000000000000:ℝ) := by
  have hlo : (4106290216787/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(123/256:ℝ)) ≤ (81692065217/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(123/256:ℝ)) (by norm_num : 2*(123/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(123/256:ℝ)) ≤ (256643220241270681/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (123/256:ℝ) (4106290216787/500000000000:ℝ) (256643220241270681/31250000000000000:ℝ) (34486805177/50000000000000:ℝ) (34486895331/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0738).1 (thetaFirstMode_refined_node_0738).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0374 :
    (-534505551297502589509204312913/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (247/512:ℝ) ∧ thetaFirstModeFirst (247/512:ℝ) ≤ (-33406498318277440238159/3125000000000000000000000:ℝ) := by
  have hlo : (8244723564573/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(247/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(247/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(247/512:ℝ)) ≤ (2624377565443/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(247/512:ℝ)) (by norm_num : 2*(247/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(247/512:ℝ)) ≤ (8244726188952770699/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (247/512:ℝ) (8244723564573/1000000000000:ℝ) (8244726188952770699/1000000000000000000:ℝ) (4178568283/6250000000000:ℝ) (66857267987/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0739).1 (thetaFirstMode_refined_node_0739).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0375 :
    (-534348616500886473995341410837/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (601631469395921364543/1247052024347146908160:ℝ) ∧ thetaFirstModeFirst (601631469395921364543/1247052024347146908160:ℝ) ≤ (-534347038694252317593899/50000000000000000000000000:ℝ) := by
  have hlo : (8245071245231/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(601631469395921364543/1247052024347146908160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(601631469395921364543/1247052024347146908160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(601631469395921364543/1247052024347146908160:ℝ)) ≤ (2624488235657/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(601631469395921364543/1247052024347146908160:ℝ)) (by norm_num : 2*(601631469395921364543/1247052024347146908160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(601631469395921364543/1247052024347146908160:ℝ)) ≤ (8245073869722381601/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (601631469395921364543/1247052024347146908160:ℝ) (8245071245231/1000000000000:ℝ) (8245073869722381601/1000000000000000000:ℝ) (66834556229/100000000000000:ℝ) (66834731637/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0743).1 (thetaFirstMode_refined_node_0743).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0376 :
    (-6501619265776154069913746739/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (31/64:ℝ) ∧ thetaFirstModeFirst (31/64:ℝ) ≤ (-10402560003500921150367/1000000000000000000000000:ℝ) := by
  have hlo : (827699250023/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(31/64:ℝ)) ≤ (164665568051/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(31/64:ℝ)) (by norm_num : 2*(31/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(31/64:ℝ)) ≤ (517312195930045243/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (31/64:ℝ) (827699250023/100000000000:ℝ) (517312195930045243/62500000000000000:ℝ) (12959473929/20000000000000:ℝ) (12959508073/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0744).1 (thetaFirstMode_refined_node_0744).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0377 :
    (-3162975119024393128182640991/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (249/512:ℝ) ∧ thetaFirstModeFirst (249/512:ℝ) ≤ (-50607451439833887584677/5000000000000000000000000:ℝ) := by
  have hlo : (830938773293/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(249/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(249/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(249/512:ℝ)) ≤ (528992162759/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(249/512:ℝ)) (by norm_num : 2*(249/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(249/512:ℝ)) ≤ (1661878075578535087/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (249/512:ℝ) (830938773293/100000000000:ℝ) (1661878075578535087/200000000000000000:ℝ) (62793171289/100000000000000:ℝ) (1962291793/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0745).1 (thetaFirstMode_refined_node_0745).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0378 :
    (-252963625329233178543728596101/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (646920215696683136241/1330156250206437122560:ℝ) ∧ thetaFirstModeFirst (646920215696683136241/1330156250206437122560:ℝ) ≤ (-3952544893743230185101/390625000000000000000000:ℝ) := by
  have hlo : (2077433831593/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(646920215696683136241/1330156250206437122560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(646920215696683136241/1330156250206437122560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(646920215696683136241/1330156250206437122560:ℝ)) ≤ (2645071456247/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(646920215696683136241/1330156250206437122560:ℝ)) (by norm_num : 2*(646920215696683136241/1330156250206437122560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(646920215696683136241/1330156250206437122560:ℝ)) ≤ (8309737971445381471/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (646920215696683136241/1330156250206437122560:ℝ) (2077433831593/250000000000:ℝ) (8309737971445381471/1000000000000000000:ℝ) (1961625157/3125000000000:ℝ) (31386085531/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0749).1 (thetaFirstMode_refined_node_0749).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0379 :
    (-2461697720663337879859799991/250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (125/256:ℝ) ∧ thetaFirstModeFirst (125/256:ℝ) ≤ (-49233807525330418696761/5000000000000000000000000:ℝ) := by
  have hlo : (4170954878493/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(125/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(125/256:ℝ)) ≤ (106212515909/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(125/256:ℝ)) (by norm_num : 2*(125/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(125/256:ℝ)) ≤ (333676496492103037/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (125/256:ℝ) (4170954878493/500000000000:ℝ) (333676496492103037/40000000000000000:ℝ) (12168649677/20000000000000:ℝ) (7605426243/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0750).1 (thetaFirstMode_refined_node_0750).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0380 :
    (-11972868081146076014367939621/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (251/512:ℝ) ∧ thetaFirstModeFirst (251/512:ℝ) ≤ (-239456644729528612562491/25000000000000000000000000:ℝ) := by
  have hlo : (4187279534323/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(251/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(251/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(251/512:ℝ)) ≤ (533141099713/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(251/512:ℝ)) (by norm_num : 2*(251/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(251/512:ℝ)) ≤ (1674912346870662809/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (251/512:ℝ) (4187279534323/500000000000:ℝ) (1674912346870662809/200000000000000000:ℝ) (58946373017/100000000000000:ℝ) (7368316269/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0751).1 (thetaFirstMode_refined_node_0751).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0381 :
    (-2992336006242376887270835629/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (695214398443277823759/1418066563546442882560:ℝ) ∧ thetaFirstModeFirst (695214398443277823759/1418066563546442882560:ℝ) ≤ (-7480817618527453762497/781250000000000000000000:ℝ) := by
  have hlo : (8374906597303/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(695214398443277823759/1418066563546442882560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(695214398443277823759/1418066563546442882560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(695214398443277823759/1418066563546442882560:ℝ)) ≤ (533163224079/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(695214398443277823759/1418066563546442882560:ℝ)) (by norm_num : 2*(695214398443277823759/1418066563546442882560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(695214398443277823759/1418066563546442882560:ℝ)) ≤ (1674981852624017847/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (695214398443277823759/1418066563546442882560:ℝ) (8374906597303/1000000000000:ℝ) (1674981852624017847/200000000000000000:ℝ) (920726599/1562500000000:ℝ) (1841458107/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0755).1 (thetaFirstMode_refined_node_0755).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0382 :
    (-93159242193065396254763328273/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (63/128:ℝ) ∧ thetaFirstModeFirst (63/128:ℝ) ≤ (-232897405807424036075103/25000000000000000000000000:ℝ) := by
  have hlo : (4203668083049/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(63/128:ℝ)) ≤ (535227754979/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(63/128:ℝ)) (by norm_num : 2*(63/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(63/128:ℝ)) ≤ (1681467768447741547/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (63/128:ℝ) (4203668083049/500000000000:ℝ) (1681467768447741547/200000000000000000:ℝ) (57101338247/100000000000000:ℝ) (57101491059/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0756).1 (thetaFirstMode_refined_node_0756).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0383 :
    (-56622338786545262525053560127/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (253/512:ℝ) ∧ thetaFirstModeFirst (253/512:ℝ) ≤ (-113244336178864022174619/12500000000000000000000000:ℝ) := by
  have hlo : (4220120774741/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(253/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(253/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(253/512:ℝ)) ≤ (1343306442957/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(253/512:ℝ)) (by norm_num : 2*(253/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(253/512:ℝ)) ≤ (4220122118048610501/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (253/512:ℝ) (4220120774741/500000000000:ℝ) (4220122118048610501/500000000000000000:ℝ) (27653478959/50000000000000:ℝ) (13826776627/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0757).1 (thetaFirstMode_refined_node_0757).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

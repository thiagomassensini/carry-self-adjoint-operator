import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0192 :
    (-411131979016656269324453890137/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (262135666824211125/1073524536622218752:ℝ) ∧ thetaFirstModeFirst (262135666824211125/1073524536622218752:ℝ) ≤ (-164452468571670529416231/1250000000000000000000000:ℝ) := by
  have hlo : (1023938351651/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(262135666824211125/1073524536622218752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(262135666824211125/1073524536622218752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(262135666824211125/1073524536622218752:ℝ)) ≤ (814824419953/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(262135666824211125/1073524536622218752:ℝ)) (by norm_num : 2*(262135666824211125/1073524536622218752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(262135666824211125/1073524536622218752:ℝ)) ≤ (2559846693953405129/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (262135666824211125/1073524536622218752:ℝ) (1023938351651/200000000000:ℝ) (2559846693953405129/500000000000000000:ℝ) (168853057581/12500000000000:ℝ) (168853332753/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0377).1 (thetaFirstMode_refined_node_0377).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0193 :
    (-324127034919971467866762425939/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (63/256:ℝ) ∧ thetaFirstModeFirst (63/256:ℝ) ≤ (-810315990586240067100897/6250000000000000000000000:ℝ) := by
  have hlo : (2569650756461/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(63/256:ℝ)) ≤ (81794540999/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(63/256:ℝ)) (by norm_num : 2*(63/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(63/256:ℝ)) ≤ (256965157440671407/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (63/256:ℝ) (2569650756461/500000000000:ℝ) (256965157440671407/50000000000000000:ℝ) (331464929477/25000000000000:ℝ) (1325861886877/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0378).1 (thetaFirstMode_refined_node_0378).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0194 :
    (-638582057154040962139753363073/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (127/512:ℝ) ∧ thetaFirstModeFirst (127/512:ℝ) ≤ (-9977824918679670288629/78125000000000000000000:ℝ) := by
  have hlo : (64492702129/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(127/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(127/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(127/512:ℝ)) ≤ (1642293515619/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(127/512:ℝ)) (by norm_num : 2*(127/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(127/512:ℝ)) ≤ (5159417812614041067/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (127/512:ℝ) (64492702129/12500000000:ℝ) (5159417812614041067/1000000000000000000:ℝ) (162590818501/12500000000000:ℝ) (130072868419/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0379).1 (thetaFirstMode_refined_node_0379).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0195 :
    (-159595011340944729628889603367/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1511920914525505143/6094295942728092160:ℝ) ∧ thetaFirstModeFirst (1511920914525505143/6094295942728092160:ℝ) ≤ (-6383787833195289128957/50000000000000000000000:ℝ) := by
  have hlo : (10319678467/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(1511920914525505143/6094295942728092160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1511920914525505143/6094295942728092160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1511920914525505143/6094295942728092160:ℝ)) ≤ (41060704521/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1511920914525505143/6094295942728092160:ℝ)) (by norm_num : 2*(1511920914525505143/6094295942728092160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1511920914525505143/6094295942728092160:ℝ)) ≤ (128996021898241953/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1511920914525505143/6094295942728092160:ℝ) (10319678467/2000000000:ℝ) (128996021898241953/25000000000000000:ℝ) (650101513471/50000000000000:ℝ) (1300205162439/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0383).1 (thetaFirstMode_refined_node_0383).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0196 :
    (-6290043168594789650918400158041/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/4:ℝ) ∧ thetaFirstModeFirst (1/4:ℝ) ≤ (-786253836790838077020779/6250000000000000000000000:ℝ) := by
  have hlo : (5179609554261/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/4:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/4:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/4:ℝ)) ≤ (1648721270701/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/4:ℝ)) (by norm_num : 2*(1/4:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/4:ℝ)) ≤ (5179611202985366693/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/4:ℝ) (5179609554261/1000000000000:ℝ) (5179611202985366693/1000000000000000000:ℝ) (159496168639/12500000000000:ℝ) (1275971452837/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0384).1 (thetaFirstMode_refined_node_0384).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0197 :
    (-193600237031668827588235485681/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (129/512:ℝ) ∧ thetaFirstModeFirst (129/512:ℝ) ≤ (-774399407407011937221351/6250000000000000000000000:ℝ) := by
  have hlo : (649985246609/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(129/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(129/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(129/512:ℝ)) ≤ (206896772913/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(129/512:ℝ)) (by norm_num : 2*(129/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(129/512:ℝ)) ≤ (649985453506070409/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (129/512:ℝ) (649985246609/125000000000:ℝ) (649985453506070409/125000000000000000:ℝ) (1251584440439/100000000000000:ℝ) (312896628009/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0385).1 (thetaFirstMode_refined_node_0385).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0198 :
    (-387078605595862628952036844953/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1740175468704392841/6905636680726120960:ℝ) ∧ thetaFirstModeFirst (1740175468704392841/6905636680726120960:ℝ) ≤ (-6048091178553644012403/48828125000000000000000:ℝ) := by
  have hlo : (20313678701/3906250000:ℝ) ≤ Real.pi*Real.exp (2*(1740175468704392841/6905636680726120960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1740175468704392841/6905636680726120960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1740175468704392841/6905636680726120960:ℝ)) ≤ (413826950433/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1740175468704392841/6905636680726120960:ℝ)) (by norm_num : 2*(1740175468704392841/6905636680726120960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1740175468704392841/6905636680726120960:ℝ)) ≤ (1300075850691659769/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1740175468704392841/6905636680726120960:ℝ) (20313678701/3906250000:ℝ) (1300075850691659769/250000000000000000:ℝ) (312771103803/25000000000000:ℝ) (312771621537/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0389).1 (thetaFirstMode_refined_node_0389).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0199 :
    (-6101312784872935521420468329769/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (65/256:ℝ) ∧ thetaFirstModeFirst (65/256:ℝ) ≤ (-3050650303401237859983369/25000000000000000000000000:ℝ) := by
  have hlo : (2610116867743/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(65/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(65/256:ℝ)) ≤ (1661652351893/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(65/256:ℝ)) (by norm_num : 2*(65/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(65/256:ℝ)) ≤ (5220235397140585549/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (65/256:ℝ) (2610116867743/500000000000:ℝ) (5220235397140585549/1000000000000000000:ℝ) (1227568144983/100000000000000:ℝ) (1227570184781/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0390).1 (thetaFirstMode_refined_node_0390).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0200 :
    (-751044700249779844203326573857/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (131/512:ℝ) ∧ thetaFirstModeFirst (131/512:ℝ) ≤ (-187760799086849630326783/1562500000000000000000000:ℝ) := by
  have hlo : (5240665152647/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(131/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(131/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(131/512:ℝ)) ≤ (1668155875317/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(131/512:ℝ)) (by norm_num : 2*(131/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(131/512:ℝ)) ≤ (5240666820804759981/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (131/512:ℝ) (5240665152647/1000000000000:ℝ) (5240666820804759981/1000000000000000000:ℝ) (37622399689/3125000000000:ℝ) (150489849797/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0391).1 (thetaFirstMode_refined_node_0391).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0201 :
    (-187702365522042567234998070069/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1998562918031146359/7809963970327836160:ℝ) ∧ thetaFirstModeFirst (1998562918031146359/7809963970327836160:ℝ) ≤ (-3003231834235158878550561/25000000000000000000000000:ℝ) := by
  have hlo : (5241081764163/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1998562918031146359/7809963970327836160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1998562918031146359/7809963970327836160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1998562918031146359/7809963970327836160:ℝ)) ≤ (1668288486909/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1998562918031146359/7809963970327836160:ℝ)) (by norm_num : 2*(1998562918031146359/7809963970327836160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1998562918031146359/7809963970327836160:ℝ)) ≤ (5241083432453906037/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1998562918031146359/7809963970327836160:ℝ) (5241081764163/1000000000000:ℝ) (5241083432453906037/1000000000000000000:ℝ) (601719622347/50000000000000:ℝ) (37607539137/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0395).1 (thetaFirstMode_refined_node_0395).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0202 :
    (-11555353009681443998870998779/97656250000000000000000000000:ℝ) ≤ thetaFirstModeFirst (33/128:ℝ) ∧ thetaFirstModeFirst (33/128:ℝ) ≤ (-92442638371191464679169/781250000000000000000000:ℝ) := by
  have hlo : (2630588268057/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(33/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(33/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(33/128:ℝ)) ≤ (418671213203/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(33/128:ℝ)) (by norm_num : 2*(33/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(33/128:ℝ)) ≤ (1315294552700052379/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (33/128:ℝ) (2630588268057/500000000000:ℝ) (1315294552700052379/250000000000000000:ℝ) (36894584617/3125000000000:ℝ) (9223661601/781250000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0396).1 (thetaFirstMode_refined_node_0396).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0203 :
    (-2912630389094638186603361177691/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (133/512:ℝ) ∧ thetaFirstModeFirst (133/512:ℝ) ≤ (-291262451907453407747717/2500000000000000000000000:ℝ) := by
  have hlo : (2640884099433/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(133/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(133/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(133/512:ℝ)) ≤ (1681239384003/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(133/512:ℝ)) (by norm_num : 2*(133/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(133/512:ℝ)) ≤ (5281769880108136779/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (133/512:ℝ) (2640884099433/500000000000:ℝ) (5281769880108136779/1000000000000000000:ℝ) (115769423549/10000000000000:ℝ) (578848090929/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0397).1 (thetaFirstMode_refined_node_0397).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0204 :
    (-5823444710741132072874374521599/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2290508312768691057/8816267219187228160:ℝ) ∧ thetaFirstModeFirst (2290508312768691057/8816267219187228160:ℝ) ≤ (-2911716486801997414415837/25000000000000000000000000:ℝ) := by
  have hlo : (5282181767379/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(2290508312768691057/8816267219187228160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2290508312768691057/8816267219187228160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2290508312768691057/8816267219187228160:ℝ)) ≤ (1681371026977/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2290508312768691057/8816267219187228160:ℝ)) (by norm_num : 2*(2290508312768691057/8816267219187228160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2290508312768691057/8816267219187228160:ℝ)) ≤ (5282183448753754361/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2290508312768691057/8816267219187228160:ℝ) (5282181767379/1000000000000:ℝ) (5282183448753754361/1000000000000000000:ℝ) (578619100303/50000000000000:ℝ) (1157240146359/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0401).1 (thetaFirstMode_refined_node_0401).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0205 :
    (-2867558081554541786663992677321/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (67/256:ℝ) ∧ thetaFirstModeFirst (67/256:ℝ) ≤ (-2867552283691761039588927/25000000000000000000000000:ℝ) := by
  have hlo : (5302440455107/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(67/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(67/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(67/256:ℝ)) ≤ (1687819568903/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(67/256:ℝ)) (by norm_num : 2*(67/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(67/256:ℝ)) ≤ (5302442142928682479/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (67/256:ℝ) (5302440455107/1000000000000:ℝ) (5302442142928682479/1000000000000000000:ℝ) (567557858261/50000000000000:ℝ) (567558816199/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0402).1 (thetaFirstMode_refined_node_0402).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0206 :
    (-5645905219235091767224082484393/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (135/512:ℝ) ∧ thetaFirstModeFirst (135/512:ℝ) ≤ (-22054272527138244735391/195312500000000000000000:ℝ) := by
  have hlo : (332699601267/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(135/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(135/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(135/512:ℝ)) ≤ (1694425507919/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(135/512:ℝ)) (by norm_num : 2*(135/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(135/512:ℝ)) ≤ (5323195314699774967/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (135/512:ℝ) (332699601267/62500000000:ℝ) (5323195314699774967/1000000000000000000:ℝ) (69555468773/6250000000000:ℝ) (1112889386079/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0403).1 (thetaFirstMode_refined_node_0403).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0207 :
    (-1411038228199264502842671683349/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (523953028089808515/1986849740868925952:ℝ) ∧ thetaFirstModeFirst (523953028089808515/1986849740868925952:ℝ) ≤ (-1128828292666363501183439/10000000000000000000000000:ℝ) := by
  have hlo : (5323604260713/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(523953028089808515/1986849740868925952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(523953028089808515/1986849740868925952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(523953028089808515/1986849740868925952:ℝ)) ≤ (847278109429/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(523953028089808515/1986849740868925952:ℝ)) (by norm_num : 2*(523953028089808515/1986849740868925952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(523953028089808515/1986849740868925952:ℝ)) ≤ (2661802977635380397/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (523953028089808515/1986849740868925952:ℝ) (5323604260713/1000000000000:ℝ) (2661802977635380397/500000000000000000:ℝ) (222490410103/20000000000000:ℝ) (556226967817/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0407).1 (thetaFirstMode_refined_node_0407).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0208 :
    (-5557626145381755970245768281739/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17/64:ℝ) ∧ thetaFirstModeFirst (17/64:ℝ) ≤ (-694701854457959945919003/6250000000000000000000000:ℝ) := by
  have hlo : (1336007002757/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17/64:ℝ)) ≤ (1701057301849/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17/64:ℝ)) (by norm_num : 2*(17/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17/64:ℝ)) ≤ (5344029712087705457/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17/64:ℝ) (1336007002757/250000000000:ℝ) (5344029712087705457/1000000000000000000:ℝ) (545502971679/50000000000000:ℝ) (1091007799227/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0408).1 (thetaFirstMode_refined_node_0408).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0209 :
    (-1094055403371933855142299780199/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (137/512:ℝ) ∧ thetaFirstModeFirst (137/512:ℝ) ≤ (-1367566462204701759016853/12500000000000000000000000:ℝ) := by
  have hlo : (1341235986321/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(137/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(137/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(137/512:ℝ)) ≤ (1707715051887/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(137/512:ℝ)) (by norm_num : 2*(137/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(137/512:ℝ)) ≤ (5364945653002835991/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (137/512:ℝ) (1341235986321/250000000000:ℝ) (5364945653002835991/1000000000000000000:ℝ) (1069467409093/100000000000000:ℝ) (213893847089/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0409).1 (thetaFirstMode_refined_node_0409).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0210 :
    (-683573308254643201407023355147/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (2990441164477942593/11174368100215452160:ℝ) ∧ thetaFirstModeFirst (2990441164477942593/11174368100215452160:ℝ) ≤ (-683571912593624779619967/6250000000000000000000000:ℝ) := by
  have hlo : (1341337941937/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(2990441164477942593/11174368100215452160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(2990441164477942593/11174368100215452160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(2990441164477942593/11174368100215452160:ℝ)) ≤ (426961216459/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(2990441164477942593/11174368100215452160:ℝ)) (by norm_num : 2*(2990441164477942593/11174368100215452160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(2990441164477942593/11174368100215452160:ℝ)) ≤ (1341338368899079187/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (2990441164477942593/11174368100215452160:ℝ) (1341337941937/250000000000:ℝ) (1341338368899079187/250000000000000000:ℝ) (534525830191/50000000000000:ℝ) (534526743081/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0413).1 (thetaFirstMode_refined_node_0413).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0211 :
    (-336490986669274645970258816143/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (69/256:ℝ) ∧ thetaFirstModeFirst (69/256:ℝ) ≤ (-16824514873325923753489/156250000000000000000000:ℝ) := by
  have hlo : (336621358887/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(69/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(69/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(69/256:ℝ)) ≤ (1714398859621/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(69/256:ℝ)) (by norm_num : 2*(69/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(69/256:ℝ)) ≤ (5385943456593316253/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (69/256:ℝ) (336621358887/62500000000:ℝ) (5385943456593316253/1000000000000000000:ℝ) (52413413447/5000000000000:ℝ) (65516879131/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0414).1 (thetaFirstMode_refined_node_0414).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0212 :
    (-5298360286931796539870249530917/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (139/512:ℝ) ∧ thetaFirstModeFirst (139/512:ℝ) ≤ (-264917469979422112138173/2500000000000000000000000:ℝ) := by
  have hlo : (2703510861077/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(139/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(139/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(139/512:ℝ)) ≤ (1721108827039/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(139/512:ℝ)) (by norm_num : 2*(139/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(139/512:ℝ)) ≤ (5407023443263933127/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (139/512:ℝ) (2703510861077/500000000000:ℝ) (5407023443263933127/1000000000000000000:ℝ) (102740490249/10000000000000:ℝ) (1027406670771/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0415).1 (thetaFirstMode_refined_node_0415).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0213 :
    (-662091194259221679603307025511/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3407025864107161791/12547889060924853760:ℝ) ∧ thetaFirstModeFirst (3407025864107161791/12547889060924853760:ℝ) ≤ (-132417966735040643460139/1250000000000000000000000:ℝ) := by
  have hlo : (270371341609/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(3407025864107161791/12547889060924853760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3407025864107161791/12547889060924853760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3407025864107161791/12547889060924853760:ℝ)) ≤ (215154722199/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3407025864107161791/12547889060924853760:ℝ)) (by norm_num : 2*(3407025864107161791/12547889060924853760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3407025864107161791/12547889060924853760:ℝ)) ≤ (675928569177323007/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3407025864107161791/12547889060924853760:ℝ) (270371341609/50000000000:ℝ) (675928569177323007/125000000000000000:ℝ) (513504005171/50000000000000:ℝ) (1027009778073/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0419).1 (thetaFirstMode_refined_node_0419).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0214 :
    (-81465441090581769886994481929/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (35/128:ℝ) ∧ thetaFirstModeFirst (35/128:ℝ) ≤ (-52137774814374992202957/500000000000000000000000:ℝ) := by
  have hlo : (217127368273/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(35/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(35/128:ℝ)) ≤ (107990316033/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(35/128:ℝ)) (by norm_num : 2*(35/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(35/128:ℝ)) ≤ (339261620917060569/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (35/128:ℝ) (217127368273/40000000000:ℝ) (339261620917060569/62500000000000000:ℝ) (251718424509/25000000000000:ℝ) (251718859441/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0420).1 (thetaFirstMode_refined_node_0420).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0215 :
    (-40079196946666626712249870397/390625000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (141/512:ℝ) ∧ thetaFirstModeFirst (141/512:ℝ) ≤ (-641265824862226378281017/6250000000000000000000000:ℝ) := by
  have hlo : (2724714759559/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(141/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(141/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(141/512:ℝ)) ≤ (1734607650873/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(141/512:ℝ)) (by norm_num : 2*(141/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(141/512:ℝ)) ≤ (5449431253729060689/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (141/512:ℝ) (2724714759559/500000000000:ℝ) (5449431253729060689/1000000000000000000:ℝ) (246667763263/25000000000000:ℝ) (7708380973/781250000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0421).1 (thetaFirstMode_refined_node_0421).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0216 :
    (-320535276306616594541771228153/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3874419549088930809/14066927919229519360:ℝ) ∧ thetaFirstModeFirst (3874419549088930809/14066927919229519360:ℝ) ≤ (-5128553813230458887425931/50000000000000000000000000:ℝ) := by
  have hlo : (5449832017949/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3874419549088930809/14066927919229519360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3874419549088930809/14066927919229519360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3874419549088930809/14066927919229519360:ℝ)) ≤ (108420985641/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3874419549088930809/14066927919229519360:ℝ)) (by norm_num : 2*(3874419549088930809/14066927919229519360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3874419549088930809/14066927919229519360:ℝ)) ≤ (340614609542866113/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3874419549088930809/14066927919229519360:ℝ) (5449832017949/1000000000000:ℝ) (340614609542866113/62500000000000000:ℝ) (986292210119/100000000000000:ℝ) (986293921081/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0425).1 (thetaFirstMode_refined_node_0425).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0217 :
    (-315462793863830427786706968441/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (71/256:ℝ) ∧ thetaFirstModeFirst (71/256:ℝ) ≤ (-5047394228701346886136551/50000000000000000000000000:ℝ) := by
  have hlo : (5470757983213/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(71/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(71/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(71/256:ℝ)) ≤ (108837294579/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(71/256:ℝ)) (by norm_num : 2*(71/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(71/256:ℝ)) ≤ (341922482788324347/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (71/256:ℝ) (5470757983213/1000000000000:ℝ) (341922482788324347/62500000000000000:ℝ) (966793374627/100000000000000:ℝ) (966795058203/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0426).1 (thetaFirstMode_refined_node_0426).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0218 :
    (-496558806876634857621765776793/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (143/512:ℝ) ∧ thetaFirstModeFirst (143/512:ℝ) ≤ (-2482788865938089219118733/25000000000000000000000000:ℝ) := by
  have hlo : (5492169924557/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(143/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(143/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(143/512:ℝ)) ≤ (874106173647/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(143/512:ℝ)) (by norm_num : 2*(143/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(143/512:ℝ)) ≤ (2746085836386199671/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (143/512:ℝ) (5492169924557/1000000000000:ℝ) (2746085836386199671/500000000000000000:ℝ) (473618539969/50000000000000:ℝ) (189447747183/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0427).1 (thetaFirstMode_refined_node_0427).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0219 :
    (-4964071412775898871754220633283/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (4397964224531456007/15744504565196700160:ℝ) ∧ thetaFirstModeFirst (4397964224531456007/15744504565196700160:ℝ) ≤ (-4964061078415802102122229/50000000000000000000000000:ℝ) := by
  have hlo : (5492569909379/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(4397964224531456007/15744504565196700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(4397964224531456007/15744504565196700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(4397964224531456007/15744504565196700160:ℝ)) ≤ (1748339666443/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(4397964224531456007/15744504565196700160:ℝ)) (by norm_num : 2*(4397964224531456007/15744504565196700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(4397964224531456007/15744504565196700160:ℝ)) ≤ (5492571657719663699/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (4397964224531456007/15744504565196700160:ℝ) (5492569909379/1000000000000:ℝ) (5492571657719663699/1000000000000000000:ℝ) (946875514151/100000000000000:ℝ) (946877169617/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0431).1 (thetaFirstMode_refined_node_0431).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0220 :
    (-4884684556704138430807991106597/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/32:ℝ) ∧ thetaFirstModeFirst (9/32:ℝ) ≤ (-610584294389417851269103/6250000000000000000000000:ℝ) := by
  have hlo : (5513665669869/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/32:ℝ)) ≤ (1755054656961/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/32:ℝ)) (by norm_num : 2*(9/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/32:ℝ)) ≤ (5513667424926078873/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/32:ℝ) (5513665669869/1000000000000:ℝ) (5513667424926078873/1000000000000000000:ℝ) (115999824587/12500000000000:ℝ) (928000225389/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0432).1 (thetaFirstMode_refined_node_0432).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0221 :
    (-4804691299394502025097380948027/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (145/512:ℝ) ∧ thetaFirstModeFirst (145/512:ℝ) ≤ (-75073144252494485009719/781250000000000000000000:ℝ) := by
  have hlo : (5535245547149/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(145/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(145/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(145/512:ℝ)) ≤ (1761923746671/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(145/512:ℝ)) (by norm_num : 2*(145/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(145/512:ℝ)) ≤ (5535247309075386903/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (145/512:ℝ) (5535245547149/1000000000000:ℝ) (5535247309075386903/1000000000000000000:ℝ) (14204286931/1562500000000:ℝ) (909075965309/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0433).1 (thetaFirstMode_refined_node_0433).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0222 :
    (-600403627685138544767187612993/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (996695256742326405/3518919113747927552:ℝ) ∧ thetaFirstModeFirst (996695256742326405/3518919113747927552:ℝ) ≤ (-480321895670816201559809/5000000000000000000000000:ℝ) := by
  have hlo : (2767821555661/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(996695256742326405/3518919113747927552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(996695256742326405/3518919113747927552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(996695256742326405/3518919113747927552:ℝ)) ≤ (220256286913/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(996695256742326405/3518919113747927552:ℝ)) (by norm_num : 2*(996695256742326405/3518919113747927552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(996695256742326405/3518919113747927552:ℝ)) ≤ (691955609171872409/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (996695256742326405/3518919113747927552:ℝ) (2767821555661/500000000000:ℝ) (691955609171872409/125000000000000000:ℝ) (181745867269/20000000000000:ℝ) (908730937577/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0437).1 (thetaFirstMode_refined_node_0437).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0223 :
    (-590700664886053846604941614681/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (73/256:ℝ) ∧ thetaFirstModeFirst (73/256:ℝ) ≤ (-2362797692632079557489031/25000000000000000000000000:ℝ) := by
  have hlo : (5556909885681/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(73/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(73/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(73/256:ℝ)) ≤ (884409860619/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(73/256:ℝ)) (by norm_num : 2*(73/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(73/256:ℝ)) ≤ (2778455827251626067/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (73/256:ℝ) (5556909885681/1000000000000:ℝ) (2778455827251626067/500000000000000000:ℝ) (445230415351/50000000000000:ℝ) (222615601443/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0438).1 (thetaFirstMode_refined_node_0438).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

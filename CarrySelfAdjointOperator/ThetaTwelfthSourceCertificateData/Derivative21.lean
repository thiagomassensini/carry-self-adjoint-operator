import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0672 :
    (-1890641322490252181259421/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (24058522909244262175605/27680444625863446871552:ℝ) ∧ thetaFirstModeFirst (24058522909244262175605/27680444625863446871552:ℝ) ≤ (-75625191549065089/40000000000000000000000:ℝ) := by
  have hlo : (71473639011/4000000000:ℝ) ≤ Real.pi*Real.exp (2*(24058522909244262175605/27680444625863446871552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(24058522909244262175605/27680444625863446871552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(24058522909244262175605/27680444625863446871552:ℝ)) ≤ (227507706319/40000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(24058522909244262175605/27680444625863446871552:ℝ)) (by norm_num : 2*(24058522909244262175605/27680444625863446871552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(24058522909244262175605/27680444625863446871552:ℝ)) ≤ (714736617617826167/40000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (24058522909244262175605/27680444625863446871552:ℝ) (71473639011/4000000000:ℝ) (714736617617826167/40000000000000000:ℝ) (1073099/20000000000000:ℝ) (2682763/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1337).1 (thetaFirstMode_refined_node_1337).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0673 :
    (-44308893953601832295239741/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (223/256:ℝ) ∧ thetaFirstModeFirst (223/256:ℝ) ≤ (-88617228662842527941/50000000000000000000000000:ℝ) := by
  have hlo : (17937924841901/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(223/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(223/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(223/256:ℝ)) ≤ (2854910001347/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(223/256:ℝ)) (by norm_num : 2*(223/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(223/256:ℝ)) ≤ (8968965275861725771/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (223/256:ℝ) (17937924841901/1000000000000:ℝ) (8968965275861725771/500000000000000000:ℝ) (5010041/100000000000000:ℝ) (5010071/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1338).1 (thetaFirstMode_refined_node_1338).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0674 :
    (-8301849428937970973837069/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (447/512:ℝ) ∧ thetaFirstModeFirst (447/512:ℝ) ≤ (-83017970264052112557/50000000000000000000000000:ℝ) := by
  have hlo : (18008131894691/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(447/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(447/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(447/512:ℝ)) ≤ (2866083803163/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(447/512:ℝ)) (by norm_num : 2*(447/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(447/512:ℝ)) ≤ (9004068813430258659/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (447/512:ℝ) (18008131894691/1000000000000:ℝ) (9004068813430258659/500000000000000000:ℝ) (4674927/100000000000000:ℝ) (934991/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1339).1 (thetaFirstMode_refined_node_1339).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0675 :
    (-41493055534829519713612419/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (125246713502597024463543/143457408303917490588160:ℝ) ∧ thetaFirstModeFirst (125246713502597024463543/143457408303917490588160:ℝ) ≤ (-82985587043050007277/50000000000000000000000000:ℝ) := by
  have hlo : (18008551541389/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(125246713502597024463543/143457408303917490588160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125246713502597024463543/143457408303917490588160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(125246713502597024463543/143457408303917490588160:ℝ)) ≤ (2866150592023/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(125246713502597024463543/143457408303917490588160:ℝ)) (by norm_num : 2*(125246713502597024463543/143457408303917490588160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(125246713502597024463543/143457408303917490588160:ℝ)) ≤ (9004278636845312639/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (125246713502597024463543/143457408303917490588160:ℝ) (18008551541389/1000000000000:ℝ) (9004278636845312639/500000000000000000:ℝ) (4672993/100000000000000:ℝ) (4673021/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1343).1 (thetaFirstMode_refined_node_1343).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0676 :
    (-1214868874618164916978457/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/8:ℝ) ∧ thetaFirstModeFirst (7/8:ℝ) ≤ (-3887555966772825077/2500000000000000000000000:ℝ) := by
  have hlo : (9039306865059/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/8:ℝ)) ≤ (2877301338003/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/8:ℝ)) (by norm_num : 2*(7/8:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/8:ℝ)) ≤ (9039309742360858779/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/8:ℝ) (9039306865059/500000000000:ℝ) (9039309742360858779/500000000000000000:ℝ) (436103/10000000000000:ℝ) (136283/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1344).1 (thetaFirstMode_refined_node_1344).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0677 :
    (-4549923237862366964710341/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (449/512:ℝ) ∧ thetaFirstModeFirst (449/512:ℝ) ≤ (-142184216259104877/97656250000000000000000:ℝ) := by
  have hlo : (567167856989/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(449/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(449/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(449/512:ℝ)) ≤ (2888562777033/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(449/512:ℝ)) (by norm_num : 2*(449/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(449/512:ℝ)) ≤ (9074688600387433569/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (449/512:ℝ) (567167856989/31250000000:ℝ) (9074688600387433569/500000000000000000:ℝ) (254193/6250000000000:ℝ) (508389/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1345).1 (thetaFirstMode_refined_node_1345).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0678 :
    (-2274070919420238827123631/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (130381348261662627095241/148673423925516220418560:ℝ) ∧ thetaFirstModeFirst (130381348261662627095241/148673423925516220418560:ℝ) ≤ (-36384899219805063681/25000000000000000000000000:ℝ) := by
  have hlo : (9074896238919/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(130381348261662627095241/148673423925516220418560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(130381348261662627095241/148673423925516220418560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(130381348261662627095241/148673423925516220418560:ℝ)) ≤ (2888629789903/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(130381348261662627095241/148673423925516220418560:ℝ)) (by norm_num : 2*(130381348261662627095241/148673423925516220418560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(130381348261662627095241/148673423925516220418560:ℝ)) ≤ (9074899127550735479/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (130381348261662627095241/148673423925516220418560:ℝ) (9074896238919/500000000000:ℝ) (9074899127550735479/500000000000000000:ℝ) (4065399/100000000000000:ℝ) (254089/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1349).1 (thetaFirstMode_refined_node_1349).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0679 :
    (-6814254382419506285542371/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (225/256:ℝ) ∧ thetaFirstModeFirst (225/256:ℝ) ≤ (-68142108512649000627/50000000000000000000000000:ℝ) := by
  have hlo : (18220406054961/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(225/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(225/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(225/256:ℝ)) ≤ (5799736584179/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(225/256:ℝ)) (by norm_num : 2*(225/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(225/256:ℝ)) ≤ (18220411854700657147/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (225/256:ℝ) (18220406054961/1000000000000:ℝ) (18220411854700657147/1000000000000000000:ℝ) (3791907/100000000000000:ℝ) (379193/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1350).1 (thetaFirstMode_refined_node_1350).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0680 :
    (-3985398907040595021387627/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (451/512:ℝ) ∧ thetaFirstModeFirst (451/512:ℝ) ≤ (-797074562701286519/625000000000000000000000:ℝ) := by
  have hlo : (457292967699/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(451/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(451/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(451/512:ℝ)) ≤ (5822436111361/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(451/512:ℝ)) (by norm_num : 2*(451/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(451/512:ℝ)) ≤ (18291724530398938073/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (451/512:ℝ) (457292967699/25000000000:ℝ) (18291724530398938073/1000000000000000000:ℝ) (1767181/50000000000000:ℝ) (220899/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1351).1 (thetaFirstMode_refined_node_1351).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0681 :
    (-398383235380354727994879/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (135702249480635062632759/154054636064115110786560:ℝ) ∧ thetaFirstModeFirst (135702249480635062632759/154054636064115110786560:ℝ) ≤ (-1274818003262159661/1000000000000000000000000:ℝ) := by
  have hlo : (3658428236549/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(135702249480635062632759/154054636064115110786560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(135702249480635062632759/154054636064115110786560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(135702249480635062632759/154054636064115110786560:ℝ)) ≤ (582257058929/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(135702249480635062632759/154054636064115110786560:ℝ)) (by norm_num : 2*(135702249480635062632759/154054636064115110786560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(135702249480635062632759/154054636064115110786560:ℝ)) ≤ (1829214700531933897/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (135702249480635062632759/154054636064115110786560:ℝ) (3658428236549/200000000000:ℝ) (1829214700531933897/100000000000000000:ℝ) (353289/10000000000000:ℝ) (220807/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1355).1 (thetaFirstMode_refined_node_1355).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0682 :
    (-2982729760082492234380577/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (113/128:ℝ) ∧ thetaFirstModeFirst (113/128:ℝ) ≤ (-59654213684708842281/50000000000000000000000000:ℝ) := by
  have hlo : (18363310470791/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(113/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(113/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(113/128:ℝ)) ≤ (292261224099/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(113/128:ℝ)) (by norm_num : 2*(113/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(113/128:ℝ)) ≤ (918165815800849707/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (113/128:ℝ) (18363310470791/1000000000000:ℝ) (918165815800849707/50000000000000000:ℝ) (3293391/100000000000000:ℝ) (3293411/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1356).1 (thetaFirstMode_refined_node_1356).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0683 :
    (-87175473746972162804871/78125000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (453/512:ℝ) ∧ thetaFirstModeFirst (453/512:ℝ) ≤ (-55791939676208617551/50000000000000000000000000:ℝ) := by
  have hlo : (18435182435859/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(453/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(453/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(453/512:ℝ)) ≤ (73351275547/12500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(453/512:ℝ)) (by norm_num : 2*(453/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(453/512:ℝ)) ≤ (230439853799526371/12500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (453/512:ℝ) (18435182435859/1000000000000:ℝ) (230439853799526371/12500000000000000:ℝ) (3067989/100000000000000:ℝ) (383501/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1357).1 (thetaFirstMode_refined_node_1357).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0684 :
    (-1115405432254215581692793/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (141215303034674977169457/159605509118049574428160:ℝ) ∧ thetaFirstModeFirst (141215303034674977169457/159605509118049574428160:ℝ) ≤ (-1742809627809731619/1562500000000000000000000:ℝ) := by
  have hlo : (1152225396523/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(141215303034674977169457/159605509118049574428160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(141215303034674977169457/159605509118049574428160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(141215303034674977169457/159605509118049574428160:ℝ)) ≤ (2934118489029/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(141215303034674977169457/159605509118049574428160:ℝ)) (by norm_num : 2*(141215303034674977169457/159605509118049574428160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(141215303034674977169457/159605509118049574428160:ℝ)) ≤ (9217806106304083197/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (141215303034674977169457/159605509118049574428160:ℝ) (1152225396523/62500000000:ℝ) (9217806106304083197/500000000000000000:ℝ) (1533353/50000000000000:ℝ) (122669/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1361).1 (thetaFirstMode_refined_node_1361).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0685 :
    (-6520673449891673726020543/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (227/256:ℝ) ∧ thetaFirstModeFirst (227/256:ℝ) ≤ (-1043300842699082649/1000000000000000000000000:ℝ) := by
  have hlo : (3701467139969/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(227/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(227/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(227/256:ℝ)) ≤ (2945534572893/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(227/256:ℝ)) (by norm_num : 2*(227/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(227/256:ℝ)) ≤ (9253670795458638549/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (227/256:ℝ) (3701467139969/200000000000:ℝ) (9253670795458638549/500000000000000000:ℝ) (285721/10000000000000:ℝ) (714307/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1362).1 (thetaFirstMode_refined_node_1362).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0686 :
    (-48760451929660833151692227/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (455/512:ℝ) ∧ thetaFirstModeFirst (455/512:ℝ) ≤ (-76187694673310493/78125000000000000000000:ℝ) := by
  have hlo : (9289885681861/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(455/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(455/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(455/512:ℝ)) ≤ (5914126138507/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(455/512:ℝ)) (by norm_num : 2*(455/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(455/512:ℝ)) ≤ (18579777277850621651/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (455/512:ℝ) (9289885681861/500000000000:ℝ) (18579777277850621651/1000000000000000000:ℝ) (8313/312500000000:ℝ) (2660177/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1363).1 (thetaFirstMode_refined_node_1363).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0687 :
    (-609264086806244446373891/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29385310700934990796995/33066121515527560919552:ℝ) ∧ thetaFirstModeFirst (29385310700934990796995/33066121515527560919552:ℝ) ≤ (-1218519990119228271/1250000000000000000000000:ℝ) := by
  have hlo : (1858019671911/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(29385310700934990796995/33066121515527560919552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29385310700934990796995/33066121515527560919552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29385310700934990796995/33066121515527560919552:ℝ)) ≤ (73928269167/12500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29385310700934990796995/33066121515527560919552:ℝ)) (by norm_num : 2*(29385310700934990796995/33066121515527560919552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29385310700934990796995/33066121515527560919552:ℝ)) ≤ (232252532917163031/12500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29385310700934990796995/33066121515527560919552:ℝ) (1858019671911/100000000000:ℝ) (232252532917163031/12500000000000000:ℝ) (664761/25000000000000:ℝ) (2659061/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1367).1 (thetaFirstMode_refined_node_1367).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0688 :
    (-11391209723696625120842823/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (57/64:ℝ) ∧ thetaFirstModeFirst (57/64:ℝ) ≤ (-11391137039163234807/12500000000000000000000000:ℝ) := by
  have hlo : (4663122633193/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(57/64:ℝ)) ≤ (2968636686873/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(57/64:ℝ)) (by norm_num : 2*(57/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(57/64:ℝ)) ≤ (9326248235023408689/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (57/64:ℝ) (4663122633193/250000000000:ℝ) (9326248235023408689/500000000000000000:ℝ) (2475999/100000000000000:ℝ) (1238007/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1368).1 (thetaFirstMode_refined_node_1368).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0689 :
    (-4256653648595396390357827/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (457/512:ℝ) ∧ thetaFirstModeFirst (457/512:ℝ) ≤ (-4256624562084654193/5000000000000000000000000:ℝ) := by
  have hlo : (18725494316601/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(457/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(457/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(457/512:ℝ)) ≤ (2980255602351/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(457/512:ℝ)) (by norm_num : 2*(457/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(457/512:ℝ)) ≤ (9362750138556685143/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (457/512:ℝ) (18725494316601/1000000000000:ℝ) (9362750138556685143/500000000000000000:ℝ) (230393/10000000000000:ℝ) (460789/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1369).1 (thetaFirstMode_refined_node_1369).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0690 :
    (-425495981963120782550659/500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (152842207727465608740993/171234597812449350300160:ℝ) ∧ thetaFirstModeFirst (152842207727465608740993/171234597812449350300160:ℝ) ≤ (-531866341628409711/625000000000000000000000:ℝ) := by
  have hlo : (18725921132053/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(152842207727465608740993/171234597812449350300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(152842207727465608740993/171234597812449350300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(152842207727465608740993/171234597812449350300160:ℝ)) ≤ (1490161766077/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(152842207727465608740993/171234597812449350300160:ℝ)) (by norm_num : 2*(152842207727465608740993/171234597812449350300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(152842207727465608740993/171234597812449350300160:ℝ)) ≤ (4681481773175140661/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (152842207727465608740993/171234597812449350300160:ℝ) (18725921132053/1000000000000:ℝ) (4681481773175140661/250000000000000000:ℝ) (28787/1250000000000:ℝ) (92119/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1373).1 (thetaFirstMode_refined_node_1373).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0691 :
    (-19877077925909999432716887/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (229/256:ℝ) ∧ thetaFirstModeFirst (229/256:ℝ) ≤ (-19876941672073401267/25000000000000000000000000:ℝ) := by
  have hlo : (9399391914581/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(229/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(229/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(229/256:ℝ)) ≤ (2991919992979/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(229/256:ℝ)) (by norm_num : 2*(229/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(229/256:ℝ)) ≤ (9399394906502875547/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (229/256:ℝ) (9399391914581/500000000000:ℝ) (9399394906502875547/500000000000000000:ℝ) (2143207/100000000000000:ℝ) (2143221/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1374).1 (thetaFirstMode_refined_node_1374).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0692 :
    (-18558472857608825239955577/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (459/512:ℝ) ∧ thetaFirstModeFirst (459/512:ℝ) ≤ (-11877341328394317/16000000000000000000000:ℝ) := by
  have hlo : (3774472037753/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(459/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(459/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(459/512:ℝ)) ≤ (6007260073481/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(459/512:ℝ)) (by norm_num : 2*(459/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(459/512:ℝ)) ≤ (18872366196027395233/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (459/512:ℝ) (3774472037753/200000000000:ℝ) (18872366196027395233/1000000000000000000:ℝ) (3189/160000000000:ℝ) (996569/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1375).1 (thetaFirstMode_refined_node_1375).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0693 :
    (-2318882435067136478747643/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (158968638409273606456191/177322249882403159887360:ℝ) ∧ thetaFirstModeFirst (158968638409273606456191/177322249882403159887360:ℝ) ≤ (-37101864896305186519/50000000000000000000000000:ℝ) := by
  have hlo : (18872788477493/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(158968638409273606456191/177322249882403159887360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(158968638409273606456191/177322249882403159887360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(158968638409273606456191/177322249882403159887360:ℝ)) ≤ (3003698201023/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(158968638409273606456191/177322249882403159887360:ℝ)) (by norm_num : 2*(158968638409273606456191/177322249882403159887360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(158968638409273606456191/177322249882403159887360:ℝ)) ≤ (9436397242446449639/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (158968638409273606456191/177322249882403159887360:ℝ) (18872788477493/1000000000000:ℝ) (9436397242446449639/500000000000000000:ℝ) (1992283/100000000000000:ℝ) (249037/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1379).1 (thetaFirstMode_refined_node_1379).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0694 :
    (-6928938958040826438853041/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (115/128:ℝ) ∧ thetaFirstModeFirst (115/128:ℝ) ≤ (-8661110141019229941/12500000000000000000000000:ℝ) := by
  have hlo : (9473112259049/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(115/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(115/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(115/128:ℝ)) ≤ (1206154364927/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(115/128:ℝ)) (by norm_num : 2*(115/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(115/128:ℝ)) ≤ (3789246109774108711/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (115/128:ℝ) (9473112259049/500000000000:ℝ) (3789246109774108711/200000000000000000:ℝ) (926509/50000000000000:ℝ) (1853031/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1380).1 (thetaFirstMode_refined_node_1380).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0695 :
    (-8081936082709550207941931/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (461/512:ℝ) ∧ thetaFirstModeFirst (461/512:ℝ) ≤ (-32327527429382337383/50000000000000000000000000:ℝ) := by
  have hlo : (19020377944241/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(461/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(461/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(461/512:ℝ)) ≤ (3027187799091/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(461/512:ℝ)) (by norm_num : 2*(461/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(461/512:ℝ)) ≤ (9510191999309691963/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (461/512:ℝ) (19020377944241/1000000000000:ℝ) (9510191999309691963/500000000000000000:ℝ) (1722263/100000000000000:ℝ) (861137/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1381).1 (thetaFirstMode_refined_node_1381).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0696 :
    (-4039347728469461010626529/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (165312387803273059105209/183598439372905969845760:ℝ) ∧ thetaFirstModeFirst (165312387803273059105209/183598439372905969845760:ℝ) ≤ (-807863653873726467/1250000000000000000000000:ℝ) := by
  have hlo : (1902080771949/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(165312387803273059105209/183598439372905969845760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(165312387803273059105209/183598439372905969845760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(165312387803273059105209/183598439372905969845760:ℝ)) ≤ (6054512399921/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(165312387803273059105209/183598439372905969845760:ℝ)) (by norm_num : 2*(165312387803273059105209/183598439372905969845760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(165312387803273059105209/183598439372905969845760:ℝ)) ≤ (19020813774005014153/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (165312387803273059105209/183598439372905969845760:ℝ) (1902080771949/100000000000:ℝ) (19020813774005014153/1000000000000000000:ℝ) (430383/25000000000000:ℝ) (215193/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1385).1 (thetaFirstMode_refined_node_1385).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0697 :
    (-376962510432121021121593/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (231/256:ℝ) ∧ thetaFirstModeFirst (231/256:ℝ) ≤ (-942399494215963971/1562500000000000000000000:ℝ) := by
  have hlo : (596713174959/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(231/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(231/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(231/256:ℝ)) ≤ (3039035877143/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(231/256:ℝ)) (by norm_num : 2*(231/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(231/256:ℝ)) ≤ (9547413838381308799/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (231/256:ℝ) (596713174959/31250000000:ℝ) (9547413838381308799/500000000000000000:ℝ) (1600269/100000000000000:ℝ) (40007/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1386).1 (thetaFirstMode_refined_node_1386).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0698 :
    (-14061908232375730772436333/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (463/512:ℝ) ∧ thetaFirstModeFirst (463/512:ℝ) ≤ (-7030904549700312181/12500000000000000000000000:ℝ) := by
  have hlo : (19169556617361/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(463/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(463/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(463/512:ℝ)) ≤ (6101860654523/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(463/512:ℝ)) (by norm_num : 2*(463/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(463/512:ℝ)) ≤ (19169562719224875139/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (463/512:ℝ) (19169556617361/1000000000000:ℝ) (19169562719224875139/1000000000000000000:ℝ) (371621/25000000000000:ℝ) (743247/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1387).1 (thetaFirstMode_refined_node_1387).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0699 :
    (-14056240598261792362790163/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (171880171452079192654407/190068149254242844572160:ℝ) ∧ thetaFirstModeFirst (171880171452079192654407/190068149254242844572160:ℝ) ≤ (-14056141464959673753/25000000000000000000000000:ℝ) := by
  have hlo : (9584993946203/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(171880171452079192654407/190068149254242844572160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(171880171452079192654407/190068149254242844572160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(171880171452079192654407/190068149254242844572160:ℝ)) ≤ (3050998966831/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(171880171452079192654407/190068149254242844572160:ℝ)) (by norm_num : 2*(171880171452079192654407/190068149254242844572160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(171880171452079192654407/190068149254242844572160:ℝ)) ≤ (9584996997203501783/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (171880171452079192654407/190068149254242844572160:ℝ) (9584993946203/500000000000:ℝ) (9584996997203501783/500000000000000000:ℝ) (1485851/100000000000000:ℝ) (1485861/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1391).1 (thetaFirstMode_refined_node_1391).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0700 :
    (-6555004609038838449985561/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29/32:ℝ) ∧ thetaFirstModeFirst (29/32:ℝ) ≤ (-2621983902895802101/5000000000000000000000000:ℝ) := by
  have hlo : (9622292070313/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(29/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29/32:ℝ)) ≤ (3062871330941/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29/32:ℝ)) (by norm_num : 2*(29/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29/32:ℝ)) ≤ (9622295133184929013/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29/32:ℝ) (9622292070313/500000000000:ℝ) (9622295133184929013/500000000000000000:ℝ) (276077/20000000000000:ℝ) (690197/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1392).1 (thetaFirstMode_refined_node_1392).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0701 :
    (-3054739988834506515653311/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (465/512:ℝ) ∧ thetaFirstModeFirst (465/512:ℝ) ≤ (-4887551894124569229/10000000000000000000000000:ℝ) := by
  have hlo : (3863981062663/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(465/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(465/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(465/512:ℝ)) ≤ (768714767597/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(465/512:ℝ)) (by norm_num : 2*(465/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(465/512:ℝ)) ≤ (2414988932879362021/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (465/512:ℝ) (3863981062663/200000000000:ℝ) (2414988932879362021/125000000000000000:ℝ) (1281483/100000000000000:ℝ) (1281491/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1393).1 (thetaFirstMode_refined_node_1393).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0702 :
    (-95422043151049020597989/195312500000000000000000000000:ℝ) ≤ thetaFirstModeFirst (35735776399208126994885/39347294353086520381952:ℝ) ∧ thetaFirstModeFirst (35735776399208126994885/39347294353086520381952:ℝ) ≤ (-2442786353600135071/5000000000000000000000000:ℝ) := by
  have hlo : (9660169050733/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(35735776399208126994885/39347294353086520381952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(35735776399208126994885/39347294353086520381952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(35735776399208126994885/39347294353086520381952:ℝ)) ≤ (384365993847/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(35735776399208126994885/39347294353086520381952:ℝ)) (by norm_num : 2*(35735776399208126994885/39347294353086520381952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(35735776399208126994885/39347294353086520381952:ℝ)) ≤ (1207521515707778271/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (35735776399208126994885/39347294353086520381952:ℝ) (9660169050733/500000000000:ℝ) (1207521515707778271/62500000000000000:ℝ) (256187/20000000000000:ℝ) (80059/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1397).1 (thetaFirstMode_refined_node_1397).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0703 :
    (-5692558824771531178850603/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (233/256:ℝ) ∧ thetaFirstModeFirst (233/256:ℝ) ≤ (-5692518698070162131/12500000000000000000000000:ℝ) := by
  have hlo : (19395521284739/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(233/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(233/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(233/256:ℝ)) ≤ (6173787457041/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(233/256:ℝ)) (by norm_num : 2*(233/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(233/256:ℝ)) ≤ (19395527458527806313/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (233/256:ℝ) (19395521284739/1000000000000:ℝ) (19395527458527806313/1000000000000000000:ℝ) (297329/25000000000000:ℝ) (297331/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1398).1 (thetaFirstMode_refined_node_1398).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0288 :
    (-531140713145251965214171273941/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (54109642629131284041/146571795189741237760:ℝ) ∧ thetaFirstModeFirst (54109642629131284041/146571795189741237760:ℝ) ≤ (-531139426006637186806179/12500000000000000000000000:ℝ) := by
  have hlo : (6573628969197/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(54109642629131284041/146571795189741237760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(54109642629131284041/146571795189741237760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(54109642629131284041/146571795189741237760:ℝ)) ≤ (1046225762161/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(54109642629131284041/146571795189741237760:ℝ)) (by norm_num : 2*(54109642629131284041/146571795189741237760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(54109642629131284041/146571795189741237760:ℝ)) ≤ (3286815530824662473/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (54109642629131284041/146571795189741237760:ℝ) (6573628969197/1000000000000:ℝ) (3286815530824662473/500000000000000000:ℝ) (83992819407/25000000000000:ℝ) (167985990317/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0569).1 (thetaFirstMode_refined_node_0569).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0289 :
    (-2081663105498706539138262658599/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (95/256:ℝ) ∧ thetaFirstModeFirst (95/256:ℝ) ≤ (-130103627762255964031853/3125000000000000000000000:ℝ) := by
  have hlo : (6598993766613/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(95/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(95/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(95/256:ℝ)) ≤ (2100525391781/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(95/256:ℝ)) (by norm_num : 2*(95/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(95/256:ℝ)) ≤ (6598995867141447133/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (95/256:ℝ) (6598993766613/1000000000000:ℝ) (6598995867141447133/1000000000000000000:ℝ) (20492007481/6250000000000:ℝ) (327872808403/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0570).1 (thetaFirstMode_refined_node_0570).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0290 :
    (-203882921158521391533026414573/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (191/512:ℝ) ∧ thetaFirstModeFirst (191/512:ℝ) ≤ (-50970605944413100095651/1250000000000000000000000:ℝ) := by
  have hlo : (165620537449/25000000000:ℝ) ≤ Real.pi*Real.exp (2*(191/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(191/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(191/512:ℝ)) ≤ (2108746615717/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(191/512:ℝ)) (by norm_num : 2*(191/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(191/512:ℝ)) ≤ (6624823606710217181/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (191/512:ℝ) (165620537449/25000000000:ℝ) (6624823606710217181/1000000000000000000:ℝ) (319824521899/100000000000000:ℝ) (31982519633/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0571).1 (thetaFirstMode_refined_node_0571).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0291 :
    (-203823608088457410080610158259/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (59486127077809925559/159448540415669455360:ℝ) ∧ thetaFirstModeFirst (59486127077809925559/159448540415669455360:ℝ) ≤ (-254778888535752836647339/6250000000000000000000000:ℝ) := by
  have hlo : (6625182758327/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(59486127077809925559/159448540415669455360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59486127077809925559/159448540415669455360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(59486127077809925559/159448540415669455360:ℝ)) ≤ (2108861608487/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(59486127077809925559/159448540415669455360:ℝ)) (by norm_num : 2*(59486127077809925559/159448540415669455360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(59486127077809925559/159448540415669455360:ℝ)) ≤ (6625184867191499791/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (59486127077809925559/159448540415669455360:ℝ) (6625182758327/1000000000000:ℝ) (6625184867191499791/1000000000000000000:ℝ) (39964170157/12500000000000:ℝ) (31971403549/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0575).1 (thetaFirstMode_refined_node_0575).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0292 :
    (-1996673611171739200025073949849/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/8:ℝ) ∧ thetaFirstModeFirst (3/8:ℝ) ≤ (-319466995811341941873/8000000000000000000000:ℝ) := by
  have hlo : (665075031619/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/8:ℝ)) ≤ (2117000016613/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/8:ℝ)) (by norm_num : 2*(3/8:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/8:ℝ)) ≤ (6650752433191284509/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/8:ℝ) (665075031619/100000000000:ℝ) (6650752433191284509/1000000000000000000:ℝ) (499108667/160000000000:ℝ) (311943577261/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0576).1 (thetaFirstMode_refined_node_0576).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0293 :
    (-3054984370704279972045734603/78125000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (193/512:ℝ) ∧ thetaFirstModeFirst (193/512:ℝ) ≤ (-122199074708781032214327/3125000000000000000000000:ℝ) := by
  have hlo : (417298788559/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(193/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(193/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(193/512:ℝ)) ≤ (2125285720407/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(193/512:ℝ)) (by norm_num : 2*(193/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(193/512:ℝ)) ≤ (6676782742230588351/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (193/512:ℝ) (417298788559/62500000000:ℝ) (6676782742230588351/1000000000000000000:ℝ) (304224667353/100000000000000:ℝ) (475352053/156250000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0577).1 (thetaFirstMode_refined_node_0577).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0294 :
    (-244327697043121646172975414807/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (65332341813084493257/173304480845017500160:ℝ) ∧ thetaFirstModeFirst (65332341813084493257/173304480845017500160:ℝ) ≤ (-39092335512243120008019/1000000000000000000000000:ℝ) := by
  have hlo : (3338570469331/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(65332341813084493257/173304480845017500160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(65332341813084493257/173304480845017500160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(65332341813084493257/173304480845017500160:ℝ)) ≤ (531350103599/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(65332341813084493257/173304480845017500160:ℝ)) (by norm_num : 2*(65332341813084493257/173304480845017500160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(65332341813084493257/173304480845017500160:ℝ)) ≤ (1669285766015893207/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (65332341813084493257/173304480845017500160:ℝ) (3338570469331/500000000000:ℝ) (1669285766015893207/250000000000000000:ℝ) (12164766849/4000000000000:ℝ) (152059908801/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0581).1 (thetaFirstMode_refined_node_0581).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0295 :
    (-191437203566876054659248635867/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (97/256:ℝ) ∧ thetaFirstModeFirst (97/256:ℝ) ≤ (-1531493854541158391569/40000000000000000000000:ℝ) := by
  have hlo : (1340582559483/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(97/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(97/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(97/256:ℝ)) ≤ (213360385353/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(97/256:ℝ)) (by norm_num : 2*(97/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(97/256:ℝ)) ≤ (670291493102287329/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (97/256:ℝ) (1340582559483/200000000000:ℝ) (670291493102287329/100000000000000000:ℝ) (1186668643/400000000000:ℝ) (296667793723/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0582).1 (thetaFirstMode_refined_node_0582).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0296 :
    (-234276670866635162282019695679/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (195/512:ℝ) ∧ thetaFirstModeFirst (195/512:ℝ) ≤ (-366056393134101133031/9765625000000000000000:ℝ) := by
  have hlo : (6729147256349/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(195/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(195/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(195/512:ℝ)) ≤ (267744317863/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(195/512:ℝ)) (by norm_num : 2*(195/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(195/512:ℝ)) ≤ (841143674788175759/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (195/512:ℝ) (6729147256349/1000000000000:ℝ) (841143674788175759/125000000000000000:ℝ) (56497619/19531250000:ℝ) (289268428881/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0583).1 (thetaFirstMode_refined_node_0583).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0297 :
    (-29276075031654577887586844773/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (14336762398671353355/37640552179499351552:ℝ) ∧ thetaFirstModeFirst (14336762398671353355/37640552179499351552:ℝ) ≤ (-58552005283468566995937/1562500000000000000000000:ℝ) := by
  have hlo : (841188335053/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(14336762398671353355/37640552179499351552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(14336762398671353355/37640552179499351552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(14336762398671353355/37640552179499351552:ℝ)) ≤ (535517237791/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(14336762398671353355/37640552179499351552:ℝ)) (by norm_num : 2*(14336762398671353355/37640552179499351552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(14336762398671353355/37640552179499351552:ℝ)) ≤ (1682377205623541063/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (14336762398671353355/37640552179499351552:ℝ) (841188335053/125000000000:ℝ) (1682377205623541063/250000000000000000:ℝ) (72291929829/25000000000000:ℝ) (18073021171/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0587).1 (thetaFirstMode_refined_node_0587).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0298 :
    (-1834707607989126777971562390339/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (49/128:ℝ) ∧ thetaFirstModeFirst (49/128:ℝ) ≤ (-458675764072266452689033/12500000000000000000000000:ℝ) := by
  have hlo : (1688871098513/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(49/128:ℝ)) ≤ (2150337915953/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(49/128:ℝ)) (by norm_num : 2*(49/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(49/128:ℝ)) ≤ (6755486544392533129/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (49/128:ℝ) (1688871098513/250000000000:ℝ) (6755486544392533129/1000000000000000000:ℝ) (282024050041/100000000000000:ℝ) (282024656491/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0588).1 (thetaFirstMode_refined_node_0588).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0299 :
    (-448962088504106680795592683839/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (197/512:ℝ) ∧ thetaFirstModeFirst (197/512:ℝ) ≤ (-1795843883699179309941067/50000000000000000000000000:ℝ) := by
  have hlo : (6781924612397/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(197/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(197/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(197/512:ℝ)) ≤ (539688525149/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(197/512:ℝ)) (by norm_num : 2*(197/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(197/512:ℝ)) ≤ (1695481692788422357/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (197/512:ℝ) (6781924612397/1000000000000:ℝ) (1695481692788422357/250000000000000000:ℝ) (274933345111/100000000000000:ℝ) (274933938627/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0589).1 (thetaFirstMode_refined_node_0589).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0300 :
    (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (78578341309131839793/204209882504936988160:ℝ) ∧ thetaFirstModeFirst (78578341309131839793/204209882504936988160:ℝ) ≤ (-448830586379803472589969/12500000000000000000000000:ℝ) := by
  have hlo : (1695570794689/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(78578341309131839793/204209882504936988160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(78578341309131839793/204209882504936988160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(78578341309131839793/204209882504936988160:ℝ)) ≤ (2158868235837/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(78578341309131839793/204209882504936988160:ℝ)) (by norm_num : 2*(78578341309131839793/204209882504936988160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(78578341309131839793/204209882504936988160:ℝ)) ≤ (6782285337627868341/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (78578341309131839793/204209882504936988160:ℝ) (1695570794689/250000000000:ℝ) (6782285337627868341/1000000000000000000:ℝ) (274838413521/100000000000000:ℝ) (274839006863/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0593).1 (thetaFirstMode_refined_node_0593).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0301 :
    (-109851823764213060394908947733/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (99/256:ℝ) ∧ thetaFirstModeFirst (99/256:ℝ) ≤ (-878812395142435166247603/25000000000000000000000000:ℝ) := by
  have hlo : (6808468314831/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(99/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(99/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(99/256:ℝ)) ≤ (1083601612627/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(99/256:ℝ)) (by norm_num : 2*(99/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(99/256:ℝ)) ≤ (3404235241017694811/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (99/256:ℝ) (6808468314831/1000000000000:ℝ) (3404235241017694811/500000000000000000:ℝ) (133996590813/50000000000000:ℝ) (33499220303/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0594).1 (thetaFirstMode_refined_node_0594).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0302 :
    (-86002182179226532373070808461/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (199/512:ℝ) ∧ thetaFirstModeFirst (199/512:ℝ) ≤ (-430009833253962321035977/12500000000000000000000000:ℝ) := by
  have hlo : (6835115906379/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(199/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(199/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(199/512:ℝ)) ≤ (543921354713/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(199/512:ℝ)) (by norm_num : 2*(199/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(199/512:ℝ)) ≤ (1708779520516877809/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (199/512:ℝ) (6835115906379/1000000000000:ℝ) (1708779520516877809/250000000000000000:ℝ) (65300267963/25000000000000:ℝ) (52240328029/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0595).1 (thetaFirstMode_refined_node_0595).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0303 :
    (-429886080618259761215196442893/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (86056132492075958991/221395846441879298560:ℝ) ∧ thetaFirstModeFirst (86056132492075958991/221395846441879298560:ℝ) ≤ (-859770006477222934550043/25000000000000000000000000:ℝ) := by
  have hlo : (3417736826957/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(86056132492075958991/221395846441879298560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(86056132492075958991/221395846441879298560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(86056132492075958991/221395846441879298560:ℝ)) ≤ (543949823363/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(86056132492075958991/221395846441879298560:ℝ)) (by norm_num : 2*(86056132492075958991/221395846441879298560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(86056132492075958991/221395846441879298560:ℝ)) ≤ (1708868957428437259/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (86056132492075958991/221395846441879298560:ℝ) (3417736826957/500000000000:ℝ) (1708868957428437259/250000000000000000:ℝ) (261111060999/100000000000000:ℝ) (261111629127/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0599).1 (thetaFirstMode_refined_node_0599).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0304 :
    (-1314910378613676273166924971/39062500000000000000000000000:ℝ) ≤ thetaFirstModeFirst (25/64:ℝ) ∧ thetaFirstModeFirst (25/64:ℝ) ≤ (-84154052621350608467613/2500000000000000000000000:ℝ) := by
  have hlo : (6861867793651/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(25/64:ℝ)) ≤ (34128137669/15625000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(25/64:ℝ)) (by norm_num : 2*(25/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(25/64:ℝ)) ≤ (107216718403966717/15625000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (25/64:ℝ) (6861867793651/1000000000000:ℝ) (107216718403966717/15625000000000000:ℝ) (12727727663/5000000000000:ℝ) (12727755463/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0600).1 (thetaFirstMode_refined_node_0600).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0305 :
    (-51460863410657600952315783453/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (201/512:ℝ) ∧ thetaFirstModeFirst (201/512:ℝ) ≤ (-32934869486208662412563/1000000000000000000000000:ℝ) := by
  have hlo : (137774487697/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(201/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(201/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(201/512:ℝ)) ≤ (1096374765541/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(201/512:ℝ)) (by norm_num : 2*(201/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(201/512:ℝ)) ≤ (3444363288800246813/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (201/512:ℝ) (137774487697/20000000000:ℝ) (3444363288800246813/500000000000000000:ℝ) (248051188579/100000000000000:ℝ) (15503233281/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0601).1 (thetaFirstMode_refined_node_0601).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0306 :
    (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (94159912870084059009/239834298071963906560:ℝ) ∧ thetaFirstModeFirst (94159912870084059009/239834298071963906560:ℝ) ≤ (-1646265587239499714783451/50000000000000000000000000:ℝ) := by
  have hlo : (6889081351461/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(94159912870084059009/239834298071963906560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(94159912870084059009/239834298071963906560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(94159912870084059009/239834298071963906560:ℝ)) ≤ (2192863157107/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(94159912870084059009/239834298071963906560:ℝ)) (by norm_num : 2*(94159912870084059009/239834298071963906560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(94159912870084059009/239834298071963906560:ℝ)) ≤ (6889083544325251451/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (94159912870084059009/239834298071963906560:ℝ) (6889081351461/1000000000000:ℝ) (6889083544325251451/1000000000000000000:ℝ) (247965870591/100000000000000:ℝ) (247966414349/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0605).1 (thetaFirstMode_refined_node_0605).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0307 :
    (-100689011870884134959010086427/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (101/256:ℝ) ∧ thetaFirstModeFirst (101/256:ℝ) ≤ (-64440804459626956072487/2000000000000000000000000:ℝ) := by
  have hlo : (276627443591/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(101/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(101/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(101/256:ℝ)) ≤ (1100665855047/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(101/256:ℝ)) (by norm_num : 2*(101/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(101/256:ℝ)) ≤ (3457844145554669871/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (101/256:ℝ) (276627443591/40000000000:ℝ) (3457844145554669871/500000000000000000:ℝ) (241688565857/100000000000000:ℝ) (30211137237/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0606).1 (thetaFirstMode_refined_node_0606).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0308 :
    (-393977117138436078554167413217/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (203/512:ℝ) ∧ thetaFirstModeFirst (203/512:ℝ) ≤ (-1575904465507159884915987/50000000000000000000000000:ℝ) := by
  have hlo : (6942753319829/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(203/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(203/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(203/512:ℝ)) ≤ (552486869701/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(203/512:ℝ)) (by norm_num : 2*(203/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(203/512:ℝ)) ≤ (1735688882444573693/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (203/512:ℝ) (6942753319829/1000000000000:ℝ) (1735688882444573693/250000000000000000:ℝ) (235464298503/100000000000000:ℝ) (235464818869/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0607).1 (thetaFirstMode_refined_node_0607).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0309 :
    (-393862812547991790702588742107/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (102935065125197358207/259602677601152028160:ℝ) ∧ thetaFirstModeFirst (102935065125197358207/259602677601152028160:ℝ) ≤ (-246163632520208527949/7812500000000000000000:ℝ) := by
  have hlo : (108486086601/15625000000:ℝ) ≤ Real.pi*Real.exp (2*(102935065125197358207/259602677601152028160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(102935065125197358207/259602677601152028160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(102935065125197358207/259602677601152028160:ℝ)) ≤ (1105030434007/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(102935065125197358207/259602677601152028160:ℝ)) (by norm_num : 2*(102935065125197358207/259602677601152028160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(102935065125197358207/259602677601152028160:ℝ)) ≤ (3471555876263353151/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (102935065125197358207/259602677601152028160:ℝ) (108486086601/15625000000:ℝ) (3471555876263353151/500000000000000000:ℝ) (2353834549/1000000000000:ℝ) (117691987557/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0611).1 (thetaFirstMode_refined_node_0611).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0310 :
    (-1541393956965029146921225289/50000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (51/128:ℝ) ∧ thetaFirstModeFirst (51/128:ℝ) ≤ (-77069501416659485884929/2500000000000000000000000:ℝ) := by
  have hlo : (3484963244013/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(51/128:ℝ)) ≤ (55464924217/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(51/128:ℝ)) (by norm_num : 2*(51/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(51/128:ℝ)) ≤ (174248217665657681/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (51/128:ℝ) (3484963244013/500000000000:ℝ) (174248217665657681/25000000000000000:ℝ) (22937602533/10000000000000:ℝ) (9175061369/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0612).1 (thetaFirstMode_refined_node_0612).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0311 :
    (-301494827854624757124523075599/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (205/512:ℝ) ∧ thetaFirstModeFirst (205/512:ℝ) ≤ (-1507470284078181177087227/50000000000000000000000000:ℝ) := by
  have hlo : (6997206008997/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(205/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(205/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(205/512:ℝ)) ≤ (2227280311701/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(205/512:ℝ)) (by norm_num : 2*(205/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(205/512:ℝ)) ≤ (6997208236277679693/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (205/512:ℝ) (6997206008997/1000000000000:ℝ) (6997208236277679693/1000000000000000000:ℝ) (223421410591/100000000000000:ℝ) (44684381643/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0613).1 (thetaFirstMode_refined_node_0613).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0312 :
    (-5886862690187487516232156083/195312500000000000000000000000:ℝ) ≤ thetaFirstModeFirst (22485952682885662245/56156474985950039552:ℝ) ∧ thetaFirstModeFirst (22485952682885662245/56156474985950039552:ℝ) ≤ (-1507032994439353546729939/50000000000000000000000000:ℝ) := by
  have hlo : (6997561523691/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(22485952682885662245/56156474985950039552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(22485952682885662245/56156474985950039552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(22485952682885662245/56156474985950039552:ℝ)) ≤ (2227393475567/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(22485952682885662245/56156474985950039552:ℝ)) (by norm_num : 2*(22485952682885662245/56156474985950039552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(22485952682885662245/56156474985950039552:ℝ)) ≤ (6997563751086958231/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (22485952682885662245/56156474985950039552:ℝ) (6997561523691/1000000000000:ℝ) (6997563751086958231/1000000000000000000:ℝ) (223344831929/100000000000000:ℝ) (872442693/390625000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0617).1 (thetaFirstMode_refined_node_0617).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0313 :
    (-1474142493352870903413065561681/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (103/256:ℝ) ∧ thetaFirstModeFirst (103/256:ℝ) ≤ (-11516708676701464587/390625000000000000000:ℝ) := by
  have hlo : (3512296149497/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(103/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(103/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(103/256:ℝ)) ≤ (2235997640367/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(103/256:ℝ)) (by norm_num : 2*(103/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(103/256:ℝ)) ≤ (7024594534993484631/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (103/256:ℝ) (3512296149497/500000000000:ℝ) (7024594534993484631/1000000000000000000:ℝ) (3399971/1562500000:ℝ) (217598630551/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0618).1 (thetaFirstMode_refined_node_0618).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0314 :
    (-90087030785128384978472129951/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (207/512:ℝ) ∧ thetaFirstModeFirst (207/512:ℝ) ≤ (-1441388781320946589070937/50000000000000000000000000:ℝ) := by
  have hlo : (7052085775899/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(207/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(207/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(207/512:ℝ)) ≤ (561187271923/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(207/512:ℝ)) (by norm_num : 2*(207/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(207/512:ℝ)) ≤ (1763022005162393339/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (207/512:ℝ) (7052085775899/1000000000000:ℝ) (1763022005162393339/250000000000000000:ℝ) (211903940763/100000000000000:ℝ) (52976104109/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0619).1 (thetaFirstMode_refined_node_0619).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0315 :
    (-180121801082870474100554348559/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (122695115016799804743/303458889196134300160:ℝ) ∧ thetaFirstModeFirst (122695115016799804743/303458889196134300160:ℝ) ≤ (-1440970698330735348269001/50000000000000000000000000:ℝ) := by
  have hlo : (7052440617811/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(122695115016799804743/303458889196134300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(122695115016799804743/303458889196134300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(122695115016799804743/303458889196134300160:ℝ)) ≤ (561215509351/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(122695115016799804743/303458889196134300160:ℝ)) (by norm_num : 2*(122695115016799804743/303458889196134300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(122695115016799804743/303458889196134300160:ℝ)) ≤ (1763110715668536143/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (122695115016799804743/303458889196134300160:ℝ) (7052440617811/1000000000000:ℝ) (1763110715668536143/250000000000000000:ℝ) (211831426291/100000000000000:ℝ) (105915950913/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0623).1 (thetaFirstMode_refined_node_0623).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0316 :
    (-704608803669548152540724394021/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13/32:ℝ) ∧ thetaFirstModeFirst (13/32:ℝ) ≤ (-70460698331077493775093/2500000000000000000000000:ℝ) := by
  have hlo : (707968685923/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13/32:ℝ)) ≤ (1126767393607/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13/32:ℝ)) (by norm_num : 2*(13/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13/32:ℝ)) ≤ (3539844556383995951/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13/32:ℝ) (707968685923/100000000000:ℝ) (3539844556383995951/500000000000000000:ℝ) (103168270791/50000000000000:ℝ) (206337006571/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0624).1 (thetaFirstMode_refined_node_0624).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0317 :
    (-1377611306851432212374207969721/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (209/512:ℝ) ∧ thetaFirstModeFirst (209/512:ℝ) ≤ (-43050241740776315862587/1562500000000000000000000:ℝ) := by
  have hlo : (7107395970147/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(209/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(209/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(209/512:ℝ)) ≤ (2262354872991/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(209/512:ℝ)) (by norm_num : 2*(209/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(209/512:ℝ)) ≤ (7107398232504414663/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (209/512:ℝ) (7107395970147/1000000000000:ℝ) (7107398232504414663/1000000000000000000:ℝ) (6277928521/3125000000000:ℝ) (200894167167/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0625).1 (thetaFirstMode_refined_node_0625).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0318 :
    (-344302932232714622490896993499/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (133785307673187732441/327721993105999567360:ℝ) ∧ thetaFirstModeFirst (133785307673187732441/327721993105999567360:ℝ) ≤ (-1377208158661184126683593/50000000000000000000000000:ℝ) := by
  have hlo : (7107750173593/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(133785307673187732441/327721993105999567360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(133785307673187732441/327721993105999567360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(133785307673187732441/327721993105999567360:ℝ)) ≤ (2262467619473/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(133785307673187732441/327721993105999567360:ℝ)) (by norm_num : 2*(133785307673187732441/327721993105999567360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(133785307673187732441/327721993105999567360:ℝ)) ≤ (7107752436063040489/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (133785307673187732441/327721993105999567360:ℝ) (7107750173593/1000000000000:ℝ) (7107752436063040489/1000000000000000000:ℝ) (200825070001/100000000000000:ℝ) (50206381091/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0629).1 (thetaFirstMode_refined_node_0629).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0319 :
    (-84160441287669287987253127539/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (105/256:ℝ) ∧ thetaFirstModeFirst (105/256:ℝ) ≤ (-168320444758796508874031/6250000000000000000000000:ℝ) := by
  have hlo : (3567606765729/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(105/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(105/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(105/256:ℝ)) ≤ (283901184951/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(105/256:ℝ)) (by norm_num : 2*(105/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(105/256:ℝ)) ≤ (891901975333766943/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (105/256:ℝ) (3567606765729/500000000000:ℝ) (891901975333766943/125000000000000000:ℝ) (48893311439/25000000000000:ℝ) (97786844973/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0630).1 (thetaFirstMode_refined_node_0630).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

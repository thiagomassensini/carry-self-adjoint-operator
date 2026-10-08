import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0064 :
    (-361660334941576353186998236619/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/64:ℝ) ∧ thetaFirstModeFirst (5/64:ℝ) ≤ (-4520747357357885407258953/12500000000000000000000000:ℝ) := by
  have hlo : (1836446578769/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/64:ℝ)) ≤ (116911844617/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/64:ℝ)) (by norm_num : 2*(5/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/64:ℝ)) ≤ (367289432665854881/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/64:ℝ) (1836446578769/500000000000:ℝ) (367289432665854881/100000000000000000:ℝ) (2641477340537/50000000000000:ℝ) (1056592171499/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0120).1 (thetaFirstMode_refined_node_0120).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0065 :
    (-2239659568736071574608134543519/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (41/512:ℝ) ∧ thetaFirstModeFirst (41/512:ℝ) ≤ (-1119828087648232286063499/3125000000000000000000000:ℝ) := by
  have hlo : (921817113727/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(41/512:ℝ)) ≤ (146711780799/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(41/512:ℝ)) (by norm_num : 2*(41/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(41/512:ℝ)) ≤ (460908703575672807/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (41/512:ℝ) (921817113727/250000000000:ℝ) (460908703575672807/125000000000000000:ℝ) (1303160462837/25000000000000:ℝ) (5212647969417/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0121).1 (thetaFirstMode_refined_node_0121).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0066 :
    (-17906546596936770385379007934871/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (57958928803809/722636919247360:ℝ) ∧ thetaFirstModeFirst (57958928803809/722636919247360:ℝ) ≤ (-716260778419082893377381/2000000000000000000000000:ℝ) := by
  have hlo : (3688202530633/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(57958928803809/722636919247360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57958928803809/722636919247360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(57958928803809/722636919247360:ℝ)) ≤ (1173991571991/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(57958928803809/722636919247360:ℝ)) (by norm_num : 2*(57958928803809/722636919247360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(57958928803809/722636919247360:ℝ)) ≤ (3688203704625921663/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (57958928803809/722636919247360:ℝ) (3688202530633/1000000000000:ℝ) (3688203704625921663/1000000000000000000:ℝ) (208324196157/4000000000000:ℝ) (5208111018217/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0125).1 (thetaFirstMode_refined_node_0125).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0067 :
    (-17752035495265020844685534732763/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21/256:ℝ) ∧ thetaFirstModeFirst (21/256:ℝ) ≤ (-8876004259149810710137793/25000000000000000000000000:ℝ) := by
  have hlo : (1850850007801/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21/256:ℝ)) ≤ (1178287955789/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21/256:ℝ)) (by norm_num : 2*(21/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21/256:ℝ)) ≤ (3701701193891031877/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21/256:ℝ) (1850850007801/500000000000:ℝ) (3701701193891031877/1000000000000000000:ℝ) (5142975472393/100000000000000:ℝ) (5142981532319/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0126).1 (thetaFirstMode_refined_node_0126).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0068 :
    (-17587304099792114740611883375833/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (43/512:ℝ) ∧ thetaFirstModeFirst (43/512:ℝ) ≤ (-4396819323433717825048221/12500000000000000000000000:ℝ) := by
  have hlo : (1858094029913/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(43/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(43/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(43/512:ℝ)) ≤ (1182899644457/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(43/512:ℝ)) (by norm_num : 2*(43/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(43/512:ℝ)) ≤ (3716189242728600001/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (43/512:ℝ) (1858094029913/500000000000:ℝ) (3716189242728600001/1000000000000000000:ℝ) (2536976786917/50000000000000:ℝ) (5073959575833/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0127).1 (thetaFirstMode_refined_node_0127).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0069 :
    (-17165169357063551396899444949/48828125000000000000000000000:ℝ) ≤ thetaFirstModeFirst (88920376319007/1057252278300160:ℝ) ∧ thetaFirstModeFirst (88920376319007/1057252278300160:ℝ) ≤ (-8788553313087453524808657/25000000000000000000000000:ℝ) := by
  have hlo : (3717085917997/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(88920376319007/1057252278300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(88920376319007/1057252278300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(88920376319007/1057252278300160:ℝ)) ≤ (73949090103/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(88920376319007/1057252278300160:ℝ)) (by norm_num : 2*(88920376319007/1057252278300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(88920376319007/1057252278300160:ℝ)) ≤ (232317943823954079/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (88920376319007/1057252278300160:ℝ) (3717085917997/1000000000000:ℝ) (232317943823954079/62500000000000000:ℝ) (2534853049781/50000000000000:ℝ) (79214251531/1562500000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0131).1 (thetaFirstMode_refined_node_0131).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0070 :
    (-4355773196367319557647851525227/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11/128:ℝ) ∧ thetaFirstModeFirst (11/128:ℝ) ≤ (-8711533075352220084728313/25000000000000000000000000:ℝ) := by
  have hlo : (3730732808653/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11/128:ℝ)) ≤ (296882345691/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11/128:ℝ)) (by norm_num : 2*(11/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11/128:ℝ)) ≤ (932683499046425763/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11/128:ℝ) (3730732808653/1000000000000:ℝ) (932683499046425763/250000000000000000:ℝ) (2502787072221/50000000000000:ℝ) (5005580088729/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0132).1 (thetaFirstMode_refined_node_0132).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0071 :
    (-8629705938981589375864885818867/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (45/512:ℝ) ∧ thetaFirstModeFirst (45/512:ℝ) ≤ (-4314846353712531568004921/12500000000000000000000000:ℝ) := by
  have hlo : (3745334484017/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(45/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(45/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(45/512:ℝ)) ≤ (596088620677/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(45/512:ℝ)) (by norm_num : 2*(45/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(45/512:ℝ)) ≤ (1872667838098518461/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (45/512:ℝ) (3745334484017/1000000000000:ℝ) (1872667838098518461/500000000000000000:ℝ) (1234458783113/25000000000000:ℝ) (4937841019247/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0133).1 (thetaFirstMode_refined_node_0133).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0072 :
    (-539054799777053651949066501611/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (26759859160005/304068323159552:ℝ) ∧ thetaFirstModeFirst (26759859160005/304068323159552:ℝ) ≤ (-539053973122316164202853/1562500000000000000000000:ℝ) := by
  have hlo : (468274921181/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(26759859160005/304068323159552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(26759859160005/304068323159552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(26759859160005/304068323159552:ℝ)) ≤ (596226271497/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(26759859160005/304068323159552:ℝ)) (by norm_num : 2*(26759859160005/304068323159552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(26759859160005/304068323159552:ℝ)) ≤ (1873100280951074721/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (26759859160005/304068323159552:ℝ) (468274921181/125000000000:ℝ) (1873100280951074721/500000000000000000:ℝ) (1233462777513/25000000000000:ℝ) (308366062091/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0137).1 (thetaFirstMode_refined_node_0137).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0073 :
    (-170962716049636727657775915129/500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (23/256:ℝ) ∧ thetaFirstModeFirst (23/256:ℝ) ≤ (-341924906277022574140437/1000000000000000000000000:ℝ) := by
  have hlo : (3759993308723/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(23/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(23/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(23/256:ℝ)) ≤ (299210822787/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(23/256:ℝ)) (by norm_num : 2*(23/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(23/256:ℝ)) ≤ (939998626391879691/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (23/256:ℝ) (3759993308723/1000000000000:ℝ) (939998626391879691/250000000000000000:ℝ) (97414688919/2000000000000:ℝ) (194829611019/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0138).1 (thetaFirstMode_refined_node_0138).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0074 :
    (-3386736418914325447832897998429/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (47/512:ℝ) ∧ thetaFirstModeFirst (47/512:ℝ) ≤ (-1693365597577077854118173/5000000000000000000000000:ℝ) := by
  have hlo : (1887354753223/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(47/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(47/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(47/512:ℝ)) ≤ (240305520669/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(47/512:ℝ)) (by norm_num : 2*(47/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(47/512:ℝ)) ≤ (754942141595085717/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (47/512:ℝ) (1887354753223/500000000000:ℝ) (754942141595085717/200000000000000000:ℝ) (960853990651/20000000000000:ℝ) (4804275725737/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0139).1 (thetaFirstMode_refined_node_0139).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0075 :
    (-1057780950135906067691419812753/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (197791827765543/2152076489628160:ℝ) ∧ thetaFirstModeFirst (197791827765543/2152076489628160:ℝ) ≤ (-16924469093139939935275749/50000000000000000000000000:ℝ) := by
  have hlo : (3775544254359/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(197791827765543/2152076489628160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(197791827765543/2152076489628160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(197791827765543/2152076489628160:ℝ)) ≤ (1201793311913/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(197791827765543/2152076489628160:ℝ)) (by norm_num : 2*(197791827765543/2152076489628160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(197791827765543/2152076489628160:ℝ)) ≤ (3775545456152697409/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (197791827765543/2152076489628160:ℝ) (3775544254359/1000000000000:ℝ) (3775545456152697409/1000000000000000000:ℝ) (4800526634211/100000000000000:ℝ) (300033275217/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0143).1 (thetaFirstMode_refined_node_0143).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0076 :
    (-3354330674754989163504677392359/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/32:ℝ) ∧ thetaFirstModeFirst (3/32:ℝ) ≤ (-8385813713801371213578543/25000000000000000000000000:ℝ) := by
  have hlo : (1894741650869/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/32:ℝ)) ≤ (1206230249421/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/32:ℝ)) (by norm_num : 2*(3/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/32:ℝ)) ≤ (3789484507969267653/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/32:ℝ) (1894741650869/500000000000:ℝ) (3789484507969267653/1000000000000000000:ℝ) (4738439483347/100000000000000:ℝ) (947689039803/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0144).1 (thetaFirstMode_refined_node_0144).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0077 :
    (-8305097683365795115386537405221/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (49/512:ℝ) ∧ thetaFirstModeFirst (49/512:ℝ) ≤ (-3322033918695685788842471/10000000000000000000000000:ℝ) := by
  have hlo : (3804314920031/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(49/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(49/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(49/512:ℝ)) ≤ (605475650567/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(49/512:ℝ)) (by norm_num : 2*(49/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(49/512:ℝ)) ≤ (1902158065491733231/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (49/512:ℝ) (3804314920031/1000000000000:ℝ) (1902158065491733231/500000000000000000:ℝ) (934648165241/20000000000000:ℝ) (4673246485291/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0145).1 (thetaFirstMode_refined_node_0145).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0078 :
    (-2075180474702186732546994589167/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (287676456077241/3002597697026560:ℝ) ∧ thetaFirstModeFirst (287676456077241/3002597697026560:ℝ) ≤ (-8300709016879730957803323/25000000000000000000000000:ℝ) := by
  have hlo : (3805122022127/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(287676456077241/3002597697026560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(287676456077241/3002597697026560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(287676456077241/3002597697026560:ℝ)) ≤ (302802052441/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(287676456077241/3002597697026560:ℝ)) (by norm_num : 2*(287676456077241/3002597697026560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(287676456077241/3002597697026560:ℝ)) ≤ (951280808334278513/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (287676456077241/3002597697026560:ℝ) (3805122022127/1000000000000:ℝ) (951280808334278513/250000000000000000:ℝ) (2334859103349/50000000000000:ℝ) (2334861931359/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0149).1 (thetaFirstMode_refined_node_0149).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0079 :
    (-16449317893361112351679343767483/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (25/256:ℝ) ∧ thetaFirstModeFirst (25/256:ℝ) ≤ (-514040384165711816907031/1562500000000000000000000:ℝ) := by
  have hlo : (954801146909/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(25/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(25/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(25/256:ℝ)) ≤ (1215690830521/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(25/256:ℝ)) (by norm_num : 2*(25/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(25/256:ℝ)) ≤ (3819205803328959953/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (25/256:ℝ) (954801146909/250000000000:ℝ) (3819205803328959953/1000000000000000000:ℝ) (576083966659/12500000000000:ℝ) (4608677336011/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0150).1 (thetaFirstMode_refined_node_0150).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0080 :
    (-3257806133546102339242734733649/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (51/512:ℝ) ∧ thetaFirstModeFirst (51/512:ℝ) ≤ (-4072251310286375767761627/12500000000000000000000000:ℝ) := by
  have hlo : (3834152531753/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(51/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(51/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(51/512:ℝ)) ≤ (1220448909901/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(51/512:ℝ)) (by norm_num : 2*(51/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(51/512:ℝ)) ≤ (3834153752202612293/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (51/512:ℝ) (3834152531753/1000000000000:ℝ) (3834153752202612293/1000000000000000000:ℝ) (1136182479459/25000000000000:ℝ) (908947092893/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0151).1 (thetaFirstMode_refined_node_0151).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0081 :
    (-4070170629264855917271108380431/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (412196976114759/4133904418178560:ℝ) ∧ thetaFirstModeFirst (412196976114759/4133904418178560:ℝ) ≤ (-407016427488239636775021/1250000000000000000000000:ℝ) := by
  have hlo : (766986837901/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(412196976114759/4133904418178560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(412196976114759/4133904418178560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(412196976114759/4133904418178560:ℝ)) ≤ (1220697719343/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(412196976114759/4133904418178560:ℝ)) (by norm_num : 2*(412196976114759/4133904418178560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(412196976114759/4133904418178560:ℝ)) ≤ (3834935410203933399/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (412196976114759/4133904418178560:ℝ) (766986837901/200000000000:ℝ) (3834935410203933399/1000000000000000000:ℝ) (567676289121/12500000000000:ℝ) (1135353964169/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0155).1 (thetaFirstMode_refined_node_0155).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0082 :
    (-1008083956031021889749993571771/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13/128:ℝ) ∧ thetaFirstModeFirst (13/128:ℝ) ≤ (-4032329510903057364619491/12500000000000000000000000:ℝ) := by
  have hlo : (962289745117/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13/128:ℝ)) ≤ (612612805939/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13/128:ℝ)) (by norm_num : 2*(13/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13/128:ℝ)) ≤ (1924580102848320827/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13/128:ℝ) (962289745117/250000000000:ℝ) (1924580102848320827/500000000000000000:ℝ) (4481413055423/100000000000000:ℝ) (560177318273/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0156).1 (thetaFirstMode_refined_node_0156).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0083 :
    (-499070789923779861225186312737/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (53/512:ℝ) ∧ thetaFirstModeFirst (53/512:ℝ) ≤ (-3992560049659117735503699/12500000000000000000000000:ℝ) := by
  have hlo : (966056040691/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(53/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(53/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(53/512:ℝ)) ≤ (1230021009337/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(53/512:ℝ)) (by norm_num : 2*(53/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(53/512:ℝ)) ≤ (3864225392786053841/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (53/512:ℝ) (966056040691/250000000000:ℝ) (3864225392786053841/1000000000000000000:ℝ) (4418718784289/100000000000000:ℝ) (138085131857/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0157).1 (thetaFirstMode_refined_node_0157).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0084 :
    (-7981146090705086483937391636031/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (582516327971457/5622000143388160:ℝ) ∧ thetaFirstModeFirst (582516327971457/5622000143388160:ℝ) ≤ (-7981133555609740184100351/25000000000000000000000000:ℝ) := by
  have hlo : (1932491165389/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(582516327971457/5622000143388160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(582516327971457/5622000143388160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(582516327971457/5622000143388160:ℝ)) ≤ (615131170881/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(582516327971457/5622000143388160:ℝ)) (by norm_num : 2*(582516327971457/5622000143388160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(582516327971457/5622000143388160:ℝ)) ≤ (1932491780521553433/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (582516327971457/5622000143388160:ℝ) (1932491165389/500000000000:ℝ) (1932491780521553433/500000000000000000:ℝ) (4415586481659/100000000000000:ℝ) (4415591914007/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0161).1 (thetaFirstMode_refined_node_0161).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0085 :
    (-3952951499596753853535160500813/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (27/256:ℝ) ∧ thetaFirstModeFirst (27/256:ℝ) ≤ (-3162356218723644348553953/10000000000000000000000000:ℝ) := by
  have hlo : (775869661703/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(27/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(27/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(27/256:ℝ)) ≤ (308708793863/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(27/256:ℝ)) (by norm_num : 2*(27/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(27/256:ℝ)) ≤ (969837385838443759/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (27/256:ℝ) (775869661703/200000000000:ℝ) (969837385838443759/250000000000000000:ℝ) (4356644705751/100000000000000:ℝ) (4356650085507/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0162).1 (thetaFirstMode_refined_node_0162).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0086 :
    (-195674684185220794771137344449/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (55/512:ℝ) ∧ thetaFirstModeFirst (55/512:ℝ) ≤ (-15653950004432657253999/50000000000000000000000:ℝ) := by
  have hlo : (7789063297/2000000000:ℝ) ≤ Real.pi*Real.exp (2*(55/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(55/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(55/512:ℝ)) ≤ (1239668183679/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(55/512:ℝ)) (by norm_num : 2*(55/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(55/512:ℝ)) ≤ (3894532888168660647/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (55/512:ℝ) (7789063297/2000000000:ℝ) (3894532888168660647/1000000000000000000:ℝ) (2147594192367/50000000000000:ℝ) (53689921367/1250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0163).1 (thetaFirstMode_refined_node_0163).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0087 :
    (-15646351358747945089036909024981/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (162550142281395/1511863535831552:ℝ) ∧ thetaFirstModeFirst (162550142281395/1511863535831552:ℝ) ≤ (-488947707399677436678479/1562500000000000000000000:ℝ) := by
  have hlo : (3895268070089/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(162550142281395/1511863535831552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(162550142281395/1511863535831552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(162550142281395/1511863535831552:ℝ)) ≤ (1239902594001/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(162550142281395/1511863535831552:ℝ)) (by norm_num : 2*(162550142281395/1511863535831552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(162550142281395/1511863535831552:ℝ)) ≤ (3895269309995383593/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (162550142281395/1511863535831552:ℝ) (3895268070089/1000000000000:ℝ) (3895269309995383593/1000000000000000000:ℝ) (134132167511/3125000000000:ℝ) (4292234682317/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0167).1 (thetaFirstMode_refined_node_0167).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0088 :
    (-7748390324661775555415589013703/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/64:ℝ) ∧ thetaFirstModeFirst (7/64:ℝ) ≤ (-7748378046742600601136483/25000000000000000000000000:ℝ) := by
  have hlo : (3909774414397/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/64:ℝ)) ≤ (1244520107767/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/64:ℝ)) (by norm_num : 2*(7/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/64:ℝ)) ≤ (3909775658920052831/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/64:ℝ) (3909774414397/1000000000000:ℝ) (3909775658920052831/1000000000000000000:ℝ) (2117173675039/50000000000000:ℝ) (2117176309913/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0168).1 (thetaFirstMode_refined_node_0168).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0089 :
    (-3835058197494205723356525268673/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (57/512:ℝ) ∧ thetaFirstModeFirst (57/512:ℝ) ≤ (-1917526051108501105680521/6250000000000000000000000:ℝ) := by
  have hlo : (490634604849/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(57/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(57/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(57/512:ℝ)) ≤ (312347755437/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(57/512:ℝ)) (by norm_num : 2*(57/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(57/512:ℝ)) ≤ (981269522046591141/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (57/512:ℝ) (490634604849/125000000000:ℝ) (981269522046591141/250000000000000000:ℝ) (4174119095129/100000000000000:ℝ) (4174124310253/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0169).1 (thetaFirstMode_refined_node_0169).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0090 :
    (-1533293640647615142773545556563/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1120594199442993/10057446457500160:ℝ) ∧ thetaFirstModeFirst (1120594199442993/10057446457500160:ℝ) ≤ (-15332912033537061235226781/50000000000000000000000000:ℝ) := by
  have hlo : (3925793075371/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1120594199442993/10057446457500160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1120594199442993/10057446457500160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1120594199442993/10057446457500160:ℝ)) ≤ (1249619006979/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1120594199442993/10057446457500160:ℝ)) (by norm_num : 2*(1120594199442993/10057446457500160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1120594199442993/10057446457500160:ℝ)) ≤ (3925794324992177547/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1120594199442993/10057446457500160:ℝ) (3925793075371/1000000000000:ℝ) (3925794324992177547/1000000000000000000:ℝ) (4171320778711/100000000000000:ℝ) (417132599129/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0173).1 (thetaFirstMode_refined_node_0173).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0091 :
    (-1518434008878023581873606322193/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (29/256:ℝ) ∧ thetaFirstModeFirst (29/256:ℝ) ≤ (-118627467832528819590041/390625000000000000000000:ℝ) := by
  have hlo : (246277447199/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(29/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(29/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(29/256:ℝ)) ≤ (1254280999947/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(29/256:ℝ)) (by norm_num : 2*(29/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(29/256:ℝ)) ≤ (3940440409466495571/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (29/256:ℝ) (246277447199/62500000000:ℝ) (3940440409466495571/1000000000000000000:ℝ) (514312634759/12500000000000:ℝ) (411450623883/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0174).1 (thetaFirstMode_refined_node_0174).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0092 :
    (-751455568020676307891379727017/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (59/512:ℝ) ∧ thetaFirstModeFirst (59/512:ℝ) ≤ (-751454366461280770506813/2500000000000000000000000:ℝ) := by
  have hlo : (1977930798991/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(59/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(59/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(59/512:ℝ)) ≤ (62959505849/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(59/512:ℝ)) (by norm_num : 2*(59/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(59/512:ℝ)) ≤ (197793142858677457/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (59/512:ℝ) (1977930798991/500000000000:ℝ) (197793142858677457/50000000000000000:ℝ) (405549072243/10000000000000:ℝ) (4055495829081/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0175).1 (thetaFirstMode_refined_node_0175).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0093 :
    (-15022121497051294181088011800497/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1528044900298191/13250186301775360:ℝ) ∧ thetaFirstModeFirst (1528044900298191/13250186301775360:ℝ) ≤ (-1877762184220205621911281/6250000000000000000000000:ℝ) := by
  have hlo : (3956559053531/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1528044900298191/13250186301775360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1528044900298191/13250186301775360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1528044900298191/13250186301775360:ℝ)) ≤ (1259412124023/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1528044900298191/13250186301775360:ℝ)) (by norm_num : 2*(1528044900298191/13250186301775360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1528044900298191/13250186301775360:ℝ)) ≤ (3956560312945788639/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1528044900298191/13250186301775360:ℝ) (3956559053531/1000000000000:ℝ) (3956560312945788639/1000000000000000000:ℝ) (506605225251/12500000000000:ℝ) (4052846906223/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0179).1 (thetaFirstMode_refined_node_0179).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0094 :
    (-929659706310126709638653724373/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15/128:ℝ) ∧ thetaFirstModeFirst (15/128:ℝ) ≤ (-3718632861231342706722633/12500000000000000000000000:ℝ) := by
  have hlo : (1985672201257/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15/128:ℝ)) ≤ (632059223877/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15/128:ℝ)) (by norm_num : 2*(15/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15/128:ℝ)) ≤ (1985672833317416061/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15/128:ℝ) (1985672201257/500000000000:ℝ) (1985672833317416061/500000000000000000:ℝ) (1998542708769/50000000000000:ℝ) (499636308793/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0180).1 (thetaFirstMode_refined_node_0180).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0095 :
    (-14720680486578698854862008406091/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (61/512:ℝ) ∧ thetaFirstModeFirst (61/512:ℝ) ≤ (-1472065680580774860715491/5000000000000000000000000:ℝ) := by
  have hlo : (398688780503/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(61/512:ℝ)) ≤ (1269066067469/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(61/512:ℝ)) (by norm_num : 2*(61/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(61/512:ℝ)) ≤ (3986889074098138117/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (61/512:ℝ) (398688780503/100000000000:ℝ) (3986889074098138117/1000000000000000000:ℝ) (3939282518997/100000000000000:ℝ) (3939287518223/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0181).1 (thetaFirstMode_refined_node_0181).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

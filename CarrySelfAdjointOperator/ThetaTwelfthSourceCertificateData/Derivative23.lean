import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0736 :
    (-445236229421342117894889/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (61/64:ℝ) ∧ thetaFirstModeFirst (61/64:ℝ) ≤ (-4452298201895901063/50000000000000000000000000:ℝ) := by
  have hlo : (21136040793053/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(61/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(61/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(61/64:ℝ)) ≤ (1345562427779/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(61/64:ℝ)) (by norm_num : 2*(61/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(61/64:ℝ)) ≤ (4227209504173511947/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (61/64:ℝ) (21136040793053/1000000000000:ℝ) (4227209504173511947/200000000000000000:ℝ) (213171/100000000000000:ℝ) (106587/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1464).1 (thetaFirstMode_refined_node_1464).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0737 :
    (-514890809500327785566531/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (489/512:ℝ) ∧ thetaFirstModeFirst (489/512:ℝ) ≤ (-257441390182281899/3125000000000000000000000:ℝ) := by
  have hlo : (2652345614721/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(489/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(489/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(489/512:ℝ)) ≤ (844268006387/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(489/512:ℝ)) (by norm_num : 2*(489/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(489/512:ℝ)) ≤ (2652346458989354491/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (489/512:ℝ) (2652345614721/125000000000:ℝ) (2652346458989354491/125000000000000000:ℝ) (98219/50000000000000:ℝ) (196441/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1465).1 (thetaFirstMode_refined_node_1465).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0738 :
    (-51467124688020112266333/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (281043842605185699355041/294259392150867570741760:ℝ) ∧ thetaFirstModeFirst (281043842605185699355041/294259392150867570741760:ℝ) ≤ (-2058663355191261909/25000000000000000000000000:ℝ) := by
  have hlo : (10609608457259/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(281043842605185699355041/294259392150867570741760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(281043842605185699355041/294259392150867570741760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(281043842605185699355041/294259392150867570741760:ℝ)) ≤ (84428599077/12500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(281043842605185699355041/294259392150867570741760:ℝ)) (by norm_num : 2*(281043842605185699355041/294259392150867570741760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(281043842605185699355041/294259392150867570741760:ℝ)) ≤ (265240295860109661/12500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (281043842605185699355041/294259392150867570741760:ℝ) (10609608457259/500000000000:ℝ) (265240295860109661/12500000000000000:ℝ) (196351/100000000000000:ℝ) (196353/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1469).1 (thetaFirstMode_refined_node_1469).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0739 :
    (-1904789688877763790284471/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (245/256:ℝ) ∧ thetaFirstModeFirst (245/256:ℝ) ≤ (-23809600294390443/312500000000000000000000:ℝ) := by
  have hlo : (21301812815553/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(245/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(245/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(245/256:ℝ)) ≤ (6780579023487/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(245/256:ℝ)) (by norm_num : 2*(245/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(245/256:ℝ)) ≤ (21301819596133594791/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (245/256:ℝ) (21301812815553/1000000000000:ℝ) (21301819596133594791/1000000000000000000:ℝ) (1131/625000000000:ℝ) (90481/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1470).1 (thetaFirstMode_refined_node_1470).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0740 :
    (-704431741010911388144159/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (491/512:ℝ) ∧ thetaFirstModeFirst (491/512:ℝ) ≤ (-3522115300283345493/50000000000000000000000000:ℝ) := by
  have hlo : (21385185753619/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(491/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(491/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(491/512:ℝ)) ≤ (1361423491887/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(491/512:ℝ)) (by norm_num : 2*(491/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(491/512:ℝ)) ≤ (4277038512147755991/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (491/512:ℝ) (21385185753619/1000000000000:ℝ) (4277038512147755991/200000000000000000:ℝ) (166647/100000000000000:ℝ) (166649/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1471).1 (thetaFirstMode_refined_node_1471).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0741 :
    (-70413405472474475513691/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (291559767057868215806559/304026373876319976271360:ℝ) ∧ thetaFirstModeFirst (291559767057868215806559/304026373876319976271360:ℝ) ≤ (-704125373684992259/10000000000000000000000000:ℝ) := by
  have hlo : (4277127887983/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(291559767057868215806559/304026373876319976271360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(291559767057868215806559/304026373876319976271360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(291559767057868215806559/304026373876319976271360:ℝ)) ≤ (3403630936149/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(291559767057868215806559/304026373876319976271360:ℝ)) (by norm_num : 2*(291559767057868215806559/304026373876319976271360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(291559767057868215806559/304026373876319976271360:ℝ)) ≤ (10692823123589145357/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (291559767057868215806559/304026373876319976271360:ℝ) (4277127887983/200000000000:ℝ) (10692823123589145357/500000000000000000:ℝ) (166573/100000000000000:ℝ) (6663/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1475).1 (thetaFirstMode_refined_node_1475).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0742 :
    (-813845291719680726809457/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (123/128:ℝ) ∧ thetaFirstModeFirst (123/128:ℝ) ≤ (-3255337680679992963/50000000000000000000000000:ℝ) := by
  have hlo : (21468885004139/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(123/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(123/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(123/128:ℝ)) ≤ (1708439940971/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(123/128:ℝ)) (by norm_num : 2*(123/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(123/128:ℝ)) ≤ (5367222959474906803/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (123/128:ℝ) (21468885004139/1000000000000:ℝ) (5367222959474906803/250000000000000000:ℝ) (153417/100000000000000:ℝ) (153419/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1476).1 (thetaFirstMode_refined_node_1476).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0743 :
    (-75195042444100959754761/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (493/512:ℝ) ∧ thetaFirstModeFirst (493/512:ℝ) ≤ (-150387906164567589/2500000000000000000000000:ℝ) := by
  have hlo : (10776455922131/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(493/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(493/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(493/512:ℝ)) ≤ (1372101268673/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(493/512:ℝ)) (by norm_num : 2*(493/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(493/512:ℝ)) ≤ (4310583740954216089/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (493/512:ℝ) (10776455922131/500000000000:ℝ) (4310583740954216089/200000000000000000:ℝ) (14119/10000000000000:ℝ) (17649/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1477).1 (thetaFirstMode_refined_node_1477).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0744 :
    (-375812822403357945730059/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (302424007419219829279257/314075847828315644700160:ℝ) ∧ thetaFirstModeFirst (302424007419219829279257/314075847828315644700160:ℝ) ≤ (-60129180085239117/1000000000000000000000000:ℝ) := by
  have hlo : (862134689359/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(302424007419219829279257/314075847828315644700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(302424007419219829279257/314075847828315644700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(302424007419219829279257/314075847828315644700160:ℝ)) ≤ (6860651298443/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(302424007419219829279257/314075847828315644700160:ℝ)) (by norm_num : 2*(302424007419219829279257/314075847828315644700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(302424007419219829279257/314075847828315644700160:ℝ)) ≤ (21553374094629439699/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (302424007419219829279257/314075847828315644700160:ℝ) (862134689359/40000000000:ℝ) (21553374094629439699/1000000000000000000:ℝ) (70563/50000000000000:ℝ) (17641/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1481).1 (thetaFirstMode_refined_node_1481).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0745 :
    (-1389071394193664609057079/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (247/256:ℝ) ∧ thetaFirstModeFirst (247/256:ℝ) ≤ (-27780991192048053/500000000000000000000000:ℝ) := by
  have hlo : (1081863377807/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(247/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(247/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(247/256:ℝ)) ≤ (3443678802999/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(247/256:ℝ)) (by norm_num : 2*(247/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(247/256:ℝ)) ≤ (10818637221750037407/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (247/256:ℝ) (1081863377807/50000000000:ℝ) (10818637221750037407/500000000000000000:ℝ) (25979/20000000000000:ℝ) (129897/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1482).1 (thetaFirstMode_refined_node_1482).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0746 :
    (-641292303532150777396419/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (495/512:ℝ) ∧ thetaFirstModeFirst (495/512:ℝ) ≤ (-320640680524480087/6250000000000000000000000:ℝ) := by
  have hlo : (21721953426939/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(495/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(495/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(495/512:ℝ)) ≤ (3457156980751/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(495/512:ℝ)) (by norm_num : 2*(495/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(495/512:ℝ)) ≤ (10860980170628476343/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (495/512:ℝ) (21721953426939/1000000000000:ℝ) (10860980170628476343/500000000000000000:ℝ) (14933/12500000000000:ℝ) (59733/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1483).1 (thetaFirstMode_refined_node_1483).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0747 :
    (-80127009761065797301587/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (62729323448440729602555/64882957727484714455552:ℝ) ∧ thetaFirstModeFirst (62729323448440729602555/64882957727484714455552:ℝ) ≤ (-256402054186338767/5000000000000000000000000:ℝ) := by
  have hlo : (21722410533987/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(62729323448440729602555/64882957727484714455552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(62729323448440729602555/64882957727484714455552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(62729323448440729602555/64882957727484714455552:ℝ)) ≤ (864307432903/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(62729323448440729602555/64882957727484714455552:ℝ)) (by norm_num : 2*(62729323448440729602555/64882957727484714455552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(62729323448440729602555/64882957727484714455552:ℝ)) ≤ (2715302181056034479/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (62729323448440729602555/64882957727484714455552:ℝ) (21722410533987/1000000000000:ℝ) (2715302181056034479/125000000000000000:ℝ) (11941/10000000000000:ℝ) (29853/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1487).1 (thetaFirstMode_refined_node_1487).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0748 :
    (-295966525198217195480013/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (31/32:ℝ) ∧ thetaFirstModeFirst (31/32:ℝ) ≤ (-94708395288063491/2000000000000000000000000:ℝ) := by
  have hlo : (4361394149773/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(31/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(31/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(31/32:ℝ)) ≤ (3470687910599/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(31/32:ℝ)) (by norm_num : 2*(31/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(31/32:ℝ)) ≤ (10903488845122444207/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (31/32:ℝ) (4361394149773/200000000000:ℝ) (10903488845122444207/500000000000000000:ℝ) (21967/20000000000000:ℝ) (27459/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1488).1 (thetaFirstMode_refined_node_1488).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0749 :
    (-1092385673921685146888813/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (497/512:ℝ) ∧ thetaFirstModeFirst (497/512:ℝ) ≤ (-27309362525682283/625000000000000000000000:ℝ) := by
  have hlo : (1094616040959/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(497/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(497/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(497/512:ℝ)) ≤ (3484271799009/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(497/512:ℝ)) (by norm_num : 2*(497/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(497/512:ℝ)) ≤ (10946163893864081337/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (497/512:ℝ) (1094616040959/50000000000:ℝ) (10946163893864081337/500000000000000000:ℝ) (25237/25000000000000:ℝ) (100949/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1489).1 (thetaFirstMode_refined_node_1489).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0750 :
    (-27298046771651250923247/625000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (325237897787019494300793/335050313849050052508160:ℝ) ∧ thetaFirstModeFirst (325237897787019494300793/335050313849050052508160:ℝ) ≤ (-1091899876501995579/25000000000000000000000000:ℝ) := by
  have hlo : (21892779657529/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(325237897787019494300793/335050313849050052508160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(325237897787019494300793/335050313849050052508160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(325237897787019494300793/335050313849050052508160:ℝ)) ≤ (696868965083/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(325237897787019494300793/335050313849050052508160:ℝ)) (by norm_num : 2*(325237897787019494300793/335050313849050052508160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(325237897787019494300793/335050313849050052508160:ℝ)) ≤ (2189278662621997219/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (325237897787019494300793/335050313849050052508160:ℝ) (21892779657529/1000000000000:ℝ) (2189278662621997219/100000000000000000:ℝ) (50451/50000000000000:ℝ) (12613/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1493).1 (thetaFirstMode_refined_node_1493).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0751 :
    (-806109242827375992953/20000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (249/256:ℝ) ∧ thetaFirstModeFirst (249/256:ℝ) ≤ (-1007625365100510637/25000000000000000000000000:ℝ) := by
  have hlo : (10989002470113/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(249/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(249/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(249/256:ℝ)) ≤ (699581770651/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(249/256:ℝ)) (by norm_num : 2*(249/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(249/256:ℝ)) ≤ (2197801193604787043/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (249/256:ℝ) (10989002470113/500000000000:ℝ) (2197801193604787043/100000000000000000:ℝ) (92749/100000000000000:ℝ) (371/400000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1494).1 (thetaFirstMode_refined_node_1494).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0752 :
    (-464578881141781149360747/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (499/512:ℝ) ∧ thetaFirstModeFirst (499/512:ℝ) ≤ (-23228391227735441/625000000000000000000000:ℝ) := by
  have hlo : (275800305243/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(499/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(499/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(499/512:ℝ)) ≤ (1755799640711/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(499/512:ℝ)) (by norm_num : 2*(499/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(499/512:ℝ)) ≤ (5516007860660192623/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (499/512:ℝ) (275800305243/12500000000:ℝ) (5516007860660192623/250000000000000000:ℝ) (85187/100000000000000:ℝ) (85189/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1495).1 (thetaFirstMode_refined_node_1495).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0753 :
    (-4643759990130725618479/125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (337208403086384037209991/345989686256645754242560:ℝ) ∧ thetaFirstModeFirst (337208403086384037209991/345989686256645754242560:ℝ) ≤ (-14511404445658589/390625000000000000000000:ℝ) := by
  have hlo : (689515156347/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(337208403086384037209991/345989686256645754242560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(337208403086384037209991/345989686256645754242560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(337208403086384037209991/345989686256645754242560:ℝ)) ≤ (877918146401/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(337208403086384037209991/345989686256645754242560:ℝ)) (by norm_num : 2*(337208403086384037209991/345989686256645754242560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(337208403086384037209991/345989686256645754242560:ℝ)) ≤ (2758061503306356793/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (337208403086384037209991/345989686256645754242560:ℝ) (689515156347/31250000000:ℝ) (2758061503306356793/125000000000000000:ℝ) (21287/25000000000000:ℝ) (1703/2000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1499).1 (thetaFirstMode_refined_node_1499).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0754 :
    (-85649130923928930152121/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (125/128:ℝ) ∧ thetaFirstModeFirst (125/128:ℝ) ≤ (-6691250650837161/195312500000000000000000:ℝ) := by
  have hlo : (692199392793/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(125/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(125/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(125/128:ℝ)) ≤ (352534329241/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(125/128:ℝ)) (by norm_num : 2*(125/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(125/128:ℝ)) ≤ (1107519381003220913/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (125/128:ℝ) (692199392793/31250000000:ℝ) (1107519381003220913/50000000000000000:ℝ) (9777/12500000000000:ℝ) (78217/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1500).1 (thetaFirstMode_refined_node_1500).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0755 :
    (-98656035973839764242543/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (501/512:ℝ) ∧ thetaFirstModeFirst (501/512:ℝ) ≤ (-1578474080342429057/50000000000000000000000000:ℝ) := by
  have hlo : (22237074707727/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(501/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(501/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(501/512:ℝ)) ≤ (7078282191873/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(501/512:ℝ)) (by norm_num : 2*(501/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(501/512:ℝ)) ≤ (22237081786012873689/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (501/512:ℝ) (22237074707727/1000000000000:ℝ) (22237081786012873689/1000000000000000000:ℝ) (71791/100000000000000:ℝ) (4487/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1501).1 (thetaFirstMode_refined_node_1501).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0756 :
    (-788902089583851834247571/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (349568945093337212835009/357240316263365765762560:ℝ) ∧ thetaFirstModeFirst (349568945093337212835009/357240316263365765762560:ℝ) ≤ (-197222710461162147/6250000000000000000000000:ℝ) := by
  have hlo : (5559384262693/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(349568945093337212835009/357240316263365765762560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(349568945093337212835009/357240316263365765762560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(349568945093337212835009/357240316263365765762560:ℝ)) ≤ (3539214680133/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(349568945093337212835009/357240316263365765762560:ℝ)) (by norm_num : 2*(349568945093337212835009/357240316263365765762560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(349568945093337212835009/357240316263365765762560:ℝ)) ≤ (11118772064603071869/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (349568945093337212835009/357240316263365765762560:ℝ) (5559384262693/250000000000:ℝ) (11118772064603071869/500000000000000000:ℝ) (35879/50000000000000:ℝ) (71759/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1505).1 (thetaFirstMode_refined_node_1505).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0757 :
    (-90879132539126594960337/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (251/256:ℝ) ∧ thetaFirstModeFirst (251/256:ℝ) ≤ (-1454043578432209011/50000000000000000000000000:ℝ) := by
  have hlo : (22324108157341/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(251/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(251/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(251/256:ℝ)) ≤ (7105985805077/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(251/256:ℝ)) (by norm_num : 2*(251/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(251/256:ℝ)) ≤ (22324115263329267661/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (251/256:ℝ) (22324108157341/1000000000000:ℝ) (22324115263329267661/1000000000000000000:ℝ) (65871/100000000000000:ℝ) (4117/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1506).1 (thetaFirstMode_refined_node_1506).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0758 :
    (-33474929708560453789287/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (503/512:ℝ) ∧ thetaFirstModeFirst (503/512:ℝ) ≤ (-1338974595835997493/50000000000000000000000000:ℝ) := by
  have hlo : (22411482246247/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(503/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(503/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(503/512:ℝ)) ≤ (3566898923579/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(503/512:ℝ)) (by norm_num : 2*(503/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(503/512:ℝ)) ≤ (11205744690023321347/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (503/512:ℝ) (22411482246247/1000000000000:ℝ) (11205744690023321347/500000000000000000:ℝ) (60419/100000000000000:ℝ) (3021/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1507).1 (thetaFirstMode_refined_node_1507).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0759 :
    (-167300586946877247705661/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (362330598912579278694207/368809764272412990108160:ℝ) ∧ thetaFirstModeFirst (362330598912579278694207/368809764272412990108160:ℝ) ≤ (-1338382102795190499/50000000000000000000000000:ℝ) := by
  have hlo : (22411946362789/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(362330598912579278694207/368809764272412990108160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(362330598912579278694207/368809764272412990108160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(362330598912579278694207/368809764272412990108160:ℝ)) ≤ (7133945580073/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(362330598912579278694207/368809764272412990108160:ℝ)) (by norm_num : 2*(362330598912579278694207/368809764272412990108160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(362330598912579278694207/368809764272412990108160:ℝ)) ≤ (22411953496738276289/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (362330598912579278694207/368809764272412990108160:ℝ) (22411946362789/1000000000000:ℝ) (22411953496738276289/1000000000000000000:ℝ) (60391/100000000000000:ℝ) (7549/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1511).1 (thetaFirstMode_refined_node_1511).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0760 :
    (-3081514957510231482467/125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (63/64:ℝ) ∧ thetaFirstModeFirst (63/64:ℝ) ≤ (-1232583337046444133/50000000000000000000000000:ℝ) := by
  have hlo : (22499198307667/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(63/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(63/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(63/64:ℝ)) ≤ (3580859371247/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(63/64:ℝ)) (by norm_num : 2*(63/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(63/64:ℝ)) ≤ (11249602734693976471/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (63/64:ℝ) (22499198307667/1000000000000:ℝ) (11249602734693976471/500000000000000000:ℝ) (55399/100000000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1512).1 (thetaFirstMode_refined_node_1512).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0761 :
    (-453714524035326416299/20000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (505/512:ℝ) ∧ thetaFirstModeFirst (505/512:ℝ) ≤ (-141780158809659279/6250000000000000000000000:ℝ) := by
  have hlo : (5646814420011/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(505/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(505/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(505/512:ℝ)) ≤ (57517991337/8000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(505/512:ℝ)) (by norm_num : 2*(505/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(505/512:ℝ)) ≤ (180698118958379841/8000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (505/512:ℝ) (5646814420011/250000000000:ℝ) (180698118958379841/8000000000000000:ℝ) (25389/50000000000000:ℝ) (2539/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1513).1 (thetaFirstMode_refined_node_1513).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0762 :
    (-283443465793226403186967/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (75100941623270192936445/76141148621259241175552:ℝ) ∧ thetaFirstModeFirst (75100941623270192936445/76141148621259241175552:ℝ) ≤ (-56687558025935513/2500000000000000000000000:ℝ) := by
  have hlo : (5646930896063/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(75100941623270192936445/76141148621259241175552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75100941623270192936445/76141148621259241175552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(75100941623270192936445/76141148621259241175552:ℝ)) ≤ (7189897219071/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(75100941623270192936445/76141148621259241175552:ℝ)) (by norm_num : 2*(75100941623270192936445/76141148621259241175552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(75100941623270192936445/76141148621259241175552:ℝ)) ≤ (22587730774152920103/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (75100941623270192936445/76141148621259241175552:ℝ) (5646930896063/250000000000:ℝ) (22587730774152920103/1000000000000000000:ℝ) (10151/20000000000000:ℝ) (12689/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1517).1 (thetaFirstMode_refined_node_1517).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0763 :
    (-1043443949409156743993629/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (253/256:ℝ) ∧ thetaFirstModeFirst (253/256:ℝ) ≤ (-16303456061033347/781250000000000000000000:ℝ) := by
  have hlo : (22675661707061/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(253/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(253/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(253/256:ℝ)) ≤ (7217888798757/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(253/256:ℝ)) (by norm_num : 2*(253/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(253/256:ℝ)) ≤ (22675668924953399901/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (253/256:ℝ) (22675661707061/1000000000000:ℝ) (22675668924953399901/1000000000000000000:ℝ) (727/1562500000000:ℝ) (46529/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1518).1 (thetaFirstMode_refined_node_1518).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0764 :
    (-239885505667634502716931/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (507/512:ℝ) ∧ thetaFirstModeFirst (507/512:ℝ) ≤ (-59969949964713963/3125000000000000000000000:ℝ) := by
  have hlo : (2845551467207/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(507/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(507/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(507/512:ℝ)) ≤ (1811534704193/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(507/512:ℝ)) (by norm_num : 2*(507/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(507/512:ℝ)) ≤ (5691104745949799449/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (507/512:ℝ) (2845551467207/125000000000:ℝ) (5691104745949799449/250000000000000000:ℝ) (21309/50000000000000:ℝ) (42619/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1519).1 (thetaFirstMode_refined_node_1519).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0765 :
    (-239777914527258129755283/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (389102890145877331465743/392936120455235036700160:ℝ) ∧ thetaFirstModeFirst (389102890145877331465743/392936120455235036700160:ℝ) ≤ (-76727106763589/4000000000000000000000:ℝ) := by
  have hlo : (3642380711/160000000:ℝ) ≤ Real.pi*Real.exp (2*(389102890145877331465743/392936120455235036700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(389102890145877331465743/392936120455235036700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(389102890145877331465743/392936120455235036700160:ℝ)) ≤ (1811571923069/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(389102890145877331465743/392936120455235036700160:ℝ)) (by norm_num : 2*(389102890145877331465743/392936120455235036700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(389102890145877331465743/392936120455235036700160:ℝ)) ≤ (5691221672510108917/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (389102890145877331465743/392936120455235036700160:ℝ) (3642380711/160000000:ℝ) (5691221672510108917/250000000000000000:ℝ) (21299/50000000000000:ℝ) (42599/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1523).1 (thetaFirstMode_refined_node_1523).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0766 :
    (-55129976500948996224537/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (127/128:ℝ) ∧ thetaFirstModeFirst (127/128:ℝ) ≤ (-17641134732516983/1000000000000000000000000:ℝ) := by
  have hlo : (457070182521/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(127/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(127/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(127/128:ℝ)) ≤ (7274499402231/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(127/128:ℝ)) (by norm_num : 2*(127/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(127/128:ℝ)) ≤ (22853516400553093983/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (127/128:ℝ) (457070182521/20000000000:ℝ) (22853516400553093983/1000000000000000000:ℝ) (39023/100000000000000:ℝ) (2439/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1524).1 (thetaFirstMode_refined_node_1524).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0767 :
    (-20264815543519531633767/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (509/512:ℝ) ∧ thetaFirstModeFirst (509/512:ℝ) ≤ (-405284833961653439/25000000000000000000000000:ℝ) := by
  have hlo : (11471477615881/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(509/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(509/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(509/512:ℝ)) ≤ (7302970987883/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(509/512:ℝ)) (by norm_num : 2*(509/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(509/512:ℝ)) ≤ (22942962534736317619/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (509/512:ℝ) (11471477615881/500000000000:ℝ) (22942962534736317619/1000000000000000000:ℝ) (35719/100000000000000:ℝ) (893/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1525).1 (thetaFirstMode_refined_node_1525).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

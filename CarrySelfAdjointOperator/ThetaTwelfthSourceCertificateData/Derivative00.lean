import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0000 :
    (-3123928630619789507/6250000000000000000:ℝ) ≤ thetaFirstModeFirst (0/1:ℝ) ∧ thetaFirstModeFirst (0/1:ℝ) ≤ (-1561962213172384947/3125000000000000000:ℝ) := by
  have hlo : (392699/125000:ℝ) ≤ Real.pi*Real.exp (2*(0/1:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(0/1:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(0/1:ℝ)) ≤ (1/1:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(0/1:ℝ)) (by norm_num : 2*(0/1:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(0/1:ℝ)) ≤ (3141593/1000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (0/1:ℝ) (392699/125000:ℝ) (3141593/1000000:ℝ) (4321390329403/50000000000000:ℝ) (1080348662699/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0000).1 (thetaFirstMode_refined_node_0000).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0001 :
    (-24815213337945753251481633848871/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/512:ℝ) ∧ thetaFirstModeFirst (1/512:ℝ) ≤ (-12407589923286773782075581/25000000000000000000000000:ℝ) := by
  have hlo : (1576943921717/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/512:ℝ)) ≤ (1003913889339/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/512:ℝ)) (by norm_num : 2*(1/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/512:ℝ)) ≤ (3153888847350177027/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/512:ℝ) (1576943921717/500000000000:ℝ) (3153888847350177027/1000000000000000000:ℝ) (8545502162793/100000000000000:ℝ) (8545510741773/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0001).1 (thetaFirstMode_refined_node_0001).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0002 :
    (-154544454851433773732428733973/312500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/1024:ℝ) ∧ thetaFirstModeFirst (3/1024:ℝ) ≤ (-2472707935666541355640347/5000000000000000000000000:ℝ) := by
  have hlo : (316005380011/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/1024:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/1024:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/1024:ℝ)) ≤ (201175314943/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/1024:ℝ)) (by norm_num : 2*(3/1024:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/1024:ℝ)) ≤ (632010961197724199/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/1024:ℝ) (316005380011/100000000000:ℝ) (632010961197724199/200000000000000000:ℝ) (8497121034577/100000000000000:ℝ) (265535299427/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0002).1 (thetaFirstMode_refined_node_0002).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0003 :
    (-771804606181969261978896606759/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/1536:ℝ) ∧ thetaFirstModeFirst (5/1536:ℝ) ≤ (-24697714002247184581220187/50000000000000000000000000:ℝ) := by
  have hlo : (3162111796651/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/1536:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/1536:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/1536:ℝ)) ≤ (125816456937/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/1536:ℝ)) (by norm_num : 2*(5/1536:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/1536:ℝ)) ≤ (395264100398080641/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/1536:ℝ) (3162111796651/1000000000000:ℝ) (395264100398080641/125000000000000000:ℝ) (8481032229137/100000000000000:ℝ) (2120260191399/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0003).1 (thetaFirstMode_refined_node_0003).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0004 :
    (-24683065018610802259251233359133/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/2048:ℝ) ∧ thetaFirstModeFirst (7/2048:ℝ) ≤ (-2468303163503486817505173/5000000000000000000000000:ℝ) := by
  have hlo : (3163141297471/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/2048:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/2048:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/2048:ℝ)) ≤ (1006859355853/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/2048:ℝ)) (by norm_num : 2*(7/2048:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/2048:ℝ)) ≤ (3163142304332293829/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/2048:ℝ) (3163141297471/1000000000000:ℝ) (3163142304332293829/1000000000000000000:ℝ) (847299499563/10000000000000:ℝ) (8473003526777/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0004).1 (thetaFirstMode_refined_node_0004).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0005 :
    (-3084281961820591115142466947601/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/2560:ℝ) ∧ thetaFirstModeFirst (9/2560:ℝ) ≤ (-1542138894887799000564873/3125000000000000000000000:ℝ) := by
  have hlo : (3163759158841/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/2560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/2560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/2560:ℝ)) ≤ (251764006819/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/2560:ℝ)) (by norm_num : 2*(9/2560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/2560:ℝ)) ≤ (790940041474522667/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/2560:ℝ) (3163759158841/1000000000000:ℝ) (790940041474522667/250000000000000000:ℝ) (529260934353/6250000000000:ℝ) (4234091738803/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0005).1 (thetaFirstMode_refined_node_0005).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0006 :
    (-12319509604871692689883596905413/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/256:ℝ) ∧ thetaFirstModeFirst (1/256:ℝ) ≤ (-12319492931105366023118123/25000000000000000000000000:ℝ) := by
  have hlo : (1583115905719/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/256:ℝ)) ≤ (1007843097207/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/256:ℝ)) (by norm_num : 2*(1/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/256:ℝ)) ≤ (3166232819283830751/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/256:ℝ) (1583115905719/500000000000:ℝ) (3166232819283830751/1000000000000000000:ℝ) (8448911971117/100000000000000:ℝ) (4224460243163/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0006).1 (thetaFirstMode_refined_node_0006).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0007 :
    (-15289287161102122917571017273/31250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/512:ℝ) ∧ thetaFirstModeFirst (3/512:ℝ) ≤ (-191115830117047295816811/390625000000000000000000:ℝ) := by
  have hlo : (198664005773/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(3/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/512:ℝ)) ≤ (25294692089/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/512:ℝ)) (by norm_num : 2*(3/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/512:ℝ)) ≤ (79465627603957777/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/512:ℝ) (198664005773/62500000000:ℝ) (79465627603957777/25000000000000000:ℝ) (1044126246807/12500000000000:ℝ) (208825460649/2500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0007).1 (thetaFirstMode_refined_node_0007).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0008 :
    (-3046546214526921640066413116143/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1785/260096:ℝ) ∧ thetaFirstModeFirst (1785/260096:ℝ) ≤ (-12186168294080635540335707/25000000000000000000000000:ℝ) := by
  have hlo : (1592504920929/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1785/260096:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1785/260096:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1785/260096:ℝ)) ≤ (126727541397/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1785/260096:ℝ)) (by norm_num : 2*(1785/260096:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1785/260096:ℝ)) ≤ (398126356960025421/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1785/260096:ℝ) (1592504920929/500000000000:ℝ) (398126356960025421/125000000000000000:ℝ) (8304005063483/100000000000000:ℝ) (8304013482283/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0010).1 (thetaFirstMode_refined_node_0010).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0009 :
    (-12178282541901429276181369128501/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9207/1308160:ℝ) ∧ thetaFirstModeFirst (9207/1308160:ℝ) ≤ (-194852255750571918189597/400000000000000000000000:ℝ) := by
  have hlo : (25489012559/8000000000:ℝ) ≤ Real.pi*Real.exp (2*(9207/1308160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9207/1308160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9207/1308160:ℝ)) ≤ (507087898409/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9207/1308160:ℝ)) (by norm_num : 2*(9207/1308160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9207/1308160:ℝ)) ≤ (1593063792026425537/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9207/1308160:ℝ) (25489012559/8000000000:ℝ) (1593063792026425537/500000000000000000:ℝ) (8295463900883/100000000000000:ℝ) (8295472313973/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0011).1 (thetaFirstMode_refined_node_0011).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0010 :
    (-12143373430081202768578419622793/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/128:ℝ) ∧ thetaFirstModeFirst (1/128:ℝ) ≤ (-6071678450760556705253373/12500000000000000000000000:ℝ) := by
  have hlo : (1595532437657/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/128:ℝ)) ≤ (1015747708587/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/128:ℝ)) (by norm_num : 2*(1/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/128:ℝ)) ≤ (3191065891062959091/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/128:ℝ) (1595532437657/500000000000:ℝ) (3191065891062959091/1000000000000000000:ℝ) (4128898006789/50000000000000:ℝ) (4128902200723/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0012).1 (thetaFirstMode_refined_node_0012).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0011 :
    (-6027673543452125007618179405923/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/512:ℝ) ∧ thetaFirstModeFirst (5/512:ℝ) ≤ (-1205533063161105100304469/2500000000000000000000000:ℝ) := by
  have hlo : (3203554350107/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/512:ℝ)) ≤ (509861616357/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/512:ℝ)) (by norm_num : 2*(5/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/512:ℝ)) ≤ (1601777684915836701/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/512:ℝ) (3203554350107/1000000000000:ℝ) (1601777684915836701/500000000000000000:ℝ) (408163493967/5000000000000:ℝ) (4081639101823/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0013).1 (thetaFirstMode_refined_node_0013).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0012 :
    (-12015916297805974949981445895421/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (104445/9815552:ℝ) ∧ thetaFirstModeFirst (104445/9815552:ℝ) ≤ (-6007949937742400983063117/12500000000000000000000000:ℝ) := by
  have hlo : (1604583194373/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(104445/9815552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(104445/9815552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(104445/9815552:ℝ)) ≤ (510754800233/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(104445/9815552:ℝ)) (by norm_num : 2*(104445/9815552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(104445/9815552:ℝ)) ≤ (1604583705128391169/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (104445/9815552:ℝ) (1604583194373/500000000000:ℝ) (1604583705128391169/500000000000000000:ℝ) (4060569193129/50000000000000:ℝ) (8121146682109/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0017).1 (thetaFirstMode_refined_node_0017).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0013 :
    (-1495919633275097234116146675387/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/256:ℝ) ∧ thetaFirstModeFirst (3/256:ℝ) ≤ (-957387254768563775252699/2000000000000000000000000:ℝ) := by
  have hlo : (3216092707323/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/256:ℝ)) ≤ (1023714316603/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/256:ℝ)) (by norm_num : 2*(3/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/256:ℝ)) ≤ (3216093731039768579/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/256:ℝ) (3216092707323/1000000000000:ℝ) (3216093731039768579/1000000000000000000:ℝ) (322777252513/4000000000000:ℝ) (504339973353/6250000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0018).1 (thetaFirstMode_refined_node_0018).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0014 :
    (-371231553821004799231150805343/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/512:ℝ) ∧ thetaFirstModeFirst (7/512:ℝ) ≤ (-23758786829634546915152541/50000000000000000000000000:ℝ) := by
  have hlo : (3228680138281/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/512:ℝ)) ≤ (32116281911/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/512:ℝ)) (by norm_num : 2*(7/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/512:ℝ)) ≤ (100896286437624223/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/512:ℝ) (3228680138281/1000000000000:ℝ) (100896286437624223/31250000000000000:ℝ) (7976280005461/100000000000000:ℝ) (3988144101441/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0019).1 (thetaFirstMode_refined_node_0019).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0015 :
    (-5924490061524007408140751687359/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8905743/620700160:ℝ) ∧ thetaFirstModeFirst (8905743/620700160:ℝ) ≤ (-5924481920673575267165577/12500000000000000000000000:ℝ) := by
  have hlo : (808262104767/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(8905743/620700160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8905743/620700160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8905743/620700160:ℝ)) ≤ (514555744201/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8905743/620700160:ℝ)) (by norm_num : 2*(8905743/620700160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8905743/620700160:ℝ)) ≤ (1616524724091652193/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8905743/620700160:ℝ) (808262104767/250000000000:ℝ) (1616524724091652193/500000000000000000:ℝ) (7944198133431/100000000000000:ℝ) (3972103154463/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0023).1 (thetaFirstMode_refined_node_0023).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0016 :
    (-9433209116631240031420315857/20000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/64:ℝ) ∧ thetaFirstModeFirst (1/64:ℝ) ≤ (-11791495162890113731789959/25000000000000000000000000:ℝ) := by
  have hlo : (3241316835051/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/64:ℝ)) ≤ (412697363/400000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/64:ℝ)) (by norm_num : 2*(1/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/64:ℝ)) ≤ (1296527146719259/400000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/64:ℝ) (3241316835051/1000000000000:ℝ) (1296527146719259/400000000000000:ℝ) (3941907799509/50000000000000:ℝ) (7883823733123/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0024).1 (thetaFirstMode_refined_node_0024).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0017 :
    (-2340733682588924423559342003027/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/512:ℝ) ∧ thetaFirstModeFirst (9/512:ℝ) ≤ (-11703652255037366925856809/25000000000000000000000000:ℝ) := by
  have hlo : (1627001495227/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/512:ℝ)) ≤ (517890768511/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/512:ℝ)) (by norm_num : 2*(9/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/512:ℝ)) ≤ (1627002013118778023/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/512:ℝ) (1627001495227/500000000000:ℝ) (1627002013118778023/500000000000000000:ℝ) (7792037685867/100000000000000:ℝ) (1558409151349/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0025).1 (thetaFirstMode_refined_node_0025).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0018 :
    (-2919791757717824683713562529343/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (78453441/4328911360:ℝ) ∧ thetaFirstModeFirst (78453441/4328911360:ℝ) ≤ (-583957544697871673705937/1250000000000000000000000:ℝ) := by
  have hlo : (1628775923309/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(78453441/4328911360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(78453441/4328911360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(78453441/4328911360:ℝ)) ≤ (1036911173259/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(78453441/4328911360:ℝ)) (by norm_num : 2*(78453441/4328911360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(78453441/4328911360:ℝ)) ≤ (3257552883532261587/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (78453441/4328911360:ℝ) (1628775923309/500000000000:ℝ) (3257552883532261587/1000000000000000000:ℝ) (388327499893/5000000000000:ℝ) (970819756389/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0029).1 (thetaFirstMode_refined_node_0029).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0019 :
    (-5807943542150341312002137127447/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/256:ℝ) ∧ thetaFirstModeFirst (5/256:ℝ) ≤ (-5807935500894688594786213/12500000000000000000000000:ℝ) := by
  have hlo : (1633369399033/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/256:ℝ)) ≤ (1039835471337/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/256:ℝ)) (by norm_num : 2*(5/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/256:ℝ)) ≤ (3266739837904019841/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/256:ℝ) (1633369399033/500000000000:ℝ) (3266739837904019841/1000000000000000000:ℝ) (3850472904461/50000000000000:ℝ) (1925238454167/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0030).1 (thetaFirstMode_refined_node_0030).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0020 :
    (-11528173703966429225124966539493/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11/512:ℝ) ∧ thetaFirstModeFirst (11/512:ℝ) ≤ (-1152815769726243074952243/2500000000000000000000000:ℝ) := by
  have hlo : (3279524452219/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11/512:ℝ)) ≤ (521952636151/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11/512:ℝ)) (by norm_num : 2*(11/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11/512:ℝ)) ≤ (1639762748063528543/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11/512:ℝ) (3279524452219/1000000000000:ℝ) (1639762748063528543/500000000000000000:ℝ) (380526973097/5000000000000:ℝ) (7610547406651/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0031).1 (thetaFirstMode_refined_node_0031).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0021 :
    (-11507771887693290951397866871341/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (456304959/20798901760:ℝ) ∧ thetaFirstModeFirst (456304959/20798901760:ℝ) ≤ (-11507755898694836014298787/25000000000000000000000000:ℝ) := by
  have hlo : (1641253519147/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(456304959/20798901760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(456304959/20798901760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(456304959/20798901760:ℝ)) ≤ (1044854659133/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(456304959/20798901760:ℝ)) (by norm_num : 2*(456304959/20798901760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(456304959/20798901760:ℝ)) ≤ (3282508083149618869/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (456304959/20798901760:ℝ) (1641253519147/500000000000:ℝ) (3282508083149618869/1000000000000000000:ℝ) (7589598806121/100000000000000:ℝ) (3794803368089/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0035).1 (thetaFirstMode_refined_node_0035).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0022 :
    (-11440534548514085349456286997703/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3/128:ℝ) ∧ thetaFirstModeFirst (3/128:ℝ) ≤ (-5720259309012744064932709/12500000000000000000000000:ℝ) := by
  have hlo : (3292360148007/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(3/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3/128:ℝ)) ≤ (1047991002017/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3/128:ℝ)) (by norm_num : 2*(3/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3/128:ℝ)) ≤ (3292361195999593081/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3/128:ℝ) (3292360148007/1000000000000:ℝ) (3292361195999593081/1000000000000000000:ℝ) (1880204522387/25000000000000:ℝ) (3760412985663/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0036).1 (thetaFirstMode_refined_node_0036).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0023 :
    (-11352975875966335008478025398527/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (13/512:ℝ) ∧ thetaFirstModeFirst (13/512:ℝ) ≤ (-2838240005519509665945443/6250000000000000000000000:ℝ) := by
  have hlo : (413155760161/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(13/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(13/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(13/512:ℝ)) ≤ (1052092722827/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(13/512:ℝ)) (by norm_num : 2*(13/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(13/512:ℝ)) ≤ (3305247133384243411/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (13/512:ℝ) (413155760161/125000000000:ℝ) (3305247133384243411/1000000000000000000:ℝ) (7431781087363/100000000000000:ℝ) (3715894453157/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0037).1 (thetaFirstMode_refined_node_0037).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0024 :
    (-4534219442057475020351205984021/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1998081657/77506332160:ℝ) ∧ thetaFirstModeFirst (1998081657/77506332160:ℝ) ≤ (-2267106553311635722166547/5000000000000000000000000:ℝ) := by
  have hlo : (661563669621/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(1998081657/77506332160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1998081657/77506332160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1998081657/77506332160:ℝ)) ≤ (210582300191/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1998081657/77506332160:ℝ)) (by norm_num : 2*(1998081657/77506332160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1998081657/77506332160:ℝ)) ≤ (661563880203944263/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1998081657/77506332160:ℝ) (661563669621/200000000000:ℝ) (661563880203944263/200000000000000000:ℝ) (3707065455207/50000000000000:ℝ) (7414138716867/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0041).1 (thetaFirstMode_refined_node_0041).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0025 :
    (-22531007849920397781980934690177/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7/256:ℝ) ∧ thetaFirstModeFirst (7/256:ℝ) ≤ (-2816372037020071822949853/6250000000000000000000000:ℝ) := by
  have hlo : (1659091224343/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(7/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7/256:ℝ)) ≤ (1056210497317/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7/256:ℝ)) (by norm_num : 2*(7/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7/256:ℝ)) ≤ (3318183504897605981/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7/256:ℝ) (1659091224343/500000000000:ℝ) (3318183504897605981/1000000000000000000:ℝ) (1835856950571/25000000000000:ℝ) (7343435558517/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0042).1 (thetaFirstMode_refined_node_0042).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0026 :
    (-5589062456769671077593324264717/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (15/512:ℝ) ∧ thetaFirstModeFirst (15/512:ℝ) ≤ (-4471243685615504445711651/10000000000000000000000000:ℝ) := by
  have hlo : (666233889519/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(15/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(15/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(15/512:ℝ)) ≤ (530172194161/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(15/512:ℝ)) (by norm_num : 2*(15/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(15/512:ℝ)) ≤ (1665585253970838473/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (15/512:ℝ) (666233889519/200000000000:ℝ) (1665585253970838473/500000000000000000:ℝ) (7255757532429/100000000000000:ℝ) (3627882613029/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0043).1 (thetaFirstMode_refined_node_0043).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0027 :
    (-4465177701458345224074278940219/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1424279835/48058429952:ℝ) ∧ thetaFirstModeFirst (1424279835/48058429952:ℝ) ≤ (-11162928567635080029842807/25000000000000000000000000:ℝ) := by
  have hlo : (1666716191283/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(1424279835/48058429952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1424279835/48058429952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1424279835/48058429952:ℝ)) ≤ (212212940609/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1424279835/48058429952:ℝ)) (by norm_num : 2*(1424279835/48058429952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1424279835/48058429952:ℝ)) ≤ (666686688726650137/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1424279835/48058429952:ℝ) (1666716191283/500000000000:ℝ) (666686688726650137/200000000000000000:ℝ) (7240585933229/100000000000000:ℝ) (7240593615987/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0047).1 (thetaFirstMode_refined_node_0047).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0028 :
    (-11090845038414560830867190724973/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1/32:ℝ) ∧ thetaFirstModeFirst (1/32:ℝ) ≤ (-69317683854247975209039/156250000000000000000000:ℝ) := by
  have hlo : (167210363809/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(1/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1/32:ℝ)) ≤ (532247229459/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1/32:ℝ)) (by norm_num : 2*(1/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1/32:ℝ)) ≤ (1672104170337788187/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1/32:ℝ) (167210363809/50000000000:ℝ) (1672104170337788187/500000000000000000:ℝ) (448048095471/6250000000000:ℝ) (7168777158679/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0048).1 (thetaFirstMode_refined_node_0048).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0029 :
    (-687729404610232079487210465111/1562500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17/512:ℝ) ∧ thetaFirstModeFirst (17/512:ℝ) ≤ (-687728433134963525582463/1562500000000000000000000:ℝ) := by
  have hlo : (419662016673/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(17/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17/512:ℝ)) ≤ (66791298277/62500000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17/512:ℝ)) (by norm_num : 2*(17/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17/512:ℝ)) ≤ (209831075127935261/62500000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17/512:ℝ) (419662016673/125000000000:ℝ) (209831075127935261/62500000000000000:ℝ) (1770615747231/25000000000000:ℝ) (3541235278851/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0049).1 (thetaFirstMode_refined_node_0049).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0030 :
    (-21980485586468361132529650697387/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21717383193/648199068160:ℝ) ∧ thetaFirstModeFirst (21717383193/648199068160:ℝ) ≤ (-2198045452341790057834661/5000000000000000000000000:ℝ) := by
  have hlo : (335931825483/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(21717383193/648199068160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21717383193/648199068160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21717383193/648199068160:ℝ)) ≤ (1069304433813/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21717383193/648199068160:ℝ)) (by norm_num : 2*(21717383193/648199068160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21717383193/648199068160:ℝ)) ≤ (3359319324135884109/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21717383193/648199068160:ℝ) (335931825483/100000000000:ℝ) (3359319324135884109/1000000000000000000:ℝ) (7069219913167/100000000000000:ℝ) (7069227472343/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0053).1 (thetaFirstMode_refined_node_0053).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0031 :
    (-4366642948177897490225661444281/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9/256:ℝ) ∧ thetaFirstModeFirst (9/256:ℝ) ≤ (-5458295952674122174714201/12500000000000000000000000:ℝ) := by
  have hlo : (1685218109463/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9/256:ℝ)) ≤ (214568678487/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9/256:ℝ)) (by norm_num : 2*(9/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9/256:ℝ)) ≤ (674087458354009791/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9/256:ℝ) (1685218109463/500000000000:ℝ) (674087458354009791/200000000000000000:ℝ) (3498418534927/50000000000000:ℝ) (6996844576391/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0054).1 (thetaFirstMode_refined_node_0054).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

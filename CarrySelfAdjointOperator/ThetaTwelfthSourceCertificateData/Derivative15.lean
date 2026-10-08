import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0480 :
    (-7085676996472660790182265029/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5682739761029596469193/9178187863912459548160:ℝ) ∧ thetaFirstModeFirst (5682739761029596469193/9178187863912459548160:ℝ) ≤ (-11337040386837400593417/10000000000000000000000000:ℝ) := by
  have hlo : (10837840781521/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5682739761029596469193/9178187863912459548160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5682739761029596469193/9178187863912459548160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5682739761029596469193/9178187863912459548160:ℝ)) ≤ (1724896291677/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5682739761029596469193/9178187863912459548160:ℝ)) (by norm_num : 2*(5682739761029596469193/9178187863912459548160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5682739761029596469193/9178187863912459548160:ℝ)) ≤ (5418922115658421461/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5682739761029596469193/9178187863912459548160:ℝ) (10837840781521/1000000000000:ℝ) (5418922115658421461/500000000000000000:ℝ) (1070760377/20000000000000:ℝ) (1338455089/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0953).1 (thetaFirstMode_refined_node_0953).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0481 :
    (-1365485331396407585777673453/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (159/256:ℝ) ∧ thetaFirstModeFirst (159/256:ℝ) ≤ (-10923841260393359080309/10000000000000000000000000:ℝ) := by
  have hlo : (10879901388233/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(159/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(159/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(159/256:ℝ)) ≤ (1731590446537/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(159/256:ℝ)) (by norm_num : 2*(159/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(159/256:ℝ)) ≤ (5439952425707513441/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (159/256:ℝ) (10879901388233/1000000000000:ℝ) (5439952425707513441/500000000000000000:ℝ) (1027652173/20000000000000:ℝ) (256913933/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0954).1 (thetaFirstMode_refined_node_0954).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0482 :
    (-52603420294587728266309129671/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (319/512:ℝ) ∧ thetaFirstModeFirst (319/512:ℝ) ≤ (-10520644050624667452087/10000000000000000000000000:ℝ) := by
  have hlo : (10922484118279/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(319/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(319/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(319/512:ℝ)) ≤ (3476735399849/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(319/512:ℝ)) (by norm_num : 2*(319/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(319/512:ℝ)) ≤ (10922487595017819457/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (319/512:ℝ) (10922484118279/1000000000000:ℝ) (10922487595017819457/1000000000000000000:ℝ) (985772753/20000000000000:ℝ) (4928880903/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0955).1 (thetaFirstMode_refined_node_0955).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0483 :
    (-3286678066500038985541107551/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (6013674361321379726391/9651788693910057372160:ℝ) ∧ thetaFirstModeFirst (6013674361321379726391/9651788693910057372160:ℝ) ≤ (-52586649085885279623/50000000000000000000000:ℝ) := by
  have hlo : (109228407703/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(6013674361321379726391/9651788693910057372160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(6013674361321379726391/9651788693910057372160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(6013674361321379726391/9651788693910057372160:ℝ)) ≤ (434606115717/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(6013674361321379726391/9651788693910057372160:ℝ)) (by norm_num : 2*(6013674361321379726391/9651788693910057372160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(6013674361321379726391/9651788693910057372160:ℝ)) ≤ (1365355530893717181/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (6013674361321379726391/9651788693910057372160:ℝ) (109228407703/10000000000:ℝ) (1365355530893717181/125000000000000000:ℝ) (492714641/10000000000000:ℝ) (2463581771/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0959).1 (thetaFirstMode_refined_node_0959).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0484 :
    (-791458998900297830620934251/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/8:ℝ) ∧ thetaFirstModeFirst (5/8:ℝ) ≤ (-6331647828576519393659/6250000000000000000000000:ℝ) := by
  have hlo : (5482616756209/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/8:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/8:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/8:ℝ)) ≤ (1745171478731/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/8:ℝ)) (by norm_num : 2*(5/8:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/8:ℝ)) ≤ (5482618501380958483/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/8:ℝ) (5482616756209/500000000000:ℝ) (5482618501380958483/500000000000000000:ℝ) (1181803051/25000000000000:ℝ) (147725897/3125000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0960).1 (thetaFirstMode_refined_node_0960).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0485 :
    (-9753488598093589024910978973/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (321/512:ℝ) ∧ thetaFirstModeFirst (321/512:ℝ) ≤ (-9753451244822059357061/10000000000000000000000000:ℝ) := by
  have hlo : (2201630044591/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(321/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(321/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(321/512:ℝ)) ≤ (3504003773551/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(321/512:ℝ)) (by norm_num : 2*(321/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(321/512:ℝ)) ≤ (11008153726961406743/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (321/512:ℝ) (2201630044591/200000000000:ℝ) (11008153726961406743/1000000000000000000:ℝ) (4533052171/100000000000000:ℝ) (906613611/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0961).1 (thetaFirstMode_refined_node_0961).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0486 :
    (-6094005007060073489706121177/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (6361630132651141262409/10146636573905784424960:ℝ) ∧ thetaFirstModeFirst (6361630132651141262409/10146636573905784424960:ℝ) ≤ (-152349541664093332339/156250000000000000000000:ℝ) := by
  have hlo : (550425371643/50000000000:ℝ) ≤ Real.pi*Real.exp (2*(6361630132651141262409/10146636573905784424960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(6361630132651141262409/10146636573905784424960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(6361630132651141262409/10146636573905784424960:ℝ)) ≤ (3504117477019/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(6361630132651141262409/10146636573905784424960:ℝ)) (by norm_num : 2*(6361630132651141262409/10146636573905784424960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(6361630132651141262409/10146636573905784424960:ℝ)) ≤ (11008510936980551267/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (6361630132651141262409/10146636573905784424960:ℝ) (550425371643/50000000000:ℝ) (11008510936980551267/1000000000000000000:ℝ) (283216873/6250000000000:ℝ) (566435731/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0965).1 (thetaFirstMode_refined_node_0965).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0487 :
    (-23471912218371399747625056219/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (161/256:ℝ) ∧ thetaFirstModeFirst (161/256:ℝ) ≤ (-23471822004054312885619/25000000000000000000000000:ℝ) := by
  have hlo : (11051234904747/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(161/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(161/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(161/256:ℝ)) ≤ (1758859028281/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(161/256:ℝ)) (by norm_num : 2*(161/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(161/256:ℝ)) ≤ (5525619211234391633/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (161/256:ℝ) (11051234904747/1000000000000:ℝ) (5525619211234391633/500000000000000000:ℝ) (2173068377/50000000000000:ℝ) (4346152043/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0966).1 (thetaFirstMode_refined_node_0966).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0488 :
    (-11295190716060018220562965203/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (323/512:ℝ) ∧ thetaFirstModeFirst (323/512:ℝ) ≤ (-705946696647169524977/781250000000000000000000:ℝ) := by
  have hlo : (11094488215217/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(323/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(323/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(323/512:ℝ)) ≤ (1765743007879/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(323/512:ℝ)) (by norm_num : 2*(323/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(323/512:ℝ)) ≤ (5547245873351611247/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (323/512:ℝ) (11094488215217/1000000000000:ℝ) (5547245873351611247/500000000000000000:ℝ) (65097281/1562500000000:ℝ) (2083120349/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0967).1 (thetaFirstMode_refined_node_0967).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0489 :
    (-705725860557885863401761009/781250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (6727368238177514567607/10663543358416903452160:ℝ) ∧ thetaFirstModeFirst (6727368238177514567607/10663543358416903452160:ℝ) ≤ (-1129157021262781119609/1250000000000000000000000:ℝ) := by
  have hlo : (2218969199553/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(6727368238177514567607/10663543358416903452160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(6727368238177514567607/10663543358416903452160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(6727368238177514567607/10663543358416903452160:ℝ)) ≤ (55181248461/15625000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(6727368238177514567607/10663543358416903452160:ℝ)) (by norm_num : 2*(6727368238177514567607/10663543358416903452160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(6727368238177514567607/10663543358416903452160:ℝ)) ≤ (173357023896338373/15625000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (6727368238177514567607/10663543358416903452160:ℝ) (2218969199553/200000000000:ℝ) (173357023896338373/15625000000000000:ℝ) (520596153/12500000000000:ℝ) (4164783933/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0971).1 (thetaFirstMode_refined_node_0971).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0490 :
    (-5434567492845972621105473673/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (81/128:ℝ) ∧ thetaFirstModeFirst (81/128:ℝ) ≤ (-271727322786455602363/312500000000000000000000:ℝ) := by
  have hlo : (2784477703589/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(81/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(81/128:ℝ)) ≤ (443163482653/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(81/128:ℝ)) (by norm_num : 2*(81/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(81/128:ℝ)) ≤ (1392239294958286229/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (81/128:ℝ) (2784477703589/250000000000:ℝ) (1392239294958286229/125000000000000000:ℝ) (99827167/2500000000000:ℝ) (3993100837/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0972).1 (thetaFirstMode_refined_node_0972).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0491 :
    (-10457368978802677663747164561/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (325/512:ℝ) ∧ thetaFirstModeFirst (325/512:ℝ) ≤ (-653583022013921781441/781250000000000000000000:ℝ) := by
  have hlo : (1397687920593/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(325/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(325/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(325/512:ℝ)) ≤ (3559183803863/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(325/512:ℝ)) (by norm_num : 2*(325/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(325/512:ℝ)) ≤ (11181506923929373759/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (325/512:ℝ) (1397687920593/125000000000:ℝ) (11181506923929373759/1000000000000000000:ℝ) (478311537/12500000000000:ℝ) (956626479/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0973).1 (thetaFirstMode_refined_node_0973).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0492 :
    (-2613512127401811263897992001/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1422335766498956948925/2240669318036578698752:ℝ) ∧ thetaFirstModeFirst (1422335766498956948925/2240669318036578698752:ℝ) ≤ (-41816031586213653457799/50000000000000000000000000:ℝ) := by
  have hlo : (11181861734589/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(1422335766498956948925/2240669318036578698752:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1422335766498956948925/2240669318036578698752:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1422335766498956948925/2240669318036578698752:ℝ)) ≤ (444912234569/125000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1422335766498956948925/2240669318036578698752:ℝ)) (by norm_num : 2*(1422335766498956948925/2240669318036578698752:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1422335766498956948925/2240669318036578698752:ℝ)) ≤ (1397733161736328417/125000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1422335766498956948925/2240669318036578698752:ℝ) (11181861734589/1000000000000:ℝ) (1397733161736328417/125000000000000000:ℝ) (3825151891/100000000000000:ℝ) (1912582753/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0977).1 (thetaFirstMode_refined_node_0977).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0493 :
    (-20118964508744370567517685883/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (163/256:ℝ) ∧ thetaFirstModeFirst (163/256:ℝ) ≤ (-100594430326597831457/125000000000000000000000:ℝ) := by
  have hlo : (224505330631/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(163/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(163/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(163/256:ℝ)) ≤ (1786557027703/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(163/256:ℝ)) (by norm_num : 2*(163/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(163/256:ℝ)) ≤ (5612635052332550879/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (163/256:ℝ) (224505330631/20000000000:ℝ) (5612635052332550879/500000000000000000:ℝ) (458277847/12500000000000:ℝ) (3666235877/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0978).1 (thetaFirstMode_refined_node_0978).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0494 :
    (-38700294938383560121165474909/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (327/512:ℝ) ∧ thetaFirstModeFirst (327/512:ℝ) ≤ (-4837517938661281757037/6250000000000000000000000:ℝ) := by
  have hlo : (2817300245637/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(327/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(327/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(327/512:ℝ)) ≤ (3587098828413/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(327/512:ℝ)) (by norm_num : 2*(327/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(327/512:ℝ)) ≤ (11269204569650481909/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (327/512:ℝ) (2817300245637/250000000000:ℝ) (11269204569650481909/1000000000000000000:ℝ) (1756032201/50000000000000:ℝ) (3512077001/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0979).1 (thetaFirstMode_refined_node_0979).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0495 :
    (-9671993372483767377048527433/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7515381976057835704143/11766910146346930332160:ℝ) ∧ thetaFirstModeFirst (7515381976057835704143/11766910146346930332160:ℝ) ≤ (-3868782210442612852023/5000000000000000000000000:ℝ) := by
  have hlo : (2253911990849/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(7515381976057835704143/11766910146346930332160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7515381976057835704143/11766910146346930332160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7515381976057835704143/11766910146346930332160:ℝ)) ≤ (896803273169/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7515381976057835704143/11766910146346930332160:ℝ)) (by norm_num : 2*(7515381976057835704143/11766910146346930332160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7515381976057835704143/11766910146346930332160:ℝ)) ≤ (2817390885364818217/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7515381976057835704143/11766910146346930332160:ℝ) (2253911990849/200000000000:ℝ) (2817390885364818217/250000000000000000:ℝ) (1755415927/50000000000000:ℝ) (3510844449/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0983).1 (thetaFirstMode_refined_node_0983).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0496 :
    (-7443001259731937866431915817/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (41/64:ℝ) ∧ thetaFirstModeFirst (41/64:ℝ) ≤ (-1190875524898917453/1600000000000000000000:ℝ) := by
  have hlo : (18101291821/1600000000:ℝ) ≤ Real.pi*Real.exp (2*(41/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(41/64:ℝ)) ≤ (3601138336273/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(41/64:ℝ)) (by norm_num : 2*(41/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(41/64:ℝ)) ≤ (11313310989266902889/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (41/64:ℝ) (18101291821/1600000000:ℝ) (11313310989266902889/1000000000000000000:ℝ) (67276193/2000000000000:ℝ) (672764353/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0984).1 (thetaFirstMode_refined_node_0984).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0497 :
    (-4472566509083807275060999383/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (329/512:ℝ) ∧ thetaFirstModeFirst (329/512:ℝ) ≤ (-35780391056966759944357/50000000000000000000000000:ℝ) := by
  have hlo : (11357586421293/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(329/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(329/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(329/512:ℝ)) ≤ (3615232793213/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(329/512:ℝ)) (by norm_num : 2*(329/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(329/512:ℝ)) ≤ (11357590036528408309/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (329/512:ℝ) (11357586421293/1000000000000:ℝ) (11357590036528408309/1000000000000000000:ℝ) (3221257049/100000000000000:ℝ) (402658587/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0985).1 (thetaFirstMode_refined_node_0985).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0498 :
    (-8942277290302605047211725741/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7939328572536936611841/12355124896752488296960:ℝ) ∧ thetaFirstModeFirst (7939328572536936611841/12355124896752488296960:ℝ) ≤ (-357689681894805310967/500000000000000000000000:ℝ) := by
  have hlo : (113579460093/10000000000:ℝ) ≤ Real.pi*Real.exp (2*(7939328572536936611841/12355124896752488296960:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7939328572536936611841/12355124896752488296960:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7939328572536936611841/12355124896752488296960:ℝ)) ≤ (1807673626827/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7939328572536936611841/12355124896752488296960:ℝ)) (by norm_num : 2*(7939328572536936611841/12355124896752488296960:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7939328572536936611841/12355124896752488296960:ℝ)) ≤ (5678974812324315411/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7939328572536936611841/12355124896752488296960:ℝ) (113579460093/10000000000:ℝ) (5678974812324315411/500000000000000000:ℝ) (3220124419/100000000000000:ℝ) (1610068031/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0989).1 (thetaFirstMode_refined_node_0989).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0499 :
    (-17197688536797880496340921181/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (165/256:ℝ) ∧ thetaFirstModeFirst (165/256:ℝ) ≤ (-17197620516346447429743/25000000000000000000000000:ℝ) := by
  have hlo : (11402038757697/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(165/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(165/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(165/256:ℝ)) ≤ (1814691207149/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(165/256:ℝ)) (by norm_num : 2*(165/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(165/256:ℝ)) ≤ (5701021193540848357/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (165/256:ℝ) (11402038757697/1000000000000:ℝ) (5701021193540848357/500000000000000000:ℝ) (1542105519/50000000000000:ℝ) (3084222233/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0990).1 (thetaFirstMode_refined_node_0990).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0500 :
    (-3305808137018534765052872577/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (331/512:ℝ) ∧ thetaFirstModeFirst (331/512:ℝ) ≤ (-8264487536898670143269/12500000000000000000000000:ℝ) := by
  have hlo : (5723332537813/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(331/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(331/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(331/512:ℝ)) ≤ (1821793707717/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(331/512:ℝ)) (by norm_num : 2*(331/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(331/512:ℝ)) ≤ (5723334359607773181/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (331/512:ℝ) (5723332537813/500000000000:ℝ) (5723334359607773181/500000000000000000:ℝ) (1476240913/50000000000000:ℝ) (590498517/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0991).1 (thetaFirstMode_refined_node_0991).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0501 :
    (-16523749262706267606642499877/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8384401329530932495359/12968909374505557020160:ℝ) ∧ thetaFirstModeFirst (8384401329530932495359/12968909374505557020160:ℝ) ≤ (-1652368367359362806919/2500000000000000000000000:ℝ) := by
  have hlo : (1144702529431/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(8384401329530932495359/12968909374505557020160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8384401329530932495359/12968909374505557020160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8384401329530932495359/12968909374505557020160:ℝ)) ≤ (1821851038313/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8384401329530932495359/12968909374505557020160:ℝ)) (by norm_num : 2*(8384401329530932495359/12968909374505557020160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8384401329530932495359/12968909374505557020160:ℝ)) ≤ (5723514469006852609/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8384401329530932495359/12968909374505557020160:ℝ) (1144702529431/100000000000:ℝ) (5723514469006852609/500000000000000000:ℝ) (1475720849/50000000000000:ℝ) (2951452453/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0995).1 (thetaFirstMode_refined_node_0995).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0502 :
    (-31767219768252516681463498833/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (83/128:ℝ) ∧ thetaFirstModeFirst (83/128:ℝ) ≤ (-1270683728690796625419/2000000000000000000000000:ℝ) := by
  have hlo : (459658642241/40000000000:ℝ) ≤ Real.pi*Real.exp (2*(83/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(83/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(83/128:ℝ)) ≤ (3657848013373/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(83/128:ℝ)) (by norm_num : 2*(83/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(83/128:ℝ)) ≤ (11491469713876523189/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (83/128:ℝ) (459658642241/40000000000:ℝ) (11491469713876523189/1000000000000000000:ℝ) (2825885259/100000000000000:ℝ) (2825895597/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0996).1 (thetaFirstMode_refined_node_0996).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0503 :
    (-30521401234822132202785103917/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (333/512:ℝ) ∧ thetaFirstModeFirst (333/512:ℝ) ≤ (-3815159900926830556653/6250000000000000000000000:ℝ) := by
  have hlo : (1442055297813/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(333/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(333/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(333/512:ℝ)) ≤ (3672164425713/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(333/512:ℝ)) (by norm_num : 2*(333/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(333/512:ℝ)) ≤ (11536446054668980809/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (333/512:ℝ) (1442055297813/125000000000:ℝ) (11536446054668980809/1000000000000000000:ℝ) (2704242681/100000000000000:ℝ) (2704252613/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0997).1 (thetaFirstMode_refined_node_0997).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0504 :
    (-15255801634371376874784358983/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8851515743072711040057/13609210458953895708160:ℝ) ∧ thetaFirstModeFirst (8851515743072711040057/13609210458953895708160:ℝ) ≤ (-7627870321522087469757/12500000000000000000000000:ℝ) := by
  have hlo : (5768401623071/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(8851515743072711040057/13609210458953895708160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8851515743072711040057/13609210458953895708160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8851515743072711040057/13609210458953895708160:ℝ)) ≤ (3672279292201/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8851515743072711040057/13609210458953895708160:ℝ)) (by norm_num : 2*(8851515743072711040057/13609210458953895708160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8851515743072711040057/13609210458953895708160:ℝ)) ≤ (11536806918423616193/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8851515743072711040057/13609210458953895708160:ℝ) (5768401623071/500000000000:ℝ) (11536806918423616193/1000000000000000000:ℝ) (1351644067/50000000000000:ℝ) (1351649031/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1001).1 (thetaFirstMode_refined_node_1001).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0505 :
    (-3664908547132780791895251203/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (167/256:ℝ) ∧ thetaFirstModeFirst (167/256:ℝ) ≤ (-29319150746463357127029/50000000000000000000000000:ℝ) := by
  have hlo : (11581594741347/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(167/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(167/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(167/256:ℝ)) ≤ (921634217727/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(167/256:ℝ)) (by norm_num : 2*(167/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(167/256:ℝ)) ≤ (2895399606971619111/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (167/256:ℝ) (11581594741347/1000000000000:ℝ) (2895399606971619111/250000000000000000:ℝ) (2587380807/100000000000000:ℝ) (1293695173/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1002).1 (thetaFirstMode_refined_node_1002).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0506 :
    (-14079748443293994346026750201/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (335/512:ℝ) ∧ thetaFirstModeFirst (335/512:ℝ) ≤ (-5631876698160076126059/10000000000000000000000000:ℝ) := by
  have hlo : (11626923821527/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(335/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(335/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(335/512:ℝ)) ≤ (1850482784131/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(335/512:ℝ)) (by norm_num : 2*(335/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(335/512:ℝ)) ≤ (5813463761246460683/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (335/512:ℝ) (11626923821527/1000000000000:ℝ) (5813463761246460683/500000000000000000:ℝ) (495026317/20000000000000:ℝ) (2475140747/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1003).1 (thetaFirstMode_refined_node_1003).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0507 :
    (-14075215871695182252788843799/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1868324221273231476315/2855400814247135293952:ℝ) ∧ thetaFirstModeFirst (1868324221273231476315/2855400814247135293952:ℝ) ≤ (-3518789797671692874357/6250000000000000000000000:ℝ) := by
  have hlo : (1453410668039/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(1868324221273231476315/2855400814247135293952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1868324221273231476315/2855400814247135293952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1868324221273231476315/2855400814247135293952:ℝ)) ≤ (3701080644563/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1868324221273231476315/2855400814247135293952:ℝ)) (by norm_num : 2*(1868324221273231476315/2855400814247135293952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1868324221273231476315/2855400814247135293952:ℝ)) ≤ (11627289045394608859/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1868324221273231476315/2855400814247135293952:ℝ) (1453410668039/125000000000:ℝ) (11627289045394608859/1000000000000000000:ℝ) (2474256163/100000000000000:ℝ) (1237132661/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1007).1 (thetaFirstMode_refined_node_1007).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0508 :
    (-6760198740043604216894630911/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (21/32:ℝ) ∧ thetaFirstModeFirst (21/32:ℝ) ≤ (-27040685681307820620593/50000000000000000000000000:ℝ) := by
  have hlo : (11672430314709/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(21/32:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(21/32:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(21/32:ℝ)) ≤ (1857725368971/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(21/32:ℝ)) (by norm_num : 2*(21/32:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(21/32:ℝ)) ≤ (5836217015081710803/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (21/32:ℝ) (11672430314709/1000000000000:ℝ) (5836217015081710803/500000000000000000:ℝ) (2367332077/100000000000000:ℝ) (1183670437/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1008).1 (thetaFirstMode_refined_node_1008).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0509 :
    (-649047569984997053773833423/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (337/512:ℝ) ∧ thetaFirstModeFirst (337/512:ℝ) ≤ (-1038471900283432150683/2000000000000000000000000:ℝ) := by
  have hlo : (11718114915271/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(337/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(337/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(337/512:ℝ)) ≤ (932498150243/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(337/512:ℝ)) (by norm_num : 2*(337/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(337/512:ℝ)) ≤ (2929529661316357099/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (337/512:ℝ) (11718114915271/1000000000000:ℝ) (2929529661316357099/250000000000000000:ℝ) (90552973/4000000000000:ℝ) (226383277/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1009).1 (thetaFirstMode_refined_node_1009).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0510 :
    (-12976760702627967184139025547/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (9855701543199181141593/14973295882550797212160:ℝ) ∧ thetaFirstModeFirst (9855701543199181141593/14973295882550797212160:ℝ) ≤ (-3244177018377719530471/6250000000000000000000000:ℝ) := by
  have hlo : (5859238555657/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(9855701543199181141593/14973295882550797212160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(9855701543199181141593/14973295882550797212160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(9855701543199181141593/14973295882550797212160:ℝ)) ≤ (3730107891577/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(9855701543199181141593/14973295882550797212160:ℝ)) (by norm_num : 2*(9855701543199181141593/14973295882550797212160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(9855701543199181141593/14973295882550797212160:ℝ)) ≤ (11718480841423062161/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (9855701543199181141593/14973295882550797212160:ℝ) (5859238555657/500000000000:ℝ) (11718480841423062161/1000000000000000000:ℝ) (565755503/25000000000000:ℝ) (1131515227/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1013).1 (thetaFirstMode_refined_node_1013).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0511 :
    (-4984318413074371467019038923/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (169/256:ℝ) ∧ thetaFirstModeFirst (169/256:ℝ) ≤ (-24921490628028378495599/50000000000000000000000000:ℝ) := by
  have hlo : (11763978320303/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(169/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(169/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(169/256:ℝ)) ≤ (748918275849/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(169/256:ℝ)) (by norm_num : 2*(169/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(169/256:ℝ)) ≤ (2352796412979287457/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (169/256:ℝ) (11763978320303/1000000000000:ℝ) (2352796412979287457/200000000000000000:ℝ) (2164455233/100000000000000:ℝ) (2164463339/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1014).1 (thetaFirstMode_refined_node_1014).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

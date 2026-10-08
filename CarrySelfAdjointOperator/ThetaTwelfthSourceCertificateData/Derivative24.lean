import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0768 :
    (-810223604736024861834831/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (403137041799404128338441/405508921354945001551360:ℝ) ∧ thetaFirstModeFirst (403137041799404128338441/405508921354945001551360:ℝ) ≤ (-12659385165123113/781250000000000000000000:ℝ) := by
  have hlo : (716982023563/31250000000:ℝ) ≤ Real.pi*Real.exp (2*(403137041799404128338441/405508921354945001551360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(403137041799404128338441/405508921354945001551360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(403137041799404128338441/405508921354945001551360:ℝ)) ≤ (7303120441489/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(403137041799404128338441/405508921354945001551360:ℝ)) (by norm_num : 2*(403137041799404128338441/405508921354945001551360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(403137041799404128338441/405508921354945001551360:ℝ)) ≤ (22943432057138751977/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (403137041799404128338441/405508921354945001551360:ℝ) (716982023563/31250000000:ℝ) (22943432057138751977/1000000000000000000:ℝ) (17851/50000000000000:ℝ) (35703/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1529).1 (thetaFirstMode_refined_node_1529).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0769 :
    (-186157921755989475768913/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (255/256:ℝ) ∧ thetaFirstModeFirst (255/256:ℝ) ≤ (-372304332323949011/25000000000000000000000000:ℝ) := by
  have hlo : (11516375709817/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(255/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(255/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(255/256:ℝ)) ≤ (7331554008171/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(255/256:ℝ)) (by norm_num : 2*(255/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(255/256:ℝ)) ≤ (23032758751191956403/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (255/256:ℝ) (11516375709817/500000000000:ℝ) (23032758751191956403/1000000000000000000:ℝ) (32683/100000000000000:ℝ) (8171/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1530).1 (thetaFirstMode_refined_node_1530).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0770 :
    (-85476051291916183389717/6250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (511/512:ℝ) ∧ thetaFirstModeFirst (511/512:ℝ) ≤ (-17094632934853899/1250000000000000000000000:ℝ) := by
  have hlo : (2890362382481/125000000000:ℝ) ≤ Real.pi*Real.exp (2*(511/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(511/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(511/512:ℝ)) ≤ (7360248899237/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(511/512:ℝ)) (by norm_num : 2*(511/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(511/512:ℝ)) ≤ (23122906420100664541/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (511/512:ℝ) (2890362382481/125000000000:ℝ) (23122906420100664541/1000000000000000000:ℝ) (5979/20000000000000:ℝ) (3737/12500000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1531).1 (thetaFirstMode_refined_node_1531).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0771 :
    (-170875568653144961453789/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (417619344807863656339959/418432330694036747061760:ℝ) ∧ thetaFirstModeFirst (417619344807863656339959/418432330694036747061760:ℝ) ≤ (-683479181298631671/50000000000000000000000000:ℝ) := by
  have hlo : (23123370412591/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(417619344807863656339959/418432330694036747061760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(417619344807863656339959/418432330694036747061760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(417619344807863656339959/418432330694036747061760:ℝ)) ≤ (3680199467753/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(417619344807863656339959/418432330694036747061760:ℝ)) (by norm_num : 2*(417619344807863656339959/418432330694036747061760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(417619344807863656339959/418432330694036747061760:ℝ)) ≤ (11561688886496550529/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (417619344807863656339959/418432330694036747061760:ℝ) (23123370412591/1000000000000:ℝ) (11561688886496550529/500000000000000000:ℝ) (29881/100000000000000:ℝ) (14941/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_1535).1 (thetaFirstMode_refined_node_1535).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

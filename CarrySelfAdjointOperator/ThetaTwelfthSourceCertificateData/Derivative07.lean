import CarrySelfAdjointOperator.CompletedNativeThetaEighthMomentCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaSharpCurvature
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_derivative_node_0224 :
    (-1161855882003536057633023932237/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (147/512:ℝ) ∧ thetaFirstModeFirst (147/512:ℝ) ≤ (-4647413726650552416003963/50000000000000000000000000:ℝ) := by
  have hlo : (5578659016037/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(147/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(147/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(147/512:ℝ)) ≤ (887871342943/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(147/512:ℝ)) (by norm_num : 2*(147/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(147/512:ℝ)) ≤ (2789330395890328199/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (147/512:ℝ) (5578659016037/1000000000000:ℝ) (2789330395890328199/500000000000000000:ℝ) (872154459999/100000000000000:ℝ) (436078004363/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0439).1 (thetaFirstMode_refined_node_0439).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0225 :
    (-929202785872532394523319159819/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5637281108870877543/19632189611037468160:ℝ) ∧ thetaFirstModeFirst (5637281108870877543/19632189611037468160:ℝ) ≤ (-2323002065195887204787957/25000000000000000000000000:ℝ) := by
  have hlo : (2789527124649/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(5637281108870877543/19632189611037468160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5637281108870877543/19632189611037468160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5637281108870877543/19632189611037468160:ℝ)) ≤ (1775868492567/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5637281108870877543/19632189611037468160:ℝ)) (by norm_num : 2*(5637281108870877543/19632189611037468160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5637281108870877543/19632189611037468160:ℝ)) ≤ (5579056025169039231/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5637281108870877543/19632189611037468160:ℝ) (2789527124649/500000000000:ℝ) (5579056025169039231/1000000000000000000:ℝ) (871825264493/100000000000000:ℝ) (174365362549/20000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0443).1 (thetaFirstMode_refined_node_0443).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0226 :
    (-285633920613287166523597449323/3125000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (37/128:ℝ) ∧ thetaFirstModeFirst (37/128:ℝ) ≤ (-2285066529974661513808413/25000000000000000000000000:ℝ) := by
  have hlo : (2800246635041/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(37/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(37/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(37/128:ℝ)) ≤ (445673186563/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(37/128:ℝ)) (by norm_num : 2*(37/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(37/128:ℝ)) ≤ (1400123763194014859/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (37/128:ℝ) (2800246635041/500000000000:ℝ) (1400123763194014859/250000000000000000:ℝ) (854151725693/100000000000000:ℝ) (213538312097/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0444).1 (thetaFirstMode_refined_node_0444).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0227 :
    (-35950076968671083691893896287/400000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (149/512:ℝ) ∧ thetaFirstModeFirst (149/512:ℝ) ≤ (-2246875040877545106741331/25000000000000000000000000:ℝ) := by
  have hlo : (5622412980981/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(149/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(149/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(149/512:ℝ)) ≤ (357934001677/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(149/512:ℝ)) (by norm_num : 2*(149/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(149/512:ℝ)) ≤ (1124482954130451461/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (149/512:ℝ) (5622412980981/1000000000000:ℝ) (1124482954130451461/200000000000000000:ℝ) (418224557351/50000000000000:ℝ) (33458024467/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0445).1 (thetaFirstMode_refined_node_0445).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0228 :
    (-1123100263923040084569625314417/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (6366249662322494241/21873345290796674560:ℝ) ∧ thetaFirstModeFirst (6366249662322494241/21873345290796674560:ℝ) ≤ (-140387234959132598630779/1562500000000000000000000:ℝ) := by
  have hlo : (1405701492411/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(6366249662322494241/21873345290796674560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(6366249662322494241/21873345290796674560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(6366249662322494241/21873345290796674560:ℝ)) ≤ (447448775147/250000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(6366249662322494241/21873345290796674560:ℝ)) (by norm_num : 2*(6366249662322494241/21873345290796674560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(6366249662322494241/21873345290796674560:ℝ)) ≤ (1405701939860389171/250000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (6366249662322494241/21873345290796674560:ℝ) (1405701492411/250000000000:ℝ) (1405701939860389171/250000000000000000:ℝ) (104516884289/12500000000000:ℝ) (836136570827/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0449).1 (thetaFirstMode_refined_node_0449).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0229 :
    (-883654158575577255778453827/10000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (75/256:ℝ) ∧ thetaFirstModeFirst (75/256:ℝ) ≤ (-1104565345778976329629453/12500000000000000000000000:ℝ) := by
  have hlo : (1411104620801/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(75/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(75/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(75/256:ℝ)) ≤ (1437339663/800000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(75/256:ℝ)) (by norm_num : 2*(75/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(75/256:ℝ)) ≤ (4515536223903159/800000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (75/256:ℝ) (1411104620801/250000000000:ℝ) (4515536223903159/800000000000000:ℝ) (819043127053/100000000000000:ℝ) (204761149653/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0450).1 (thetaFirstMode_refined_node_0450).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0230 :
    (-2171836366119804139922537508687/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (151/512:ℝ) ∧ thetaFirstModeFirst (151/512:ℝ) ≤ (-2171831725535485339960533/25000000000000000000000000:ℝ) := by
  have hlo : (2833255056263/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(151/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(151/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(151/512:ℝ)) ≤ (1803706564229/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(151/512:ℝ)) (by norm_num : 2*(151/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(151/512:ℝ)) ≤ (5666511916235876797/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (151/512:ℝ) (2833255056263/500000000000:ℝ) (5666511916235876797/1000000000000000000:ℝ) (801930276291/100000000000000:ℝ) (400965861371/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0451).1 (thetaFirstMode_refined_node_0451).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0231 :
    (-217118180229069638499437562101/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (7177837152534081759/24335251372240130560:ℝ) ∧ thetaFirstModeFirst (7177837152534081759/24335251372240130560:ℝ) ≤ (-4342354325673290611821981/50000000000000000000000000:ℝ) := by
  have hlo : (5666900939661/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(7177837152534081759/24335251372240130560:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(7177837152534081759/24335251372240130560:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(7177837152534081759/24335251372240130560:ℝ)) ≤ (360766193679/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(7177837152534081759/24335251372240130560:ℝ)) (by norm_num : 2*(7177837152534081759/24335251372240130560:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(7177837152534081759/24335251372240130560:ℝ)) ≤ (1133380548698590647/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (7177837152534081759/24335251372240130560:ℝ) (5666900939661/1000000000000:ℝ) (1133380548698590647/200000000000000000:ℝ) (801630743121/100000000000000:ℝ) (200408047283/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0455).1 (thetaFirstMode_refined_node_0455).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0232 :
    (-5337452279781138832050812283/62500000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (19/64:ℝ) ∧ thetaFirstModeFirst (19/64:ℝ) ≤ (-426995267026391422802549/5000000000000000000000000:ℝ) := by
  have hlo : (5688688206041/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(19/64:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(19/64:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(19/64:ℝ)) ≤ (45269151803/25000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(19/64:ℝ)) (by norm_num : 2*(19/64:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(19/64:ℝ)) ≤ (142217250420242179/25000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (19/64:ℝ) (5688688206041/1000000000000:ℝ) (142217250420242179/25000000000000000:ℝ) (78510708989/10000000000000:ℝ) (39255425577/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0456).1 (thetaFirstMode_refined_node_0456).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0233 :
    (-13116044848090309680926939599/156250000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (153/512:ℝ) ∧ thetaFirstModeFirst (153/512:ℝ) ≤ (-52464066555620330768949/625000000000000000000000:ℝ) := by
  have hlo : (71386913777/12500000000:ℝ) ≤ Real.pi*Real.exp (2*(153/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(153/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(153/512:ℝ)) ≤ (56807912817/31250000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(153/512:ℝ)) (by norm_num : 2*(153/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(153/512:ℝ)) ≤ (178467341250497481/31250000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (153/512:ℝ) (71386913777/12500000000:ℝ) (178467341250497481/31250000000000000:ℝ) (768570109637/100000000000000:ℝ) (76857150679/10000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0457).1 (thetaFirstMode_refined_node_0457).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0234 :
    (-1048968278535039437045883926147/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (8080123862216333457/27036289542638748160:ℝ) ∧ thetaFirstModeFirst (8080123862216333457/27036289542638748160:ℝ) ≤ (-524483011175480589249857/6250000000000000000000000:ℝ) := by
  have hlo : (2855670923883/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(8080123862216333457/27036289542638748160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(8080123862216333457/27036289542638748160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(8080123862216333457/27036289542638748160:ℝ)) ≤ (1817976951739/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(8080123862216333457/27036289542638748160:ℝ)) (by norm_num : 2*(8080123862216333457/27036289542638748160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(8080123862216333457/27036289542638748160:ℝ)) ≤ (5711343665744580227/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (8080123862216333457/27036289542638748160:ℝ) (2855670923883/500000000000:ℝ) (5711343665744580227/1000000000000000000:ℝ) (192071115779/25000000000000:ℝ) (192071464961/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0461).1 (thetaFirstMode_refined_node_0461).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0235 :
    (-2062593249729226879894276925523/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (77/256:ℝ) ∧ thetaFirstModeFirst (77/256:ℝ) ≤ (-1031294399539662119009253/12500000000000000000000000:ℝ) := by
  have hlo : (2866652570309/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(77/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(77/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(77/256:ℝ)) ≤ (912484043221/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(77/256:ℝ)) (by norm_num : 2*(77/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(77/256:ℝ)) ≤ (2866653482794791053/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (77/256:ℝ) (2866652570309/500000000000:ℝ) (2866653482794791053/500000000000000000:ℝ) (376157946017/50000000000000:ℝ) (752317264991/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0462).1 (thetaFirstMode_refined_node_0462).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0236 :
    (-2027057177477008647647354146857/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (155/512:ℝ) ∧ thetaFirstModeFirst (155/512:ℝ) ≤ (-2027052789150508143840639/25000000000000000000000000:ℝ) := by
  have hlo : (2877872331241/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(155/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(155/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(155/512:ℝ)) ≤ (916055404789/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(155/512:ℝ)) (by norm_num : 2*(155/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(155/512:ℝ)) ≤ (2877873247297288877/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (155/512:ℝ) (2877872331241/500000000000:ℝ) (2877873247297288877/500000000000000000:ℝ) (736341008679/100000000000000:ℝ) (736342357741/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0463).1 (thetaFirstMode_refined_node_0463).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0237 :
    (-101322487675637297705305099061/1250000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (1816371645569997795/5999219949625943552:ℝ) ∧ thetaFirstModeFirst (1816371645569997795/5999219949625943552:ℝ) ≤ (-31663208847659774488797/390625000000000000000000:ℝ) := by
  have hlo : (44969776591/7812500000:ℝ) ≤ Real.pi*Real.exp (2*(1816371645569997795/5999219949625943552:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(1816371645569997795/5999219949625943552:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(1816371645569997795/5999219949625943552:ℝ)) ≤ (91611695657/50000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(1816371645569997795/5999219949625943552:ℝ)) (by norm_num : 2*(1816371645569997795/5999219949625943552:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(1816371645569997795/5999219949625943552:ℝ)) ≤ (287806661794161601/50000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (1816371645569997795/5999219949625943552:ℝ) (44969776591/7812500000:ℝ) (287806661794161601/50000000000000000:ℝ) (736068654267/100000000000000:ℝ) (368035001461/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0467).1 (thetaFirstMode_refined_node_0467).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0238 :
    (-1991956954393217262127398832221/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (39/128:ℝ) ∧ thetaFirstModeFirst (39/128:ℝ) ≤ (-79678105115431891627717/1000000000000000000000000:ℝ) := by
  have hlo : (115565440203/20000000000:ℝ) ≤ Real.pi*Real.exp (2*(39/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(39/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(39/128:ℝ)) ≤ (919640744271/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(39/128:ℝ)) (by norm_num : 2*(39/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(39/128:ℝ)) ≤ (2889136924716563703/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (39/128:ℝ) (115565440203/20000000000:ℝ) (2889136924716563703/500000000000000000:ℝ) (720642046639/100000000000000:ℝ) (720643372107/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0468).1 (thetaFirstMode_refined_node_0468).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0239 :
    (-3914581057522903253866383560657/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (157/512:ℝ) ∧ thetaFirstModeFirst (157/512:ℝ) ≤ (-195728626357322999278911/2500000000000000000000000:ℝ) := by
  have hlo : (1160177505473/200000000000:ℝ) ≤ Real.pi*Real.exp (2*(157/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(157/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(157/512:ℝ)) ≤ (1846480232751/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(157/512:ℝ)) (by norm_num : 2*(157/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(157/512:ℝ)) ≤ (5800889373848912343/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (157/512:ℝ) (1160177505473/200000000000:ℝ) (5800889373848912343/1000000000000000000:ℝ) (176303902207/25000000000000:ℝ) (705216910999/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0469).1 (thetaFirstMode_refined_node_0469).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0240 :
    (-78268222841926281470126304231/1000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (10192502262515829993/33235648177494300160:ℝ) ∧ thetaFirstModeFirst (10192502262515829993/33235648177494300160:ℝ) ≤ (-244587663362138601733347/3125000000000000000000000:ℝ) := by
  have hlo : (362579521151/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(10192502262515829993/33235648177494300160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(10192502262515829993/33235648177494300160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(10192502262515829993/33235648177494300160:ℝ)) ≤ (923301360969/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(10192502262515829993/33235648177494300160:ℝ)) (by norm_num : 2*(10192502262515829993/33235648177494300160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(10192502262515829993/33235648177494300160:ℝ)) ≤ (2900637092510683617/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (10192502262515829993/33235648177494300160:ℝ) (362579521151/62500000000:ℝ) (2900637092510683617/500000000000000000:ℝ) (704955976797/100000000000000:ℝ) (28198291143/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0473).1 (thetaFirstMode_refined_node_0473).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0241 :
    (-1923055802555391946567563659283/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (79/256:ℝ) ∧ thetaFirstModeFirst (79/256:ℝ) ≤ (-480762899546180532064667/6250000000000000000000000:ℝ) := by
  have hlo : (5823591559211/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(79/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(79/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(79/256:ℝ)) ≤ (1853707152047/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(79/256:ℝ)) (by norm_num : 2*(79/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(79/256:ℝ)) ≤ (5823593412920790871/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (79/256:ℝ) (5823591559211/1000000000000:ℝ) (5823593412920790871/1000000000000000000:ℝ) (86257289297/12500000000000:ℝ) (345029796773/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0474).1 (thetaFirstMode_refined_node_0474).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0242 :
    (-1889250632247567077906260543431/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (159/512:ℝ) ∧ thetaFirstModeFirst (159/512:ℝ) ≤ (-75569859527507411067417/1000000000000000000000000:ℝ) := by
  have hlo : (2923192226063/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(159/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(159/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(159/512:ℝ)) ≤ (930481178353/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(159/512:ℝ)) (by norm_num : 2*(159/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(159/512:ℝ)) ≤ (2923193156545536329/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (159/512:ℝ) (2923192226063/500000000000:ℝ) (2923193156545536329/500000000000000000:ℝ) (27006671959/4000000000000:ℝ) (675168055439/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0475).1 (thetaFirstMode_refined_node_0475).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0243 :
    (-188868743363900031565117752833/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (11422279416358375191/36777297964497103360:ℝ) ∧ thetaFirstModeFirst (11422279416358375191/36777297964497103360:ℝ) ≤ (-1888683290585368814445909/25000000000000000000000000:ℝ) := by
  have hlo : (5846767404767/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(11422279416358375191/36777297964497103360:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(11422279416358375191/36777297964497103360:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(11422279416358375191/36777297964497103360:ℝ)) ≤ (1861084254343/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(11422279416358375191/36777297964497103360:ℝ)) (by norm_num : 2*(11422279416358375191/36777297964497103360:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(11422279416358375191/36777297964497103360:ℝ)) ≤ (5846769265854188399/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (11422279416358375191/36777297964497103360:ℝ) (5846767404767/1000000000000:ℝ) (5846769265854188399/1000000000000000000:ℝ) (337459671627/50000000000000:ℝ) (33746029967/5000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0479).1 (thetaFirstMode_refined_node_0479).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0244 :
    (-3711745659362169973594036336317/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (5/16:ℝ) ∧ thetaFirstModeFirst (5/16:ℝ) ≤ (-1855868745424776691129521/25000000000000000000000000:ℝ) := by
  have hlo : (5869266553901/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(5/16:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(5/16:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(5/16:ℝ)) ≤ (1868245957433/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(5/16:ℝ)) (by norm_num : 2*(5/16:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(5/16:ℝ)) ≤ (5869268422149810769/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (5/16:ℝ) (5869266553901/1000000000000:ℝ) (5869268422149810769/1000000000000000000:ℝ) (330268857621/50000000000000:ℝ) (660538949293/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0480).1 (thetaFirstMode_refined_node_0480).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0245 :
    (-3645840325845643007993853689059/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (161/512:ℝ) ∧ thetaFirstModeFirst (161/512:ℝ) ≤ (-18229161379622855787957/250000000000000000000000:ℝ) := by
  have hlo : (589223821369/100000000000:ℝ) ≤ Real.pi*Real.exp (2*(161/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(161/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(161/512:ℝ)) ≤ (1875558065367/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(161/512:ℝ)) (by norm_num : 2*(161/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(161/512:ℝ)) ≤ (5892240089250509631/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (161/512:ℝ) (589223821369/100000000000:ℝ) (5892240089250509631/1000000000000000000:ℝ) (32308386653/5000000000000:ℝ) (646168944989/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0481).1 (thetaFirstMode_refined_node_0481).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0246 :
    (-182237803669525893533975887351/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (12782224971512359209/40644882680317749760:ℝ) ∧ thetaFirstModeFirst (12782224971512359209/40644882680317749760:ℝ) ≤ (-911187006354774087551793/12500000000000000000000000:ℝ) := by
  have hlo : (2946309688567/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(12782224971512359209/40644882680317749760:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(12782224971512359209/40644882680317749760:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(12782224971512359209/40644882680317749760:ℝ)) ≤ (375135878697/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(12782224971512359209/40644882680317749760:ℝ)) (by norm_num : 2*(12782224971512359209/40644882680317749760:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(12782224971512359209/40644882680317749760:ℝ)) ≤ (1178524250563344321/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (12782224971512359209/40644882680317749760:ℝ) (2946309688567/500000000000:ℝ) (1178524250563344321/200000000000000000:ℝ) (322965965079/50000000000000:ℝ) (161483285431/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0485).1 (thetaFirstMode_refined_node_0485).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0247 :
    (-1790390357129477066179156723069/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (81/256:ℝ) ∧ thetaFirstModeFirst (81/256:ℝ) ≤ (-447596597738411480983853/6250000000000000000000000:ℝ) := by
  have hlo : (2957649891007/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(81/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(81/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(81/256:ℝ)) ≤ (941449396041/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(81/256:ℝ)) (by norm_num : 2*(81/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(81/256:ℝ)) ≤ (2957650832456633313/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (81/256:ℝ) (2957649891007/500000000000:ℝ) (2957650832456633313/500000000000000000:ℝ) (158013384979/25000000000000:ℝ) (632054730013/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0486).1 (thetaFirstMode_refined_node_0486).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0248 :
    (-175828109541601961338828028491/2500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (163/512:ℝ) ∧ thetaFirstModeFirst (163/512:ℝ) ≤ (-439569296878588781680347/6250000000000000000000000:ℝ) := by
  have hlo : (1484612902691/250000000000:ℝ) ≤ Real.pi*Real.exp (2*(163/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(163/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(163/512:ℝ)) ≤ (189026824959/100000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(163/512:ℝ)) (by norm_num : 2*(163/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(163/512:ℝ)) ≤ (593845350103419687/100000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (163/512:ℝ) (1484612902691/250000000000:ℝ) (593845350103419687/100000000000000000:ℝ) (309095920617/50000000000000:ℝ) (309096504893/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0487).1 (thetaFirstMode_refined_node_0487).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0249 :
    (-140620749959506428356366670507/2000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (14284239070852168407/44863782688534812160:ℝ) ∧ thetaFirstModeFirst (14284239070852168407/44863782688534812160:ℝ) ≤ (-1757755467540605405863167/25000000000000000000000000:ℝ) := by
  have hlo : (2969415525929/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(14284239070852168407/44863782688534812160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(14284239070852168407/44863782688534812160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(14284239070852168407/44863782688534812160:ℝ)) ≤ (1890389029467/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(14284239070852168407/44863782688534812160:ℝ)) (by norm_num : 2*(14284239070852168407/44863782688534812160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(14284239070852168407/44863782688534812160:ℝ)) ≤ (5938832942250320931/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (14284239070852168407/44863782688534812160:ℝ) (2969415525929/500000000000:ℝ) (5938832942250320931/1000000000000000000:ℝ) (617967189223/100000000000000:ℝ) (24718734297/4000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0491).1 (thetaFirstMode_refined_node_0491).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0250 :
    (-863295009875303196532089278973/12500000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (41/128:ℝ) ∧ thetaFirstModeFirst (41/128:ℝ) ≤ (-1726586169607256195796359/25000000000000000000000000:ℝ) := by
  have hlo : (5961694053209/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(41/128:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(41/128:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(41/128:ℝ)) ≤ (1897666550339/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(41/128:ℝ)) (by norm_num : 2*(41/128:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(41/128:ℝ)) ≤ (5961695950879150027/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (41/128:ℝ) (5961694053209/1000000000000:ℝ) (5961695950879150027/1000000000000000000:ℝ) (302289680351/50000000000000:ℝ) (151145126999/25000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0492).1 (thetaFirstMode_refined_node_0492).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0251 :
    (-1695314731816708281918793529259/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (165/512:ℝ) ∧ thetaFirstModeFirst (165/512:ℝ) ≤ (-3390621877837672519889761/50000000000000000000000000:ℝ) := by
  have hlo : (5985027464003/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(165/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(165/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(165/512:ℝ)) ≤ (952546903609/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(165/512:ℝ)) (by norm_num : 2*(165/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(165/512:ℝ)) ≤ (2992514684549709137/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (165/512:ℝ) (5985027464003/1000000000000:ℝ) (2992514684549709137/500000000000000000:ℝ) (591212840587/100000000000000:ℝ) (591213966907/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0493).1 (thetaFirstMode_refined_node_0493).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0252 :
    (-677925107220350352590775899137/10000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (3188228496497630685/9892200887210173952:ℝ) ∧ thetaFirstModeFirst (3188228496497630685/9892200887210173952:ℝ) ≤ (-10592556100470213336813/156250000000000000000000:ℝ) := by
  have hlo : (374087827959/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(3188228496497630685/9892200887210173952:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(3188228496497630685/9892200887210173952:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(3188228496497630685/9892200887210173952:ℝ)) ≤ (381042811883/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(3188228496497630685/9892200887210173952:ℝ)) (by norm_num : 2*(3188228496497630685/9892200887210173952:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(3188228496497630685/9892200887210173952:ℝ)) ≤ (1197081430511949619/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (3188228496497630685/9892200887210173952:ℝ) (374087827959/62500000000:ℝ) (1197081430511949619/200000000000000000:ℝ) (29549942907/5000000000000:ℝ) (590999984123/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0497).1 (thetaFirstMode_refined_node_0497).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0253 :
    (-1664452793922021710207011376119/25000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (83/256:ℝ) ∧ thetaFirstModeFirst (83/256:ℝ) ≤ (-1625438532961658909809/24414062500000000000000:ℝ) := by
  have hlo : (375528262449/62500000000:ℝ) ≤ Real.pi*Real.exp (2*(83/256:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(83/256:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(83/256:ℝ)) ≤ (956275066779/500000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(83/256:ℝ)) (by norm_num : 2*(83/256:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(83/256:ℝ)) ≤ (3004227055867438947/500000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (83/256:ℝ) (375528262449/62500000000:ℝ) (3004227055867438947/500000000000000000:ℝ) (4516320641/781250000000:ℝ) (578090147677/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0498).1 (thetaFirstMode_refined_node_0498).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0254 :
    (-326800345974310853708005344197/5000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (167/512:ℝ) ∧ thetaFirstModeFirst (167/512:ℝ) ≤ (-1633998049918065643921641/25000000000000000000000000:ℝ) := by
  have hlo : (3015984308093/500000000000:ℝ) ≤ Real.pi*Real.exp (2*(167/512:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(167/512:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(167/512:ℝ)) ≤ (384007128627/200000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(167/512:ℝ)) (by norm_num : 2*(167/512:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(167/512:ℝ)) ≤ (1206394107244682811/200000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (167/512:ℝ) (3015984308093/500000000000:ℝ) (1206394107244682811/200000000000000000:ℝ) (565204745437/100000000000000:ℝ) (282602915327/50000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0499).1 (thetaFirstMode_refined_node_0499).2
  convert h using 1 <;> first | rfl | norm_num

theorem thetaTwelfth_derivative_node_0255 :
    (-3267037786701633939058727331097/50000000000000000000000000000000:ℝ) ≤ thetaFirstModeFirst (17766735204530144943/54465262754276508160:ℝ) ∧ thetaFirstModeFirst (17766735204530144943/54465262754276508160:ℝ) ≤ (-3267030428577819977216451/50000000000000000000000000:ℝ) := by
  have hlo : (6032344804229/1000000000000:ℝ) ≤ Real.pi*Real.exp (2*(17766735204530144943/54465262754276508160:ℝ)) := by
    calc
      _ ≤ (3141592/1000000:ℝ)*∑ i ∈ Finset.range 20, (2*(17766735204530144943/54465262754276508160:ℝ))^i/i.factorial := by
        norm_num [Finset.sum_range_succ]
      _ ≤ _ := mul_le_mul (by linarith [Real.pi_gt_d6])
        (Real.sum_le_exp_of_nonneg (by norm_num) 20)
        (Finset.sum_nonneg (fun i _ => by positivity)) Real.pi_pos.le
  have hi : Real.exp (2*(17766735204530144943/54465262754276508160:ℝ)) ≤ (1920155387533/1000000000000:ℝ) := by
    have h := (thetaExp_bounds (by norm_num : (0:ℝ) ≤ 2*(17766735204530144943/54465262754276508160:ℝ)) (by norm_num : 2*(17766735204530144943/54465262754276508160:ℝ) ≤ (32:ℝ))).2
    exact h.trans (by norm_num [thetaExpUpper, Finset.sum_range_succ])
  have hhi : Real.pi*Real.exp (2*(17766735204530144943/54465262754276508160:ℝ)) ≤ (6032346724385960069/1000000000000000000:ℝ) := by
    have h := mul_le_mul (show Real.pi ≤ (3141593/1000000:ℝ) by linarith [Real.pi_lt_d6])
      hi (by positivity) (by norm_num : (0:ℝ) ≤ 3141593/1000000)
    convert h using 1 <;> first | rfl | norm_num
  have h := thetaFirstModeFirst_node_bounds (17766735204530144943/54465262754276508160:ℝ) (6032344804229/1000000000000:ℝ) (6032346724385960069/1000000000000000000:ℝ) (565000970919/100000000000000:ℝ) (565002055813/100000000000000:ℝ)
    (by norm_num) hlo hhi (by norm_num) (thetaFirstMode_refined_node_0503).1 (thetaFirstMode_refined_node_0503).2
  convert h using 1 <;> first | rfl | norm_num

end CarrySelfAdjointOperator

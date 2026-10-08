import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature10
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative15
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative16

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_12_320 :
    (327286575253377/1000000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(321/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-9753451244822059357061/10000000000000000000000000:ℝ)*(thetaPowerMass 13 (5/8:ℝ) (321/512:ℝ)-(321/512:ℝ)*thetaPowerMass 12 (5/8:ℝ) (321/512:ℝ)) ≤
      thetaFirstModeFirst (321/512:ℝ)*(thetaPowerMass 13 (5/8:ℝ) (321/512:ℝ)-(321/512:ℝ)*thetaPowerMass 12 (5/8:ℝ) (321/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0485.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (5/8:ℝ) (321/512:ℝ)
    (321/512:ℝ) (4533052171/100000000000000:ℝ) (-9753451244822059357061/10000000000000000000000000:ℝ) (18989797966138220160881/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_320
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0961).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_320 :
    (∫ x in (5/8:ℝ)..(321/512:ℝ), x^12*thetaFirstMode x) ≤ (40911144704441/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (5/8:ℝ) (321/512:ℝ)
    (147725897/3125000000000:ℝ) (906613611/20000000000000:ℝ) (18989797966138220160881/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_320 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0961).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_321 :
    (20360611667357/62500000000000000000000:ℝ) ≤ ∫ x in (321/512:ℝ)..(161/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-6094005007060073489706121177/6250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (321/512:ℝ) (161/256:ℝ)-(6361630132651141262409/10146636573905784424960:ℝ)*thetaPowerMass 12 (321/512:ℝ) (161/256:ℝ)) ≤
      thetaFirstModeFirst (6361630132651141262409/10146636573905784424960:ℝ)*(thetaPowerMass 13 (321/512:ℝ) (161/256:ℝ)-(6361630132651141262409/10146636573905784424960:ℝ)*thetaPowerMass 12 (321/512:ℝ) (161/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0486.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (321/512:ℝ) (161/256:ℝ)
    (6361630132651141262409/10146636573905784424960:ℝ) (283216873/6250000000000:ℝ) (-6094005007060073489706121177/6250000000000000000000000000000:ℝ) (18360765920791664960263/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_321
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0965).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_321 :
    (∫ x in (321/512:ℝ)..(161/256:ℝ), x^12*thetaFirstMode x) ≤ (162886912667117/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (321/512:ℝ) (161/256:ℝ)
    (906613611/20000000000000:ℝ) (4346152043/100000000000000:ℝ) (18360765920791664960263/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_321 (thetaFirstMode_refined_node_0961).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_322 :
    (324170698595787/1000000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(323/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-705946696647169524977/781250000000000000000000:ℝ)*(thetaPowerMass 13 (161/256:ℝ) (323/512:ℝ)-(323/512:ℝ)*thetaPowerMass 12 (161/256:ℝ) (323/512:ℝ)) ≤
      thetaFirstModeFirst (323/512:ℝ)*(thetaPowerMass 13 (161/256:ℝ) (323/512:ℝ)-(323/512:ℝ)*thetaPowerMass 12 (161/256:ℝ) (323/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0488.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (161/256:ℝ) (323/512:ℝ)
    (323/512:ℝ) (65097281/1562500000000:ℝ) (-705946696647169524977/781250000000000000000000:ℝ) (2218691076948617867173/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_322
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0967).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_322 :
    (∫ x in (161/256:ℝ)..(323/512:ℝ), x^12*thetaFirstMode x) ≤ (162086652096137/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (161/256:ℝ) (323/512:ℝ)
    (4346152043/100000000000000:ℝ) (2083120349/50000000000000:ℝ) (2218691076948617867173/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_322 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0967).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_323 :
    (322484855013327/1000000000000000000000000:ℝ) ≤ ∫ x in (323/512:ℝ)..(81/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-705725860557885863401761009/781250000000000000000000000000:ℝ)*(thetaPowerMass 13 (323/512:ℝ) (81/128:ℝ)-(6727368238177514567607/10663543358416903452160:ℝ)*thetaPowerMass 12 (323/512:ℝ) (81/128:ℝ)) ≤
      thetaFirstModeFirst (6727368238177514567607/10663543358416903452160:ℝ)*(thetaPowerMass 13 (323/512:ℝ) (81/128:ℝ)-(6727368238177514567607/10663543358416903452160:ℝ)*thetaPowerMass 12 (323/512:ℝ) (81/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0489.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (323/512:ℝ) (81/128:ℝ)
    (6727368238177514567607/10663543358416903452160:ℝ) (520596153/12500000000000:ℝ) (-705725860557885863401761009/781250000000000000000000000000:ℝ) (17155688547831666497587/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_323
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0971).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_323 :
    (∫ x in (323/512:ℝ)..(81/128:ℝ), x^12*thetaFirstMode x) ≤ (161244470045807/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (323/512:ℝ) (81/128:ℝ)
    (2083120349/50000000000000:ℝ) (3993100837/100000000000000:ℝ) (17155688547831666497587/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_323 (thetaFirstMode_refined_node_0967).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_324 :
    (320719514052519/1000000000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(325/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-653583022013921781441/781250000000000000000000:ℝ)*(thetaPowerMass 13 (81/128:ℝ) (325/512:ℝ)-(325/512:ℝ)*thetaPowerMass 12 (81/128:ℝ) (325/512:ℝ)) ≤
      thetaFirstModeFirst (325/512:ℝ)*(thetaPowerMass 13 (81/128:ℝ) (325/512:ℝ)-(325/512:ℝ)*thetaPowerMass 12 (81/128:ℝ) (325/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0491.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (81/128:ℝ) (325/512:ℝ)
    (325/512:ℝ) (478311537/12500000000000:ℝ) (-653583022013921781441/781250000000000000000000:ℝ) (4144713437913322237179/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_324
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0973).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_324 :
    (∫ x in (81/128:ℝ)..(325/512:ℝ), x^12*thetaFirstMode x) ≤ (320722140213711/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (81/128:ℝ) (325/512:ℝ)
    (3993100837/100000000000000:ℝ) (956626479/25000000000000:ℝ) (4144713437913322237179/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_324 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0973).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_325 :
    (159435121809959/500000000000000000000000:ℝ) ≤ ∫ x in (325/512:ℝ)..(163/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-2613512127401811263897992001/3125000000000000000000000000000:ℝ)*(thetaPowerMass 13 (325/512:ℝ) (163/256:ℝ)-(1422335766498956948925/2240669318036578698752:ℝ)*thetaPowerMass 12 (325/512:ℝ) (163/256:ℝ)) ≤
      thetaFirstModeFirst (1422335766498956948925/2240669318036578698752:ℝ)*(thetaPowerMass 13 (325/512:ℝ) (163/256:ℝ)-(1422335766498956948925/2240669318036578698752:ℝ)*thetaPowerMass 12 (325/512:ℝ) (163/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0492.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (325/512:ℝ) (163/256:ℝ)
    (1422335766498956948925/2240669318036578698752:ℝ) (3825151891/100000000000000:ℝ) (-2613512127401811263897992001/3125000000000000000000000000000:ℝ) (16018637837795994942557/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_325
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0977).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_325 :
    (∫ x in (325/512:ℝ)..(163/256:ℝ), x^12*thetaFirstMode x) ≤ (159437185598353/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (325/512:ℝ) (163/256:ℝ)
    (956626479/25000000000000:ℝ) (3666235877/100000000000000:ℝ) (16018637837795994942557/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_325 (thetaFirstMode_refined_node_0973).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_326 :
    (63388902603563/200000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(327/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-4837517938661281757037/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (163/256:ℝ) (327/512:ℝ)-(327/512:ℝ)*thetaPowerMass 12 (163/256:ℝ) (327/512:ℝ)) ≤
      thetaFirstModeFirst (327/512:ℝ)*(thetaPowerMass 13 (163/256:ℝ) (327/512:ℝ)-(327/512:ℝ)*thetaPowerMass 12 (163/256:ℝ) (327/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0494.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (163/256:ℝ) (327/512:ℝ)
    (327/512:ℝ) (1756032201/50000000000000:ℝ) (-4837517938661281757037/6250000000000000000000000:ℝ) (7737329995450590364139/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_326
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0979).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_326 :
    (∫ x in (163/256:ℝ)..(327/512:ℝ), x^12*thetaFirstMode x) ≤ (158473578543707/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (163/256:ℝ) (327/512:ℝ)
    (3666235877/100000000000000:ℝ) (3512077001/100000000000000:ℝ) (7737329995450590364139/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_326 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0979).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_327 :
    (62987582283373/200000000000000000000000:ℝ) ≤ ∫ x in (327/512:ℝ)..(41/64:ℝ), x^12*thetaFirstMode x := by
  have hd : (-9671993372483767377048527433/12500000000000000000000000000000:ℝ)*(thetaPowerMass 13 (327/512:ℝ) (41/64:ℝ)-(7515381976057835704143/11766910146346930332160:ℝ)*thetaPowerMass 12 (327/512:ℝ) (41/64:ℝ)) ≤
      thetaFirstModeFirst (7515381976057835704143/11766910146346930332160:ℝ)*(thetaPowerMass 13 (327/512:ℝ) (41/64:ℝ)-(7515381976057835704143/11766910146346930332160:ℝ)*thetaPowerMass 12 (327/512:ℝ) (41/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0495.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (327/512:ℝ) (41/64:ℝ)
    (7515381976057835704143/11766910146346930332160:ℝ) (1755415927/50000000000000:ℝ) (-9671993372483767377048527433/12500000000000000000000000000000:ℝ) (3736636247141410437059/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_327
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0983).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_327 :
    (∫ x in (327/512:ℝ)..(41/64:ℝ), x^12*thetaFirstMode x) ≤ (314942077462839/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (327/512:ℝ) (41/64:ℝ)
    (3512077001/100000000000000:ℝ) (672764353/20000000000000:ℝ) (3736636247141410437059/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_327 (thetaFirstMode_refined_node_0979).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_328 :
    (312858106048733/1000000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(329/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-35780391056966759944357/50000000000000000000000000:ℝ)*(thetaPowerMass 13 (41/64:ℝ) (329/512:ℝ)-(329/512:ℝ)*thetaPowerMass 12 (41/64:ℝ) (329/512:ℝ)) ≤
      thetaFirstModeFirst (329/512:ℝ)*(thetaPowerMass 13 (41/64:ℝ) (329/512:ℝ)-(329/512:ℝ)*thetaPowerMass 12 (41/64:ℝ) (329/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0497.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (41/64:ℝ) (329/512:ℝ)
    (329/512:ℝ) (3221257049/100000000000000:ℝ) (-35780391056966759944357/50000000000000000000000000:ℝ) (2886784644269605718733/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_328
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0985).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_328 :
    (∫ x in (41/64:ℝ)..(329/512:ℝ), x^12*thetaFirstMode x) ≤ (156430382679987/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (41/64:ℝ) (329/512:ℝ)
    (672764353/20000000000000:ℝ) (402658587/12500000000000:ℝ) (2886784644269605718733/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_328 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0985).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_329 :
    (155350352486559/500000000000000000000000:ℝ) ≤ ∫ x in (329/512:ℝ)..(165/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-8942277290302605047211725741/12500000000000000000000000000000:ℝ)*(thetaPowerMass 13 (329/512:ℝ) (165/256:ℝ)-(7939328572536936611841/12355124896752488296960:ℝ)*thetaPowerMass 12 (329/512:ℝ) (165/256:ℝ)) ≤
      thetaFirstModeFirst (7939328572536936611841/12355124896752488296960:ℝ)*(thetaPowerMass 13 (329/512:ℝ) (165/256:ℝ)-(7939328572536936611841/12355124896752488296960:ℝ)*thetaPowerMass 12 (329/512:ℝ) (165/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0498.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (329/512:ℝ) (165/256:ℝ)
    (7939328572536936611841/12355124896752488296960:ℝ) (3220124419/100000000000000:ℝ) (-8942277290302605047211725741/12500000000000000000000000000000:ℝ) (1742053836423642278459/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_329
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0989).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_329 :
    (∫ x in (329/512:ℝ)..(165/256:ℝ), x^12*thetaFirstMode x) ≤ (310704905181903/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (329/512:ℝ) (165/256:ℝ)
    (402658587/12500000000000:ℝ) (3084222233/100000000000000:ℝ) (1742053836423642278459/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_329 (thetaFirstMode_refined_node_0985).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_330 :
    (38559194852781/125000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(331/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-8264487536898670143269/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (165/256:ℝ) (331/512:ℝ)-(331/512:ℝ)*thetaPowerMass 12 (165/256:ℝ) (331/512:ℝ)) ≤
      thetaFirstModeFirst (331/512:ℝ)*(thetaPowerMass 13 (165/256:ℝ) (331/512:ℝ)-(331/512:ℝ)*thetaPowerMass 12 (165/256:ℝ) (331/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0500.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (165/256:ℝ) (331/512:ℝ)
    (331/512:ℝ) (1476240913/50000000000000:ℝ) (-8264487536898670143269/12500000000000000000000000:ℝ) (6726854505705281028953/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_330
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0991).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_330 :
    (∫ x in (165/256:ℝ)..(331/512:ℝ), x^12*thetaFirstMode x) ≤ (308476230534479/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (165/256:ℝ) (331/512:ℝ)
    (3084222233/100000000000000:ℝ) (590498517/20000000000000:ℝ) (6726854505705281028953/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_330 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0991).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_331 :
    (2449378335861/8000000000000000000000:ℝ) ≤ ∫ x in (331/512:ℝ)..(83/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-16523749262706267606642499877/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (331/512:ℝ) (83/128:ℝ)-(8384401329530932495359/12968909374505557020160:ℝ)*thetaPowerMass 12 (331/512:ℝ) (83/128:ℝ)) ≤
      thetaFirstModeFirst (8384401329530932495359/12968909374505557020160:ℝ)*(thetaPowerMass 13 (331/512:ℝ) (83/128:ℝ)-(8384401329530932495359/12968909374505557020160:ℝ)*thetaPowerMass 12 (331/512:ℝ) (83/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0501.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (331/512:ℝ) (83/128:ℝ)
    (8384401329530932495359/12968909374505557020160:ℝ) (1475720849/50000000000000:ℝ) (-16523749262706267606642499877/25000000000000000000000000000000:ℝ) (2597081084548014810409/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_331
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0995).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_331 :
    (∫ x in (331/512:ℝ)..(83/128:ℝ), x^12*thetaFirstMode x) ≤ (153088261000149/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (331/512:ℝ) (83/128:ℝ)
    (590498517/20000000000000:ℝ) (2825895597/100000000000000:ℝ) (2597081084548014810409/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_331 (thetaFirstMode_refined_node_0991).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_332 :
    (75951230888037/250000000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(333/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-3815159900926830556653/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (83/128:ℝ) (333/512:ℝ)-(333/512:ℝ)*thetaPowerMass 12 (83/128:ℝ) (333/512:ℝ)) ≤
      thetaFirstModeFirst (333/512:ℝ)*(thetaPowerMass 13 (83/128:ℝ) (333/512:ℝ)-(333/512:ℝ)*thetaPowerMass 12 (83/128:ℝ) (333/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0503.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (83/128:ℝ) (333/512:ℝ)
    (333/512:ℝ) (2704242681/100000000000000:ℝ) (-3815159900926830556653/6250000000000000000000000:ℝ) (2506234554697104736573/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_332
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0997).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_332 :
    (∫ x in (83/128:ℝ)..(333/512:ℝ), x^12*thetaFirstMode x) ≤ (9493987653059/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (83/128:ℝ) (333/512:ℝ)
    (2825895597/100000000000000:ℝ) (2704252613/100000000000000:ℝ) (2506234554697104736573/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_332 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_0997).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_333 :
    (301367091612721/1000000000000000000000000:ℝ) ≤ ∫ x in (333/512:ℝ)..(167/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-15255801634371376874784358983/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (333/512:ℝ) (167/256:ℝ)-(8851515743072711040057/13609210458953895708160:ℝ)*thetaPowerMass 12 (333/512:ℝ) (167/256:ℝ)) ≤
      thetaFirstModeFirst (8851515743072711040057/13609210458953895708160:ℝ)*(thetaPowerMass 13 (333/512:ℝ) (167/256:ℝ)-(8851515743072711040057/13609210458953895708160:ℝ)*thetaPowerMass 12 (333/512:ℝ) (167/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0504.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (333/512:ℝ) (167/256:ℝ)
    (8851515743072711040057/13609210458953895708160:ℝ) (1351644067/50000000000000:ℝ) (-15255801634371376874784358983/25000000000000000000000000000000:ℝ) (12090669538846831606073/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_333
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1001).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_333 :
    (∫ x in (333/512:ℝ)..(167/256:ℝ), x^12*thetaFirstMode x) ≤ (301371346988547/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (333/512:ℝ) (167/256:ℝ)
    (2704252613/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (12090669538846831606073/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_333 (thetaFirstMode_refined_node_0997).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_334 :
    (149433484090969/500000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(335/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-5631876698160076126059/10000000000000000000000000:ℝ)*(thetaPowerMass 13 (167/256:ℝ) (335/512:ℝ)-(335/512:ℝ)*thetaPowerMass 12 (167/256:ℝ) (335/512:ℝ)) ≤
      thetaFirstModeFirst (335/512:ℝ)*(thetaPowerMass 13 (167/256:ℝ) (335/512:ℝ)-(335/512:ℝ)*thetaPowerMass 12 (167/256:ℝ) (335/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0506.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (167/256:ℝ) (335/512:ℝ)
    (335/512:ℝ) (495026317/20000000000000:ℝ) (-5631876698160076126059/10000000000000000000000000:ℝ) (11663559777958023968721/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_334
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1003).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_334 :
    (∫ x in (167/256:ℝ)..(335/512:ℝ), x^12*thetaFirstMode x) ≤ (149434828121937/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (167/256:ℝ) (335/512:ℝ)
    (1293695173/50000000000000:ℝ) (2475140747/100000000000000:ℝ) (11663559777958023968721/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_334 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1003).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_335 :
    (296300201961049/1000000000000000000000000:ℝ) ≤ ∫ x in (335/512:ℝ)..(21/32:ℝ), x^12*thetaFirstMode x := by
  have hd : (-14075215871695182252788843799/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (335/512:ℝ) (21/32:ℝ)-(1868324221273231476315/2855400814247135293952:ℝ)*thetaPowerMass 12 (335/512:ℝ) (21/32:ℝ)) ≤
      thetaFirstModeFirst (1868324221273231476315/2855400814247135293952:ℝ)*(thetaPowerMass 13 (335/512:ℝ) (21/32:ℝ)-(1868324221273231476315/2855400814247135293952:ℝ)*thetaPowerMass 12 (335/512:ℝ) (21/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0507.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (335/512:ℝ) (21/32:ℝ)
    (1868324221273231476315/2855400814247135293952:ℝ) (2474256163/100000000000000:ℝ) (-14075215871695182252788843799/25000000000000000000000000000000:ℝ) (449980526649808350319/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_335
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1007).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_335 :
    (∫ x in (335/512:ℝ)..(21/32:ℝ), x^12*thetaFirstMode x) ≤ (59260895655549/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (335/512:ℝ) (21/32:ℝ)
    (2475140747/100000000000000:ℝ) (1183670437/50000000000000:ℝ) (449980526649808350319/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_335 (thetaFirstMode_refined_node_1003).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_336 :
    (293675102061521/1000000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(337/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1038471900283432150683/2000000000000000000000000:ℝ)*(thetaPowerMass 13 (21/32:ℝ) (337/512:ℝ)-(337/512:ℝ)*thetaPowerMass 12 (21/32:ℝ) (337/512:ℝ)) ≤
      thetaFirstModeFirst (337/512:ℝ)*(thetaPowerMass 13 (21/32:ℝ) (337/512:ℝ)-(337/512:ℝ)*thetaPowerMass 12 (21/32:ℝ) (337/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0509.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (21/32:ℝ) (337/512:ℝ)
    (337/512:ℝ) (90552973/4000000000000:ℝ) (-1038471900283432150683/2000000000000000000000000:ℝ) (2712051236299203677233/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_336
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1009).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_336 :
    (∫ x in (21/32:ℝ)..(337/512:ℝ), x^12*thetaFirstMode x) ≤ (293677794005371/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (21/32:ℝ) (337/512:ℝ)
    (1183670437/50000000000000:ℝ) (226383277/10000000000000:ℝ) (2712051236299203677233/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_336 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1009).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_337 :
    (290987324996237/1000000000000000000000000:ℝ) ≤ ∫ x in (337/512:ℝ)..(169/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-12976760702627967184139025547/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (337/512:ℝ) (169/256:ℝ)-(9855701543199181141593/14973295882550797212160:ℝ)*thetaPowerMass 12 (337/512:ℝ) (169/256:ℝ)) ≤
      thetaFirstModeFirst (9855701543199181141593/14973295882550797212160:ℝ)*(thetaPowerMass 13 (337/512:ℝ) (169/256:ℝ)-(9855701543199181141593/14973295882550797212160:ℝ)*thetaPowerMass 12 (337/512:ℝ) (169/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0510.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (337/512:ℝ) (169/256:ℝ)
    (9855701543199181141593/14973295882550797212160:ℝ) (565755503/25000000000000:ℝ) (-12976760702627967184139025547/25000000000000000000000000000000:ℝ) (1045931593457899070031/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_337
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1013).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_337 :
    (∫ x in (337/512:ℝ)..(169/256:ℝ), x^12*thetaFirstMode x) ≤ (290991617465611/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (337/512:ℝ) (169/256:ℝ)
    (226383277/10000000000000:ℝ) (2164463339/100000000000000:ℝ) (1045931593457899070031/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_337 (thetaFirstMode_refined_node_1009).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_338 :
    (144122650121611/500000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(339/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-5979641895920786498487/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (169/256:ℝ) (339/512:ℝ)-(339/512:ℝ)*thetaPowerMass 12 (169/256:ℝ) (339/512:ℝ)) ≤
      thetaFirstModeFirst (339/512:ℝ)*(thetaPowerMass 13 (169/256:ℝ) (339/512:ℝ)-(339/512:ℝ)*thetaPowerMass 12 (169/256:ℝ) (339/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0512.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (169/256:ℝ) (339/512:ℝ)
    (339/512:ℝ) (2069076441/100000000000000:ℝ) (-5979641895920786498487/12500000000000000000000000:ℝ) (5041266247114722322963/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_338
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1015).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_338 :
    (∫ x in (169/256:ℝ)..(339/512:ℝ), x^12*thetaFirstMode x) ≤ (57649598622639/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (169/256:ℝ) (339/512:ℝ)
    (2164463339/100000000000000:ℝ) (103454211/5000000000000:ℝ) (5041266247114722322963/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_338 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1015).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_339 :
    (142722344644673/500000000000000000000000:ℝ) ≤ ∫ x in (339/512:ℝ)..(85/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-747216294124166881302501399/1562500000000000000000000000000:ℝ)*(thetaPowerMass 13 (339/512:ℝ) (85/128:ℝ)-(10394777066482805050791/15699122035309073589760:ℝ)*thetaPowerMass 12 (339/512:ℝ) (85/128:ℝ)) ≤
      thetaFirstModeFirst (10394777066482805050791/15699122035309073589760:ℝ)*(thetaPowerMass 13 (339/512:ℝ) (85/128:ℝ)-(10394777066482805050791/15699122035309073589760:ℝ)*thetaPowerMass 12 (339/512:ℝ) (85/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0513.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (339/512:ℝ) (85/128:ℝ)
    (10394777066482805050791/15699122035309073589760:ℝ) (16158919/781250000000:ℝ) (-747216294124166881302501399/1562500000000000000000000000000:ℝ) (9717546511209071045359/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_339
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1019).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_339 :
    (∫ x in (339/512:ℝ)..(85/128:ℝ), x^12*thetaFirstMode x) ≤ (142724496650851/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (339/512:ℝ) (85/128:ℝ)
    (103454211/5000000000000:ℝ) (1977551671/100000000000000:ℝ) (9717546511209071045359/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_339 (thetaFirstMode_refined_node_1015).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_340 :
    (282594025060171/1000000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(341/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-11010117211927961486661/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (85/128:ℝ) (341/512:ℝ)-(341/512:ℝ)*thetaPowerMass 12 (85/128:ℝ) (341/512:ℝ)) ≤
      thetaFirstModeFirst (341/512:ℝ)*(thetaPowerMass 13 (85/128:ℝ) (341/512:ℝ)-(341/512:ℝ)*thetaPowerMass 12 (85/128:ℝ) (341/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0515.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (85/128:ℝ) (341/512:ℝ)
    (341/512:ℝ) (1889719291/100000000000000:ℝ) (-11010117211927961486661/25000000000000000000000000:ℝ) (1170506923053822489801/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_340
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1021).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_340 :
    (∫ x in (85/128:ℝ)..(341/512:ℝ), x^12*thetaFirstMode x) ≤ (4415573688849/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (85/128:ℝ) (341/512:ℝ)
    (1977551671/100000000000000:ℝ) (472431613/25000000000000:ℝ) (1170506923053822489801/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_340 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1021).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_341 :
    (34961121439541/125000000000000000000000:ℝ) ≤ ∫ x in (341/512:ℝ)..(171/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-2751646894917022496316655149/6250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (341/512:ℝ) (171/256:ℝ)-(10959904662371742259809/16455549877310448463360:ℝ)*thetaPowerMass 12 (341/512:ℝ) (171/256:ℝ)) ≤
      thetaFirstModeFirst (10959904662371742259809/16455549877310448463360:ℝ)*(thetaPowerMass 13 (341/512:ℝ) (171/256:ℝ)-(10959904662371742259809/16455549877310448463360:ℝ)*thetaPowerMass 12 (341/512:ℝ) (171/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0516.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (341/512:ℝ) (171/256:ℝ)
    (10959904662371742259809/16455549877310448463360:ℝ) (1889046769/100000000000000:ℝ) (-2751646894917022496316655149/6250000000000000000000000000000:ℝ) (902176198681593383143/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_341
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1025).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_341 :
    (∫ x in (341/512:ℝ)..(171/256:ℝ), x^12*thetaFirstMode x) ≤ (139846641266523/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (341/512:ℝ) (171/256:ℝ)
    (472431613/25000000000000:ℝ) (902736853/50000000000000:ℝ) (902176198681593383143/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_341 (thetaFirstMode_refined_node_1021).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_342 :
    (276738147933387/1000000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(343/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-5064453976706091210187/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (171/256:ℝ) (343/512:ℝ)-(343/512:ℝ)*thetaPowerMass 12 (171/256:ℝ) (343/512:ℝ)) ≤
      thetaFirstModeFirst (343/512:ℝ)*(thetaPowerMass 13 (171/256:ℝ) (343/512:ℝ)-(343/512:ℝ)*thetaPowerMass 12 (171/256:ℝ) (343/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0518.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (171/256:ℝ) (343/512:ℝ)
    (343/512:ℝ) (862328131/50000000000000:ℝ) (-5064453976706091210187/12500000000000000000000000:ℝ) (4345187324651066737441/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_342
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1027).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_342 :
    (∫ x in (171/256:ℝ)..(343/512:ℝ), x^12*thetaFirstMode x) ≤ (55348166824151/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (171/256:ℝ) (343/512:ℝ)
    (902736853/50000000000000:ℝ) (26947857/1562500000000:ℝ) (4345187324651066737441/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_342 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1027).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_343 :
    (136868608710999/500000000000000000000000:ℝ) ≤ ∫ x in (343/512:ℝ)..(43/64:ℝ), x^12*thetaFirstMode x := by
  have hd : (-10125651529677904809646813429/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (343/512:ℝ) (43/64:ℝ)-(11552179400427359855007/17243678709113286300160:ℝ)*thetaPowerMass 12 (343/512:ℝ) (43/64:ℝ)) ≤
      thetaFirstModeFirst (11552179400427359855007/17243678709113286300160:ℝ)*(thetaPowerMass 13 (343/512:ℝ) (43/64:ℝ)-(11552179400427359855007/17243678709113286300160:ℝ)*thetaPowerMass 12 (343/512:ℝ) (43/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0519.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (343/512:ℝ) (43/64:ℝ)
    (11552179400427359855007/17243678709113286300160:ℝ) (1724041173/100000000000000:ℝ) (-10125651529677904809646813429/25000000000000000000000000000000:ℝ) (4184803553622849574231/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_343
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1031).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_343 :
    (∫ x in (343/512:ℝ)..(43/64:ℝ), x^12*thetaFirstMode x) ≤ (273741530590799/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (343/512:ℝ) (43/64:ℝ)
    (26947857/1562500000000:ℝ) (51473983/3125000000000:ℝ) (4184803553622849574231/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_343 (thetaFirstMode_refined_node_1027).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_344 :
    (135347434294571/500000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(345/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-9311394941907337555997/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (43/64:ℝ) (345/512:ℝ)-(345/512:ℝ)*thetaPowerMass 12 (43/64:ℝ) (345/512:ℝ)) ≤
      thetaFirstModeFirst (345/512:ℝ)*(thetaPowerMass 13 (43/64:ℝ) (345/512:ℝ)-(345/512:ℝ)*thetaPowerMass 12 (43/64:ℝ) (345/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0521.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (43/64:ℝ) (345/512:ℝ)
    (345/512:ℝ) (786429551/50000000000000:ℝ) (-9311394941907337555997/25000000000000000000000000:ℝ) (8059178514888556234447/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_344
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1033).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_344 :
    (∫ x in (43/64:ℝ)..(345/512:ℝ), x^12*thetaFirstMode x) ≤ (135348773592581/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (43/64:ℝ) (345/512:ℝ)
    (51473983/3125000000000:ℝ) (393216289/25000000000000:ℝ) (8059178514888556234447/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_344 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1033).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_345 :
    (267606761450051/1000000000000000000000000:ℝ) ≤ ∫ x in (345/512:ℝ)..(173/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-9308392710025231478938235433/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (345/512:ℝ) (173/256:ℝ)-(2434547114057885834205/3612928108949549783552:ℝ)*thetaPowerMass 12 (345/512:ℝ) (173/256:ℝ)) ≤
      thetaFirstModeFirst (2434547114057885834205/3612928108949549783552:ℝ)*(thetaPowerMass 13 (345/512:ℝ) (173/256:ℝ)-(2434547114057885834205/3612928108949549783552:ℝ)*thetaPowerMass 12 (345/512:ℝ) (173/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0522.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (345/512:ℝ) (173/256:ℝ)
    (2434547114057885834205/3612928108949549783552:ℝ) (314459387/20000000000000:ℝ) (-9308392710025231478938235433/25000000000000000000000000000000:ℝ) (12123145869520086023/1562500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_345
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1037).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_345 :
    (∫ x in (345/512:ℝ)..(173/256:ℝ), x^12*thetaFirstMode x) ≤ (133805536044949/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (345/512:ℝ) (173/256:ℝ)
    (393216289/25000000000000:ℝ) (18770469/1250000000000:ℝ) (12123145869520086023/1562500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_345 (thetaFirstMode_refined_node_1033).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_346 :
    (66120409085371/250000000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(347/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-42767693318296663223/125000000000000000000000:ℝ)*(thetaPowerMass 13 (173/256:ℝ) (347/512:ℝ)-(347/512:ℝ)*thetaPowerMass 12 (173/256:ℝ) (347/512:ℝ)) ≤
      thetaFirstModeFirst (347/512:ℝ)*(thetaPowerMass 13 (173/256:ℝ) (347/512:ℝ)-(347/512:ℝ)*thetaPowerMass 12 (173/256:ℝ) (347/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0524.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (173/256:ℝ) (347/512:ℝ)
    (347/512:ℝ) (3583411/250000000000:ℝ) (-42767693318296663223/125000000000000000000000:ℝ) (466765090716006631209/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_346
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1039).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_346 :
    (∫ x in (173/256:ℝ)..(347/512:ℝ), x^12*thetaFirstMode x) ≤ (264484304307357/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (173/256:ℝ) (347/512:ℝ)
    (18770469/1250000000000:ℝ) (35834249/2500000000000:ℝ) (466765090716006631209/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_346 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1039).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_347 :
    (26131514768169/100000000000000000000000:ℝ) ≤ ∫ x in (347/512:ℝ)..(87/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-17101545515717541399376803969/50000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (347/512:ℝ) (87/128:ℝ)-(12822747845328599226543/18919600885932177948160:ℝ)*thetaPowerMass 12 (347/512:ℝ) (87/128:ℝ)) ≤
      thetaFirstModeFirst (12822747845328599226543/18919600885932177948160:ℝ)*(thetaPowerMass 13 (347/512:ℝ) (87/128:ℝ)-(12822747845328599226543/18919600885932177948160:ℝ)*thetaPowerMass 12 (347/512:ℝ) (87/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0525.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (347/512:ℝ) (87/128:ℝ)
    (12822747845328599226543/18919600885932177948160:ℝ) (286570193/20000000000000:ℝ) (-17101545515717541399376803969/50000000000000000000000000000000:ℝ) (3593598945580688865067/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_347
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1043).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_347 :
    (∫ x in (347/512:ℝ)..(87/128:ℝ), x^12*thetaFirstMode x) ≤ (130659725434011/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (347/512:ℝ) (87/128:ℝ)
    (35834249/2500000000000:ℝ) (683975811/50000000000000:ℝ) (3593598945580688865067/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_347 (thetaFirstMode_refined_node_1039).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_348 :
    (64529017390539/250000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(349/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1962878190904528220173/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (87/128:ℝ) (349/512:ℝ)-(349/512:ℝ)*thetaPowerMass 12 (87/128:ℝ) (349/512:ℝ)) ≤
      thetaFirstModeFirst (349/512:ℝ)*(thetaPowerMass 13 (87/128:ℝ) (349/512:ℝ)-(349/512:ℝ)*thetaPowerMass 12 (87/128:ℝ) (349/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0527.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (87/128:ℝ) (349/512:ℝ)
    (349/512:ℝ) (163158773/12500000000000:ℝ) (-1962878190904528220173/6250000000000000000000000:ℝ) (1383084605119152080019/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_348
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1045).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_348 :
    (∫ x in (87/128:ℝ)..(349/512:ℝ), x^12*thetaFirstMode x) ≤ (806621013363/3125000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (87/128:ℝ) (349/512:ℝ)
    (683975811/50000000000000:ℝ) (1305275287/100000000000000:ℝ) (1383084605119152080019/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_348 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1045).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_349 :
    (127440024587303/500000000000000000000000:ℝ) ≤ ∫ x in (349/512:ℝ)..(175/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-3924483208224762998804737941/12500000000000000000000000000000:ℝ)*(thetaPowerMass 13 (349/512:ℝ) (175/256:ℝ)-(13503432473757098003241/19809759509951338370560:ℝ)*thetaPowerMass 12 (349/512:ℝ) (175/256:ℝ)) ≤
      thetaFirstModeFirst (13503432473757098003241/19809759509951338370560:ℝ)*(thetaPowerMass 13 (349/512:ℝ) (175/256:ℝ)-(13503432473757098003241/19809759509951338370560:ℝ)*thetaPowerMass 12 (349/512:ℝ) (175/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0528.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (349/512:ℝ) (175/256:ℝ)
    (13503432473757098003241/19809759509951338370560:ℝ) (1304801589/100000000000000:ℝ) (-3924483208224762998804737941/12500000000000000000000000000000:ℝ) (415791399088820588141/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_349
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1049).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_349 :
    (∫ x in (349/512:ℝ)..(175/256:ℝ), x^12*thetaFirstMode x) ≤ (50976868090443/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (349/512:ℝ) (175/256:ℝ)
    (1305275287/100000000000000:ℝ) (622618637/50000000000000:ℝ) (415791399088820588141/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_349 (thetaFirstMode_refined_node_1045).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_350 :
    (125807938712231/500000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(351/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-288067832501024132739/1000000000000000000000000:ℝ)*(thetaPowerMass 13 (175/256:ℝ) (351/512:ℝ)-(351/512:ℝ)*thetaPowerMass 12 (175/256:ℝ) (351/512:ℝ)) ≤
      thetaFirstModeFirst (351/512:ℝ)*(thetaPowerMass 13 (175/256:ℝ) (351/512:ℝ)-(351/512:ℝ)*thetaPowerMass 12 (175/256:ℝ) (351/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0530.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (175/256:ℝ) (351/512:ℝ)
    (351/512:ℝ) (593866329/50000000000000:ℝ) (-288067832501024132739/1000000000000000000000000:ℝ) (3199333338005062984983/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_350
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1051).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_350 :
    (∫ x in (175/256:ℝ)..(351/512:ℝ), x^12*thetaFirstMode x) ≤ (50323703231659/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (175/256:ℝ) (351/512:ℝ)
    (622618637/50000000000000:ℝ) (1187737339/100000000000000:ℝ) (3199333338005062984983/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_350 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1051).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_351 :
    (248319191988701/1000000000000000000000000:ℝ) ≤ ∫ x in (351/512:ℝ)..(11/16:ℝ), x^12*thetaFirstMode x := by
  have hd : (-7199353298200506036368577071/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (351/512:ℝ) (11/16:ℝ)-(14216048497680767340759/20736351271356306434560:ℝ)*thetaPowerMass 12 (351/512:ℝ) (11/16:ℝ)) ≤
      thetaFirstModeFirst (14216048497680767340759/20736351271356306434560:ℝ)*(thetaPowerMass 13 (351/512:ℝ) (11/16:ℝ)-(14216048497680767340759/20736351271356306434560:ℝ)*thetaPowerMass 12 (351/512:ℝ) (11/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0531.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (351/512:ℝ) (11/16:ℝ)
    (14216048497680767340759/20736351271356306434560:ℝ) (74206581/6250000000000:ℝ) (-7199353298200506036368577071/25000000000000000000000000000000:ℝ) (1538297928038724187807/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_351
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1055).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_351 :
    (∫ x in (351/512:ℝ)..(11/16:ℝ), x^12*thetaFirstMode x) ≤ (248323466425633/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (351/512:ℝ) (11/16:ℝ)
    (1187737339/100000000000000:ℝ) (566339291/50000000000000:ℝ) (1538297928038724187807/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_351 (thetaFirstMode_refined_node_1051).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature10
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative15
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative16

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_2_320 :
    (3543006193818951/100000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(321/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-9753451244822059357061/10000000000000000000000000:ℝ)*(thetaPowerMass 3 (5/8:ℝ) (321/512:ℝ)-(321/512:ℝ)*thetaPowerMass 2 (5/8:ℝ) (321/512:ℝ)) ≤
      thetaFirstModeFirst (321/512:ℝ)*(thetaPowerMass 3 (5/8:ℝ) (321/512:ℝ)-(321/512:ℝ)*thetaPowerMass 2 (5/8:ℝ) (321/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0485.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (5/8:ℝ) (321/512:ℝ)
    (321/512:ℝ) (4533052171/100000000000000:ℝ) (-9753451244822059357061/10000000000000000000000000:ℝ) (18989797966138220160881/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_320
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0961).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_320 :
    (∫ x in (5/8:ℝ)..(321/512:ℝ), x^2*thetaFirstMode x) ≤ (2214396392956669/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (5/8:ℝ) (321/512:ℝ)
    (147725897/3125000000000:ℝ) (906613611/20000000000000:ℝ) (18989797966138220160881/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_320 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0961).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_321 :
    (8546047691700629/250000000000000000000000:ℝ) ≤ ∫ x in (321/512:ℝ)..(161/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-6094005007060073489706121177/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (321/512:ℝ) (161/256:ℝ)-(6361630132651141262409/10146636573905784424960:ℝ)*thetaPowerMass 2 (321/512:ℝ) (161/256:ℝ)) ≤
      thetaFirstModeFirst (6361630132651141262409/10146636573905784424960:ℝ)*(thetaPowerMass 3 (321/512:ℝ) (161/256:ℝ)-(6361630132651141262409/10146636573905784424960:ℝ)*thetaPowerMass 2 (321/512:ℝ) (161/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0486.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (321/512:ℝ) (161/256:ℝ)
    (6361630132651141262409/10146636573905784424960:ℝ) (283216873/6250000000000:ℝ) (-6094005007060073489706121177/6250000000000000000000000000000:ℝ) (18360765920791664960263/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_321
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0965).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_321 :
    (∫ x in (321/512:ℝ)..(161/256:ℝ), x^2*thetaFirstMode x) ≤ (6836922591700999/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (321/512:ℝ) (161/256:ℝ)
    (906613611/20000000000000:ℝ) (4346152043/100000000000000:ℝ) (18360765920791664960263/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_321 (thetaFirstMode_refined_node_0961).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_322 :
    (32976229176381121/1000000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(323/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-705946696647169524977/781250000000000000000000:ℝ)*(thetaPowerMass 3 (161/256:ℝ) (323/512:ℝ)-(323/512:ℝ)*thetaPowerMass 2 (161/256:ℝ) (323/512:ℝ)) ≤
      thetaFirstModeFirst (323/512:ℝ)*(thetaPowerMass 3 (161/256:ℝ) (323/512:ℝ)-(323/512:ℝ)*thetaPowerMass 2 (161/256:ℝ) (323/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0488.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (161/256:ℝ) (323/512:ℝ)
    (323/512:ℝ) (65097281/1562500000000:ℝ) (-705946696647169524977/781250000000000000000000:ℝ) (2218691076948617867173/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_322
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0967).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_322 :
    (∫ x in (161/256:ℝ)..(323/512:ℝ), x^2*thetaFirstMode x) ≤ (8244123746671781/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (161/256:ℝ) (323/512:ℝ)
    (4346152043/100000000000000:ℝ) (2083120349/50000000000000:ℝ) (2218691076948617867173/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_322 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0967).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_323 :
    (1987792873788061/62500000000000000000000:ℝ) ≤ ∫ x in (323/512:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-705725860557885863401761009/781250000000000000000000000000:ℝ)*(thetaPowerMass 3 (323/512:ℝ) (81/128:ℝ)-(6727368238177514567607/10663543358416903452160:ℝ)*thetaPowerMass 2 (323/512:ℝ) (81/128:ℝ)) ≤
      thetaFirstModeFirst (6727368238177514567607/10663543358416903452160:ℝ)*(thetaPowerMass 3 (323/512:ℝ) (81/128:ℝ)-(6727368238177514567607/10663543358416903452160:ℝ)*thetaPowerMass 2 (323/512:ℝ) (81/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0489.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (323/512:ℝ) (81/128:ℝ)
    (6727368238177514567607/10663543358416903452160:ℝ) (520596153/12500000000000:ℝ) (-705725860557885863401761009/781250000000000000000000000000:ℝ) (17155688547831666497587/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_323
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0971).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_323 :
    (∫ x in (323/512:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x) ≤ (31805087347430273/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (323/512:ℝ) (81/128:ℝ)
    (2083120349/50000000000000:ℝ) (3993100837/100000000000000:ℝ) (17155688547831666497587/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_323 (thetaFirstMode_refined_node_0967).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_324 :
    (30669250517573129/1000000000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(325/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-653583022013921781441/781250000000000000000000:ℝ)*(thetaPowerMass 3 (81/128:ℝ) (325/512:ℝ)-(325/512:ℝ)*thetaPowerMass 2 (81/128:ℝ) (325/512:ℝ)) ≤
      thetaFirstModeFirst (325/512:ℝ)*(thetaPowerMass 3 (81/128:ℝ) (325/512:ℝ)-(325/512:ℝ)*thetaPowerMass 2 (81/128:ℝ) (325/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0491.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (81/128:ℝ) (325/512:ℝ)
    (325/512:ℝ) (478311537/12500000000000:ℝ) (-653583022013921781441/781250000000000000000000:ℝ) (4144713437913322237179/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_324
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0973).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_324 :
    (∫ x in (81/128:ℝ)..(325/512:ℝ), x^2*thetaFirstMode x) ≤ (7667375591465369/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (81/128:ℝ) (325/512:ℝ)
    (3993100837/100000000000000:ℝ) (956626479/25000000000000:ℝ) (4144713437913322237179/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_324 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0973).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_325 :
    (29568484498198857/1000000000000000000000000:ℝ) ≤ ∫ x in (325/512:ℝ)..(163/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2613512127401811263897992001/3125000000000000000000000000000:ℝ)*(thetaPowerMass 3 (325/512:ℝ) (163/256:ℝ)-(1422335766498956948925/2240669318036578698752:ℝ)*thetaPowerMass 2 (325/512:ℝ) (163/256:ℝ)) ≤
      thetaFirstModeFirst (1422335766498956948925/2240669318036578698752:ℝ)*(thetaPowerMass 3 (325/512:ℝ) (163/256:ℝ)-(1422335766498956948925/2240669318036578698752:ℝ)*thetaPowerMass 2 (325/512:ℝ) (163/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0492.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (325/512:ℝ) (163/256:ℝ)
    (1422335766498956948925/2240669318036578698752:ℝ) (3825151891/100000000000000:ℝ) (-2613512127401811263897992001/3125000000000000000000000000000:ℝ) (16018637837795994942557/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_325
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0977).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_325 :
    (∫ x in (325/512:ℝ)..(163/256:ℝ), x^2*thetaFirstMode x) ≤ (1182754632061823/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (325/512:ℝ) (163/256:ℝ)
    (956626479/25000000000000:ℝ) (3666235877/100000000000000:ℝ) (16018637837795994942557/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_325 (thetaFirstMode_refined_node_0973).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_326 :
    (28502078452483827/1000000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(327/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-4837517938661281757037/6250000000000000000000000:ℝ)*(thetaPowerMass 3 (163/256:ℝ) (327/512:ℝ)-(327/512:ℝ)*thetaPowerMass 2 (163/256:ℝ) (327/512:ℝ)) ≤
      thetaFirstModeFirst (327/512:ℝ)*(thetaPowerMass 3 (163/256:ℝ) (327/512:ℝ)-(327/512:ℝ)*thetaPowerMass 2 (163/256:ℝ) (327/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0494.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (163/256:ℝ) (327/512:ℝ)
    (327/512:ℝ) (1756032201/50000000000000:ℝ) (-4837517938661281757037/6250000000000000000000000:ℝ) (7737329995450590364139/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_326
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0979).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_326 :
    (∫ x in (163/256:ℝ)..(327/512:ℝ), x^2*thetaFirstMode x) ≤ (28502316908537609/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (163/256:ℝ) (327/512:ℝ)
    (3666235877/100000000000000:ℝ) (3512077001/100000000000000:ℝ) (7737329995450590364139/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_326 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0979).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_327 :
    (27468646515030199/1000000000000000000000000:ℝ) ≤ ∫ x in (327/512:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-9671993372483767377048527433/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (327/512:ℝ) (41/64:ℝ)-(7515381976057835704143/11766910146346930332160:ℝ)*thetaPowerMass 2 (327/512:ℝ) (41/64:ℝ)) ≤
      thetaFirstModeFirst (7515381976057835704143/11766910146346930332160:ℝ)*(thetaPowerMass 3 (327/512:ℝ) (41/64:ℝ)-(7515381976057835704143/11766910146346930332160:ℝ)*thetaPowerMass 2 (327/512:ℝ) (41/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0495.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (327/512:ℝ) (41/64:ℝ)
    (7515381976057835704143/11766910146346930332160:ℝ) (1755415927/50000000000000:ℝ) (-9671993372483767377048527433/12500000000000000000000000000000:ℝ) (3736636247141410437059/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_327
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0983).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_327 :
    (∫ x in (327/512:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x) ≤ (27469008506191923/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (327/512:ℝ) (41/64:ℝ)
    (3512077001/100000000000000:ℝ) (672764353/20000000000000:ℝ) (3736636247141410437059/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_327 (thetaFirstMode_refined_node_0979).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_328 :
    (26467881401747147/1000000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(329/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-35780391056966759944357/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (41/64:ℝ) (329/512:ℝ)-(329/512:ℝ)*thetaPowerMass 2 (41/64:ℝ) (329/512:ℝ)) ≤
      thetaFirstModeFirst (329/512:ℝ)*(thetaPowerMass 3 (41/64:ℝ) (329/512:ℝ)-(329/512:ℝ)*thetaPowerMass 2 (41/64:ℝ) (329/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0497.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (41/64:ℝ) (329/512:ℝ)
    (329/512:ℝ) (3221257049/100000000000000:ℝ) (-35780391056966759944357/50000000000000000000000000:ℝ) (2886784644269605718733/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_328
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0985).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_328 :
    (∫ x in (41/64:ℝ)..(329/512:ℝ), x^2*thetaFirstMode x) ≤ (26468107025773353/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (41/64:ℝ) (329/512:ℝ)
    (672764353/20000000000000:ℝ) (402658587/12500000000000:ℝ) (2886784644269605718733/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_328 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0985).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_329 :
    (5099689828985677/200000000000000000000000:ℝ) ≤ ∫ x in (329/512:ℝ)..(165/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-8942277290302605047211725741/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (329/512:ℝ) (165/256:ℝ)-(7939328572536936611841/12355124896752488296960:ℝ)*thetaPowerMass 2 (329/512:ℝ) (165/256:ℝ)) ≤
      thetaFirstModeFirst (7939328572536936611841/12355124896752488296960:ℝ)*(thetaPowerMass 3 (329/512:ℝ) (165/256:ℝ)-(7939328572536936611841/12355124896752488296960:ℝ)*thetaPowerMass 2 (329/512:ℝ) (165/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0498.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (329/512:ℝ) (165/256:ℝ)
    (7939328572536936611841/12355124896752488296960:ℝ) (3220124419/100000000000000:ℝ) (-8942277290302605047211725741/12500000000000000000000000000000:ℝ) (1742053836423642278459/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_329
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0989).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_329 :
    (∫ x in (329/512:ℝ)..(165/256:ℝ), x^2*thetaFirstMode x) ≤ (796837267151417/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (329/512:ℝ) (165/256:ℝ)
    (402658587/12500000000000:ℝ) (3084222233/100000000000000:ℝ) (1742053836423642278459/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_329 (thetaFirstMode_refined_node_0985).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_330 :
    (24560045505864361/1000000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(331/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-8264487536898670143269/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (165/256:ℝ) (331/512:ℝ)-(331/512:ℝ)*thetaPowerMass 2 (165/256:ℝ) (331/512:ℝ)) ≤
      thetaFirstModeFirst (331/512:ℝ)*(thetaPowerMass 3 (165/256:ℝ) (331/512:ℝ)-(331/512:ℝ)*thetaPowerMass 2 (165/256:ℝ) (331/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0500.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (165/256:ℝ) (331/512:ℝ)
    (331/512:ℝ) (1476240913/50000000000000:ℝ) (-8264487536898670143269/12500000000000000000000000:ℝ) (6726854505705281028953/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_330
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0991).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_330 :
    (∫ x in (165/256:ℝ)..(331/512:ℝ), x^2*thetaFirstMode x) ≤ (2456025883367539/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (165/256:ℝ) (331/512:ℝ)
    (3084222233/100000000000000:ℝ) (590498517/20000000000000:ℝ) (6726854505705281028953/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_330 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0991).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_331 :
    (1478211737216203/62500000000000000000000:ℝ) ≤ ∫ x in (331/512:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-16523749262706267606642499877/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (331/512:ℝ) (83/128:ℝ)-(8384401329530932495359/12968909374505557020160:ℝ)*thetaPowerMass 2 (331/512:ℝ) (83/128:ℝ)) ≤
      thetaFirstModeFirst (8384401329530932495359/12968909374505557020160:ℝ)*(thetaPowerMass 3 (331/512:ℝ) (83/128:ℝ)-(8384401329530932495359/12968909374505557020160:ℝ)*thetaPowerMass 2 (331/512:ℝ) (83/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0501.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (331/512:ℝ) (83/128:ℝ)
    (8384401329530932495359/12968909374505557020160:ℝ) (1475720849/50000000000000:ℝ) (-16523749262706267606642499877/25000000000000000000000000000000:ℝ) (2597081084548014810409/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_331
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0995).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_331 :
    (∫ x in (331/512:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x) ≤ (23651713329996849/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (331/512:ℝ) (83/128:ℝ)
    (590498517/20000000000000:ℝ) (2825895597/100000000000000:ℝ) (2597081084548014810409/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_331 (thetaFirstMode_refined_node_0991).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_332 :
    (22772175623246709/1000000000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(333/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-3815159900926830556653/6250000000000000000000000:ℝ)*(thetaPowerMass 3 (83/128:ℝ) (333/512:ℝ)-(333/512:ℝ)*thetaPowerMass 2 (83/128:ℝ) (333/512:ℝ)) ≤
      thetaFirstModeFirst (333/512:ℝ)*(thetaPowerMass 3 (83/128:ℝ) (333/512:ℝ)-(333/512:ℝ)*thetaPowerMass 2 (83/128:ℝ) (333/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0503.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (83/128:ℝ) (333/512:ℝ)
    (333/512:ℝ) (2704242681/100000000000000:ℝ) (-3815159900926830556653/6250000000000000000000000:ℝ) (2506234554697104736573/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_332
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0997).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_332 :
    (∫ x in (83/128:ℝ)..(333/512:ℝ), x^2*thetaFirstMode x) ≤ (22772377186421489/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (83/128:ℝ) (333/512:ℝ)
    (2825895597/100000000000000:ℝ) (2704252613/100000000000000:ℝ) (2506234554697104736573/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_332 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_0997).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_333 :
    (21921176877303761/1000000000000000000000000:ℝ) ≤ ∫ x in (333/512:ℝ)..(167/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-15255801634371376874784358983/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (333/512:ℝ) (167/256:ℝ)-(8851515743072711040057/13609210458953895708160:ℝ)*thetaPowerMass 2 (333/512:ℝ) (167/256:ℝ)) ≤
      thetaFirstModeFirst (8851515743072711040057/13609210458953895708160:ℝ)*(thetaPowerMass 3 (333/512:ℝ) (167/256:ℝ)-(8851515743072711040057/13609210458953895708160:ℝ)*thetaPowerMass 2 (333/512:ℝ) (167/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0504.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (333/512:ℝ) (167/256:ℝ)
    (8851515743072711040057/13609210458953895708160:ℝ) (1351644067/50000000000000:ℝ) (-15255801634371376874784358983/25000000000000000000000000000000:ℝ) (12090669538846831606073/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_333
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1001).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_333 :
    (∫ x in (333/512:ℝ)..(167/256:ℝ), x^2*thetaFirstMode x) ≤ (21921485246860769/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (333/512:ℝ) (167/256:ℝ)
    (2704252613/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (12090669538846831606073/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_333 (thetaFirstMode_refined_node_0997).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_334 :
    (21098095737301721/1000000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(335/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-5631876698160076126059/10000000000000000000000000:ℝ)*(thetaPowerMass 3 (167/256:ℝ) (335/512:ℝ)-(335/512:ℝ)*thetaPowerMass 2 (167/256:ℝ) (335/512:ℝ)) ≤
      thetaFirstModeFirst (335/512:ℝ)*(thetaPowerMass 3 (167/256:ℝ) (335/512:ℝ)-(335/512:ℝ)*thetaPowerMass 2 (167/256:ℝ) (335/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0506.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (167/256:ℝ) (335/512:ℝ)
    (335/512:ℝ) (495026317/20000000000000:ℝ) (-5631876698160076126059/10000000000000000000000000:ℝ) (11663559777958023968721/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_334
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1003).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_334 :
    (∫ x in (167/256:ℝ)..(335/512:ℝ), x^2*thetaFirstMode x) ≤ (10549143022259377/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (167/256:ℝ) (335/512:ℝ)
    (1293695173/50000000000000:ℝ) (2475140747/100000000000000:ℝ) (11663559777958023968721/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_334 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1003).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_335 :
    (10150874930921449/500000000000000000000000:ℝ) ≤ ∫ x in (335/512:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x := by
  have hd : (-14075215871695182252788843799/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (335/512:ℝ) (21/32:ℝ)-(1868324221273231476315/2855400814247135293952:ℝ)*thetaPowerMass 2 (335/512:ℝ) (21/32:ℝ)) ≤
      thetaFirstModeFirst (1868324221273231476315/2855400814247135293952:ℝ)*(thetaPowerMass 3 (335/512:ℝ) (21/32:ℝ)-(1868324221273231476315/2855400814247135293952:ℝ)*thetaPowerMass 2 (335/512:ℝ) (21/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0507.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (335/512:ℝ) (21/32:ℝ)
    (1868324221273231476315/2855400814247135293952:ℝ) (2474256163/100000000000000:ℝ) (-14075215871695182252788843799/25000000000000000000000000000000:ℝ) (449980526649808350319/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_335
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1007).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_335 :
    (∫ x in (335/512:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x) ≤ (507551044118381/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (335/512:ℝ) (21/32:ℝ)
    (2475140747/100000000000000:ℝ) (1183670437/50000000000000:ℝ) (449980526649808350319/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_335 (thetaFirstMode_refined_node_1003).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_336 :
    (19531848664446097/1000000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(337/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1038471900283432150683/2000000000000000000000000:ℝ)*(thetaPowerMass 3 (21/32:ℝ) (337/512:ℝ)-(337/512:ℝ)*thetaPowerMass 2 (21/32:ℝ) (337/512:ℝ)) ≤
      thetaFirstModeFirst (337/512:ℝ)*(thetaPowerMass 3 (21/32:ℝ) (337/512:ℝ)-(337/512:ℝ)*thetaPowerMass 2 (21/32:ℝ) (337/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0509.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (21/32:ℝ) (337/512:ℝ)
    (337/512:ℝ) (90552973/4000000000000:ℝ) (-1038471900283432150683/2000000000000000000000000:ℝ) (2712051236299203677233/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_336
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1009).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_336 :
    (∫ x in (21/32:ℝ)..(337/512:ℝ), x^2*thetaFirstMode x) ≤ (76296985227941/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (21/32:ℝ) (337/512:ℝ)
    (1183670437/50000000000000:ℝ) (226383277/10000000000000:ℝ) (2712051236299203677233/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_336 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1009).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_337 :
    (18787258719049813/1000000000000000000000000:ℝ) ≤ ∫ x in (337/512:ℝ)..(169/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-12976760702627967184139025547/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (337/512:ℝ) (169/256:ℝ)-(9855701543199181141593/14973295882550797212160:ℝ)*thetaPowerMass 2 (337/512:ℝ) (169/256:ℝ)) ≤
      thetaFirstModeFirst (9855701543199181141593/14973295882550797212160:ℝ)*(thetaPowerMass 3 (337/512:ℝ) (169/256:ℝ)-(9855701543199181141593/14973295882550797212160:ℝ)*thetaPowerMass 2 (337/512:ℝ) (169/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0510.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (337/512:ℝ) (169/256:ℝ)
    (9855701543199181141593/14973295882550797212160:ℝ) (565755503/25000000000000:ℝ) (-12976760702627967184139025547/25000000000000000000000000000000:ℝ) (1045931593457899070031/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_337
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1013).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_337 :
    (∫ x in (337/512:ℝ)..(169/256:ℝ), x^2*thetaFirstMode x) ≤ (18787534818172419/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (337/512:ℝ) (169/256:ℝ)
    (226383277/10000000000000:ℝ) (2164463339/100000000000000:ℝ) (1045931593457899070031/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_337 (thetaFirstMode_refined_node_1009).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_338 :
    (2258461903826229/125000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(339/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-5979641895920786498487/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (169/256:ℝ) (339/512:ℝ)-(339/512:ℝ)*thetaPowerMass 2 (169/256:ℝ) (339/512:ℝ)) ≤
      thetaFirstModeFirst (339/512:ℝ)*(thetaPowerMass 3 (169/256:ℝ) (339/512:ℝ)-(339/512:ℝ)*thetaPowerMass 2 (169/256:ℝ) (339/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0512.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (169/256:ℝ) (339/512:ℝ)
    (339/512:ℝ) (2069076441/100000000000000:ℝ) (-5979641895920786498487/12500000000000000000000000:ℝ) (5041266247114722322963/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_338
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1015).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_338 :
    (∫ x in (169/256:ℝ)..(339/512:ℝ), x^2*thetaFirstMode x) ≤ (9033932256227617/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (169/256:ℝ) (339/512:ℝ)
    (2164463339/100000000000000:ℝ) (103454211/5000000000000:ℝ) (5041266247114722322963/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_338 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1015).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_339 :
    (17372072766362357/1000000000000000000000000:ℝ) ≤ ∫ x in (339/512:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-747216294124166881302501399/1562500000000000000000000000000:ℝ)*(thetaPowerMass 3 (339/512:ℝ) (85/128:ℝ)-(10394777066482805050791/15699122035309073589760:ℝ)*thetaPowerMass 2 (339/512:ℝ) (85/128:ℝ)) ≤
      thetaFirstModeFirst (10394777066482805050791/15699122035309073589760:ℝ)*(thetaPowerMass 3 (339/512:ℝ) (85/128:ℝ)-(10394777066482805050791/15699122035309073589760:ℝ)*thetaPowerMass 2 (339/512:ℝ) (85/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0513.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (339/512:ℝ) (85/128:ℝ)
    (10394777066482805050791/15699122035309073589760:ℝ) (16158919/781250000000:ℝ) (-747216294124166881302501399/1562500000000000000000000000000:ℝ) (9717546511209071045359/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_339
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1019).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_339 :
    (∫ x in (339/512:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x) ≤ (17372333725937513/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (339/512:ℝ) (85/128:ℝ)
    (103454211/5000000000000:ℝ) (1977551671/100000000000000:ℝ) (9717546511209071045359/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_339 (thetaFirstMode_refined_node_1015).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_340 :
    (16700112824679331/1000000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(341/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-11010117211927961486661/25000000000000000000000000:ℝ)*(thetaPowerMass 3 (85/128:ℝ) (341/512:ℝ)-(341/512:ℝ)*thetaPowerMass 2 (85/128:ℝ) (341/512:ℝ)) ≤
      thetaFirstModeFirst (341/512:ℝ)*(thetaPowerMass 3 (85/128:ℝ) (341/512:ℝ)-(341/512:ℝ)*thetaPowerMass 2 (85/128:ℝ) (341/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0515.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (85/128:ℝ) (341/512:ℝ)
    (341/512:ℝ) (1889719291/100000000000000:ℝ) (-11010117211927961486661/25000000000000000000000000:ℝ) (1170506923053822489801/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_340
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1021).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_340 :
    (∫ x in (85/128:ℝ)..(341/512:ℝ), x^2*thetaFirstMode x) ≤ (16700272313613203/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (85/128:ℝ) (341/512:ℝ)
    (1977551671/100000000000000:ℝ) (472431613/25000000000000:ℝ) (1170506923053822489801/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_340 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1021).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_341 :
    (1605077700183901/100000000000000000000000:ℝ) ≤ ∫ x in (341/512:ℝ)..(171/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2751646894917022496316655149/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (341/512:ℝ) (171/256:ℝ)-(10959904662371742259809/16455549877310448463360:ℝ)*thetaPowerMass 2 (341/512:ℝ) (171/256:ℝ)) ≤
      thetaFirstModeFirst (10959904662371742259809/16455549877310448463360:ℝ)*(thetaPowerMass 3 (341/512:ℝ) (171/256:ℝ)-(10959904662371742259809/16455549877310448463360:ℝ)*thetaPowerMass 2 (341/512:ℝ) (171/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0516.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (341/512:ℝ) (171/256:ℝ)
    (10959904662371742259809/16455549877310448463360:ℝ) (1889046769/100000000000000:ℝ) (-2751646894917022496316655149/6250000000000000000000000000000:ℝ) (902176198681593383143/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_341
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1025).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_341 :
    (∫ x in (341/512:ℝ)..(171/256:ℝ), x^2*thetaFirstMode x) ≤ (2006377934552601/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (341/512:ℝ) (171/256:ℝ)
    (472431613/25000000000000:ℝ) (902736853/50000000000000:ℝ) (902176198681593383143/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_341 (thetaFirstMode_refined_node_1021).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_342 :
    (15423793530368871/1000000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(343/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-5064453976706091210187/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (171/256:ℝ) (343/512:ℝ)-(343/512:ℝ)*thetaPowerMass 2 (171/256:ℝ) (343/512:ℝ)) ≤
      thetaFirstModeFirst (343/512:ℝ)*(thetaPowerMass 3 (171/256:ℝ) (343/512:ℝ)-(343/512:ℝ)*thetaPowerMass 2 (171/256:ℝ) (343/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0518.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (171/256:ℝ) (343/512:ℝ)
    (343/512:ℝ) (862328131/50000000000000:ℝ) (-5064453976706091210187/12500000000000000000000000:ℝ) (4345187324651066737441/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_342
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1027).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_342 :
    (∫ x in (171/256:ℝ)..(343/512:ℝ), x^2*thetaFirstMode x) ≤ (15423943677298889/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (171/256:ℝ) (343/512:ℝ)
    (902736853/50000000000000:ℝ) (26947857/1562500000000:ℝ) (4345187324651066737441/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_342 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1027).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_343 :
    (14818169964664689/1000000000000000000000000:ℝ) ≤ ∫ x in (343/512:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-10125651529677904809646813429/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (343/512:ℝ) (43/64:ℝ)-(11552179400427359855007/17243678709113286300160:ℝ)*thetaPowerMass 2 (343/512:ℝ) (43/64:ℝ)) ≤
      thetaFirstModeFirst (11552179400427359855007/17243678709113286300160:ℝ)*(thetaPowerMass 3 (343/512:ℝ) (43/64:ℝ)-(11552179400427359855007/17243678709113286300160:ℝ)*thetaPowerMass 2 (343/512:ℝ) (43/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0519.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (343/512:ℝ) (43/64:ℝ)
    (11552179400427359855007/17243678709113286300160:ℝ) (1724041173/100000000000000:ℝ) (-10125651529677904809646813429/25000000000000000000000000000000:ℝ) (4184803553622849574231/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_343
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1031).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_343 :
    (∫ x in (343/512:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x) ≤ (7409201287922801/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (343/512:ℝ) (43/64:ℝ)
    (26947857/1562500000000:ℝ) (51473983/3125000000000:ℝ) (4184803553622849574231/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_343 (thetaFirstMode_refined_node_1027).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_344 :
    (711682083321287/50000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(345/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-9311394941907337555997/25000000000000000000000000:ℝ)*(thetaPowerMass 3 (43/64:ℝ) (345/512:ℝ)-(345/512:ℝ)*thetaPowerMass 2 (43/64:ℝ) (345/512:ℝ)) ≤
      thetaFirstModeFirst (345/512:ℝ)*(thetaPowerMass 3 (43/64:ℝ) (345/512:ℝ)-(345/512:ℝ)*thetaPowerMass 2 (43/64:ℝ) (345/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0521.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (43/64:ℝ) (345/512:ℝ)
    (345/512:ℝ) (786429551/50000000000000:ℝ) (-9311394941907337555997/25000000000000000000000000:ℝ) (8059178514888556234447/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_344
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1033).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_344 :
    (∫ x in (43/64:ℝ)..(345/512:ℝ), x^2*thetaFirstMode x) ≤ (14233782921081541/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (43/64:ℝ) (345/512:ℝ)
    (51473983/3125000000000:ℝ) (393216289/25000000000000:ℝ) (8059178514888556234447/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_344 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1033).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_345 :
    (13669261086548119/1000000000000000000000000:ℝ) ≤ ∫ x in (345/512:ℝ)..(173/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-9308392710025231478938235433/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (345/512:ℝ) (173/256:ℝ)-(2434547114057885834205/3612928108949549783552:ℝ)*thetaPowerMass 2 (345/512:ℝ) (173/256:ℝ)) ≤
      thetaFirstModeFirst (2434547114057885834205/3612928108949549783552:ℝ)*(thetaPowerMass 3 (345/512:ℝ) (173/256:ℝ)-(2434547114057885834205/3612928108949549783552:ℝ)*thetaPowerMass 2 (345/512:ℝ) (173/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0522.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (345/512:ℝ) (173/256:ℝ)
    (2434547114057885834205/3612928108949549783552:ℝ) (314459387/20000000000000:ℝ) (-9308392710025231478938235433/25000000000000000000000000000000:ℝ) (12123145869520086023/1562500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_345
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1037).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_345 :
    (∫ x in (345/512:ℝ)..(173/256:ℝ), x^2*thetaFirstMode x) ≤ (2733896090066113/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (345/512:ℝ) (173/256:ℝ)
    (393216289/25000000000000:ℝ) (18770469/1250000000000:ℝ) (12123145869520086023/1562500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_345 (thetaFirstMode_refined_node_1033).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_346 :
    (13124771022363249/1000000000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(347/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-42767693318296663223/125000000000000000000000:ℝ)*(thetaPowerMass 3 (173/256:ℝ) (347/512:ℝ)-(347/512:ℝ)*thetaPowerMass 2 (173/256:ℝ) (347/512:ℝ)) ≤
      thetaFirstModeFirst (347/512:ℝ)*(thetaPowerMass 3 (173/256:ℝ) (347/512:ℝ)-(347/512:ℝ)*thetaPowerMass 2 (173/256:ℝ) (347/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0524.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (173/256:ℝ) (347/512:ℝ)
    (347/512:ℝ) (3583411/250000000000:ℝ) (-42767693318296663223/125000000000000000000000:ℝ) (466765090716006631209/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_346
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1039).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_346 :
    (∫ x in (173/256:ℝ)..(347/512:ℝ), x^2*thetaFirstMode x) ≤ (13124903803868489/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (173/256:ℝ) (347/512:ℝ)
    (18770469/1250000000000:ℝ) (35834249/2500000000000:ℝ) (466765090716006631209/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_346 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1039).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_347 :
    (1574908461847519/125000000000000000000000:ℝ) ≤ ∫ x in (347/512:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-17101545515717541399376803969/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (347/512:ℝ) (87/128:ℝ)-(12822747845328599226543/18919600885932177948160:ℝ)*thetaPowerMass 2 (347/512:ℝ) (87/128:ℝ)) ≤
      thetaFirstModeFirst (12822747845328599226543/18919600885932177948160:ℝ)*(thetaPowerMass 3 (347/512:ℝ) (87/128:ℝ)-(12822747845328599226543/18919600885932177948160:ℝ)*thetaPowerMass 2 (347/512:ℝ) (87/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0525.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (347/512:ℝ) (87/128:ℝ)
    (12822747845328599226543/18919600885932177948160:ℝ) (286570193/20000000000000:ℝ) (-17101545515717541399376803969/50000000000000000000000000000000:ℝ) (3593598945580688865067/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_347
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1043).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_347 :
    (∫ x in (347/512:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x) ≤ (2519894879656509/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (347/512:ℝ) (87/128:ℝ)
    (35834249/2500000000000:ℝ) (683975811/50000000000000:ℝ) (3593598945580688865067/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_347 (thetaFirstMode_refined_node_1039).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_348 :
    (1209250157422403/100000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(349/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1962878190904528220173/6250000000000000000000000:ℝ)*(thetaPowerMass 3 (87/128:ℝ) (349/512:ℝ)-(349/512:ℝ)*thetaPowerMass 2 (87/128:ℝ) (349/512:ℝ)) ≤
      thetaFirstModeFirst (349/512:ℝ)*(thetaPowerMass 3 (87/128:ℝ) (349/512:ℝ)-(349/512:ℝ)*thetaPowerMass 2 (87/128:ℝ) (349/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0527.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (87/128:ℝ) (349/512:ℝ)
    (349/512:ℝ) (163158773/12500000000000:ℝ) (-1962878190904528220173/6250000000000000000000000:ℝ) (1383084605119152080019/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_348
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1045).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_348 :
    (∫ x in (87/128:ℝ)..(349/512:ℝ), x^2*thetaFirstMode x) ≤ (12092626307239313/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (87/128:ℝ) (349/512:ℝ)
    (683975811/50000000000000:ℝ) (1305275287/100000000000000:ℝ) (1383084605119152080019/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_348 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1045).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_349 :
    (464144460953171/40000000000000000000000:ℝ) ≤ ∫ x in (349/512:ℝ)..(175/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-3924483208224762998804737941/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (349/512:ℝ) (175/256:ℝ)-(13503432473757098003241/19809759509951338370560:ℝ)*thetaPowerMass 2 (349/512:ℝ) (175/256:ℝ)) ≤
      thetaFirstModeFirst (13503432473757098003241/19809759509951338370560:ℝ)*(thetaPowerMass 3 (349/512:ℝ) (175/256:ℝ)-(13503432473757098003241/19809759509951338370560:ℝ)*thetaPowerMass 2 (349/512:ℝ) (175/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0528.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (349/512:ℝ) (175/256:ℝ)
    (13503432473757098003241/19809759509951338370560:ℝ) (1304801589/100000000000000:ℝ) (-3924483208224762998804737941/12500000000000000000000000000000:ℝ) (415791399088820588141/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_349
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1049).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_349 :
    (∫ x in (349/512:ℝ)..(175/256:ℝ), x^2*thetaFirstMode x) ≤ (11603806159685499/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (349/512:ℝ) (175/256:ℝ)
    (1305275287/100000000000000:ℝ) (622618637/50000000000000:ℝ) (415791399088820588141/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_349 (thetaFirstMode_refined_node_1045).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_350 :
    (11132355919479983/1000000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(351/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-288067832501024132739/1000000000000000000000000:ℝ)*(thetaPowerMass 3 (175/256:ℝ) (351/512:ℝ)-(351/512:ℝ)*thetaPowerMass 2 (175/256:ℝ) (351/512:ℝ)) ≤
      thetaFirstModeFirst (351/512:ℝ)*(thetaPowerMass 3 (175/256:ℝ) (351/512:ℝ)-(351/512:ℝ)*thetaPowerMass 2 (175/256:ℝ) (351/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0530.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (175/256:ℝ) (351/512:ℝ)
    (351/512:ℝ) (593866329/50000000000000:ℝ) (-288067832501024132739/1000000000000000000000000:ℝ) (3199333338005062984983/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_350
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1051).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_350 :
    (∫ x in (175/256:ℝ)..(351/512:ℝ), x^2*thetaFirstMode x) ≤ (11132473006418053/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (175/256:ℝ) (351/512:ℝ)
    (622618637/50000000000000:ℝ) (1187737339/100000000000000:ℝ) (3199333338005062984983/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_350 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1051).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_351 :
    (5338957531018163/500000000000000000000000:ℝ) ≤ ∫ x in (351/512:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x := by
  have hd : (-7199353298200506036368577071/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (351/512:ℝ) (11/16:ℝ)-(14216048497680767340759/20736351271356306434560:ℝ)*thetaPowerMass 2 (351/512:ℝ) (11/16:ℝ)) ≤
      thetaFirstModeFirst (14216048497680767340759/20736351271356306434560:ℝ)*(thetaPowerMass 3 (351/512:ℝ) (11/16:ℝ)-(14216048497680767340759/20736351271356306434560:ℝ)*thetaPowerMass 2 (351/512:ℝ) (11/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0531.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (351/512:ℝ) (11/16:ℝ)
    (14216048497680767340759/20736351271356306434560:ℝ) (74206581/6250000000000:ℝ) (-7199353298200506036368577071/25000000000000000000000000000000:ℝ) (1538297928038724187807/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_351
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1055).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_351 :
    (∫ x in (351/512:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x) ≤ (533904909104129/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (351/512:ℝ) (11/16:ℝ)
    (1187737339/100000000000000:ℝ) (566339291/50000000000000:ℝ) (1538297928038724187807/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_351 (thetaFirstMode_refined_node_1051).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature10
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative15
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative16

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_320 :
    (90419671249552071/1000000000000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(321/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-791458998900297830620934251/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (5/8:ℝ) (321/512:ℝ)-(5/8:ℝ)*thetaPowerMass 0 (5/8:ℝ) (321/512:ℝ)) ≤
      thetaFirstModeFirst (5/8:ℝ)*(thetaPowerMass 1 (5/8:ℝ) (321/512:ℝ)-(5/8:ℝ)*thetaPowerMass 0 (5/8:ℝ) (321/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0484.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (5/8:ℝ) (321/512:ℝ)
    (5/8:ℝ) (1181803051/25000000000000:ℝ) (-791458998900297830620934251/781250000000000000000000000000:ℝ) (18989797966138220160881/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_320
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0960).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_320 :
    (∫ x in (5/8:ℝ)..(321/512:ℝ), x^0*thetaFirstMode x) ≤ (45210397559376937/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/8:ℝ) (321/512:ℝ)
    (147725897/3125000000000:ℝ) (906613611/20000000000000:ℝ) (18989797966138220160881/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_320 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0961).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_321 :
    (86698663945192051/1000000000000000000000000:ℝ) ≤ ∫ x in (321/512:ℝ)..(161/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6094005007060073489706121177/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (321/512:ℝ) (161/256:ℝ)-(6361630132651141262409/10146636573905784424960:ℝ)*thetaPowerMass 0 (321/512:ℝ) (161/256:ℝ)) ≤
      thetaFirstModeFirst (6361630132651141262409/10146636573905784424960:ℝ)*(thetaPowerMass 1 (321/512:ℝ) (161/256:ℝ)-(6361630132651141262409/10146636573905784424960:ℝ)*thetaPowerMass 0 (321/512:ℝ) (161/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0486.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (321/512:ℝ) (161/256:ℝ)
    (6361630132651141262409/10146636573905784424960:ℝ) (283216873/6250000000000:ℝ) (-6094005007060073489706121177/6250000000000000000000000000000:ℝ) (18360765920791664960263/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_321
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0965).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_321 :
    (∫ x in (321/512:ℝ)..(161/256:ℝ), x^0*thetaFirstMode x) ≤ (86699733905671741/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (321/512:ℝ) (161/256:ℝ)
    (906613611/20000000000000:ℝ) (4346152043/100000000000000:ℝ) (18360765920791664960263/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_321 (thetaFirstMode_refined_node_0961).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_322 :
    (83116759404978913/1000000000000000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(323/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-23471912218371399747625056219/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (161/256:ℝ) (323/512:ℝ)-(161/256:ℝ)*thetaPowerMass 0 (161/256:ℝ) (323/512:ℝ)) ≤
      thetaFirstModeFirst (161/256:ℝ)*(thetaPowerMass 1 (161/256:ℝ) (323/512:ℝ)-(161/256:ℝ)*thetaPowerMass 0 (161/256:ℝ) (323/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0487.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (161/256:ℝ) (323/512:ℝ)
    (161/256:ℝ) (2173068377/50000000000000:ℝ) (-23471912218371399747625056219/25000000000000000000000000000000:ℝ) (2218691076948617867173/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_322
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0966).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_322 :
    (∫ x in (161/256:ℝ)..(323/512:ℝ), x^0*thetaFirstMode x) ≤ (16623563000707161/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (161/256:ℝ) (323/512:ℝ)
    (4346152043/100000000000000:ℝ) (2083120349/50000000000000:ℝ) (2218691076948617867173/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_322 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0967).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_323 :
    (39834706689117161/500000000000000000000000:ℝ) ≤ ∫ x in (323/512:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-705725860557885863401761009/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (323/512:ℝ) (81/128:ℝ)-(6727368238177514567607/10663543358416903452160:ℝ)*thetaPowerMass 0 (323/512:ℝ) (81/128:ℝ)) ≤
      thetaFirstModeFirst (6727368238177514567607/10663543358416903452160:ℝ)*(thetaPowerMass 1 (323/512:ℝ) (81/128:ℝ)-(6727368238177514567607/10663543358416903452160:ℝ)*thetaPowerMass 0 (323/512:ℝ) (81/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0489.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (323/512:ℝ) (81/128:ℝ)
    (6727368238177514567607/10663543358416903452160:ℝ) (520596153/12500000000000:ℝ) (-705725860557885863401761009/781250000000000000000000000000:ℝ) (17155688547831666497587/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_323
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0971).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_323 :
    (∫ x in (323/512:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x) ≤ (79670418024382597/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (323/512:ℝ) (81/128:ℝ)
    (2083120349/50000000000000:ℝ) (3993100837/100000000000000:ℝ) (17155688547831666497587/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_323 (thetaFirstMode_refined_node_0967).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_324 :
    (954400785658897/12500000000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(325/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5434567492845972621105473673/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (81/128:ℝ) (325/512:ℝ)-(81/128:ℝ)*thetaPowerMass 0 (81/128:ℝ) (325/512:ℝ)) ≤
      thetaFirstModeFirst (81/128:ℝ)*(thetaPowerMass 1 (81/128:ℝ) (325/512:ℝ)-(81/128:ℝ)*thetaPowerMass 0 (81/128:ℝ) (325/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0490.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (81/128:ℝ) (325/512:ℝ)
    (81/128:ℝ) (99827167/2500000000000:ℝ) (-5434567492845972621105473673/6250000000000000000000000000000:ℝ) (4144713437913322237179/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_324
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0972).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_324 :
    (∫ x in (81/128:ℝ)..(325/512:ℝ), x^0*thetaFirstMode x) ≤ (76353053690092183/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (81/128:ℝ) (325/512:ℝ)
    (3993100837/100000000000000:ℝ) (956626479/25000000000000:ℝ) (4144713437913322237179/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_324 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0973).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_325 :
    (73160418159071541/1000000000000000000000000:ℝ) ≤ ∫ x in (325/512:ℝ)..(163/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2613512127401811263897992001/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (325/512:ℝ) (163/256:ℝ)-(1422335766498956948925/2240669318036578698752:ℝ)*thetaPowerMass 0 (325/512:ℝ) (163/256:ℝ)) ≤
      thetaFirstModeFirst (1422335766498956948925/2240669318036578698752:ℝ)*(thetaPowerMass 1 (325/512:ℝ) (163/256:ℝ)-(1422335766498956948925/2240669318036578698752:ℝ)*thetaPowerMass 0 (325/512:ℝ) (163/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0492.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (325/512:ℝ) (163/256:ℝ)
    (1422335766498956948925/2240669318036578698752:ℝ) (3825151891/100000000000000:ℝ) (-2613512127401811263897992001/3125000000000000000000000000000:ℝ) (16018637837795994942557/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_325
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0977).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_325 :
    (∫ x in (325/512:ℝ)..(163/256:ℝ), x^0*thetaFirstMode x) ≤ (73161360892910339/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (325/512:ℝ) (163/256:ℝ)
    (956626479/25000000000000:ℝ) (3666235877/100000000000000:ℝ) (16018637837795994942557/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_325 (thetaFirstMode_refined_node_0973).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_326 :
    (35045087141343881/500000000000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(327/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-20118964508744370567517685883/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (163/256:ℝ) (327/512:ℝ)-(163/256:ℝ)*thetaPowerMass 0 (163/256:ℝ) (327/512:ℝ)) ≤
      thetaFirstModeFirst (163/256:ℝ)*(thetaPowerMass 1 (163/256:ℝ) (327/512:ℝ)-(163/256:ℝ)*thetaPowerMass 0 (163/256:ℝ) (327/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0493.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (163/256:ℝ) (327/512:ℝ)
    (163/256:ℝ) (458277847/12500000000000:ℝ) (-20118964508744370567517685883/25000000000000000000000000000000:ℝ) (7737329995450590364139/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_326
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0978).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_326 :
    (∫ x in (163/256:ℝ)..(327/512:ℝ), x^0*thetaFirstMode x) ≤ (35045551882881367/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (163/256:ℝ) (327/512:ℝ)
    (3666235877/100000000000000:ℝ) (3512077001/100000000000000:ℝ) (7737329995450590364139/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_326 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0979).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_327 :
    (33568642380503141/500000000000000000000000:ℝ) ≤ ∫ x in (327/512:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9671993372483767377048527433/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (327/512:ℝ) (41/64:ℝ)-(7515381976057835704143/11766910146346930332160:ℝ)*thetaPowerMass 0 (327/512:ℝ) (41/64:ℝ)) ≤
      thetaFirstModeFirst (7515381976057835704143/11766910146346930332160:ℝ)*(thetaPowerMass 1 (327/512:ℝ) (41/64:ℝ)-(7515381976057835704143/11766910146346930332160:ℝ)*thetaPowerMass 0 (327/512:ℝ) (41/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0495.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (327/512:ℝ) (41/64:ℝ)
    (7515381976057835704143/11766910146346930332160:ℝ) (1755415927/50000000000000:ℝ) (-9671993372483767377048527433/12500000000000000000000000000000:ℝ) (3736636247141410437059/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_327
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0983).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_327 :
    (∫ x in (327/512:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x) ≤ (33569084425105923/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (327/512:ℝ) (41/64:ℝ)
    (3512077001/100000000000000:ℝ) (672764353/20000000000000:ℝ) (3736636247141410437059/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_327 (thetaFirstMode_refined_node_0979).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_328 :
    (64297690916933767/1000000000000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(329/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7443001259731937866431915817/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (41/64:ℝ) (329/512:ℝ)-(41/64:ℝ)*thetaPowerMass 0 (41/64:ℝ) (329/512:ℝ)) ≤
      thetaFirstModeFirst (41/64:ℝ)*(thetaPowerMass 1 (41/64:ℝ) (329/512:ℝ)-(41/64:ℝ)*thetaPowerMass 0 (41/64:ℝ) (329/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0496.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (41/64:ℝ) (329/512:ℝ)
    (41/64:ℝ) (67276193/2000000000000:ℝ) (-7443001259731937866431915817/10000000000000000000000000000000:ℝ) (2886784644269605718733/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_328
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0984).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_328 :
    (∫ x in (41/64:ℝ)..(329/512:ℝ), x^0*thetaFirstMode x) ≤ (1607464056854473/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/64:ℝ) (329/512:ℝ)
    (672764353/20000000000000:ℝ) (402658587/12500000000000:ℝ) (2886784644269605718733/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_328 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0985).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_329 :
    (61567578434826911/1000000000000000000000000:ℝ) ≤ ∫ x in (329/512:ℝ)..(165/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-8942277290302605047211725741/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (329/512:ℝ) (165/256:ℝ)-(7939328572536936611841/12355124896752488296960:ℝ)*thetaPowerMass 0 (329/512:ℝ) (165/256:ℝ)) ≤
      thetaFirstModeFirst (7939328572536936611841/12355124896752488296960:ℝ)*(thetaPowerMass 1 (329/512:ℝ) (165/256:ℝ)-(7939328572536936611841/12355124896752488296960:ℝ)*thetaPowerMass 0 (329/512:ℝ) (165/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0498.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (329/512:ℝ) (165/256:ℝ)
    (7939328572536936611841/12355124896752488296960:ℝ) (3220124419/100000000000000:ℝ) (-8942277290302605047211725741/12500000000000000000000000000000:ℝ) (1742053836423642278459/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_329
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0989).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_329 :
    (∫ x in (329/512:ℝ)..(165/256:ℝ), x^0*thetaFirstMode x) ≤ (30784203489253661/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (329/512:ℝ) (165/256:ℝ)
    (402658587/12500000000000:ℝ) (3084222233/100000000000000:ℝ) (1742053836423642278459/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_329 (thetaFirstMode_refined_node_0985).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_330 :
    (58943123651095813/1000000000000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(331/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17197688536797880496340921181/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (165/256:ℝ) (331/512:ℝ)-(165/256:ℝ)*thetaPowerMass 0 (165/256:ℝ) (331/512:ℝ)) ≤
      thetaFirstModeFirst (165/256:ℝ)*(thetaPowerMass 1 (165/256:ℝ) (331/512:ℝ)-(165/256:ℝ)*thetaPowerMass 0 (165/256:ℝ) (331/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0499.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (165/256:ℝ) (331/512:ℝ)
    (165/256:ℝ) (1542105519/50000000000000:ℝ) (-17197688536797880496340921181/25000000000000000000000000000000:ℝ) (6726854505705281028953/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_330
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0990).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_330 :
    (∫ x in (165/256:ℝ)..(331/512:ℝ), x^0*thetaFirstMode x) ≤ (58943939982588161/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (165/256:ℝ) (331/512:ℝ)
    (3084222233/100000000000000:ℝ) (590498517/20000000000000:ℝ) (6726854505705281028953/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_330 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0991).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_331 :
    (56420733707666839/1000000000000000000000000:ℝ) ≤ ∫ x in (331/512:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-16523749262706267606642499877/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (331/512:ℝ) (83/128:ℝ)-(8384401329530932495359/12968909374505557020160:ℝ)*thetaPowerMass 0 (331/512:ℝ) (83/128:ℝ)) ≤
      thetaFirstModeFirst (8384401329530932495359/12968909374505557020160:ℝ)*(thetaPowerMass 1 (331/512:ℝ) (83/128:ℝ)-(8384401329530932495359/12968909374505557020160:ℝ)*thetaPowerMass 0 (331/512:ℝ) (83/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0501.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (331/512:ℝ) (83/128:ℝ)
    (8384401329530932495359/12968909374505557020160:ℝ) (1475720849/50000000000000:ℝ) (-16523749262706267606642499877/25000000000000000000000000000000:ℝ) (2597081084548014810409/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_331
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0995).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_331 :
    (∫ x in (331/512:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x) ≤ (14105377422259149/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (331/512:ℝ) (83/128:ℝ)
    (590498517/20000000000000:ℝ) (2825895597/100000000000000:ℝ) (2597081084548014810409/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_331 (thetaFirstMode_refined_node_0991).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_332 :
    (6749601119137451/125000000000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(333/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-31767219768252516681463498833/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (83/128:ℝ) (333/512:ℝ)-(83/128:ℝ)*thetaPowerMass 0 (83/128:ℝ) (333/512:ℝ)) ≤
      thetaFirstModeFirst (83/128:ℝ)*(thetaPowerMass 1 (83/128:ℝ) (333/512:ℝ)-(83/128:ℝ)*thetaPowerMass 0 (83/128:ℝ) (333/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0502.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (83/128:ℝ) (333/512:ℝ)
    (83/128:ℝ) (2825885259/100000000000000:ℝ) (-31767219768252516681463498833/50000000000000000000000000000000:ℝ) (2506234554697104736573/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_332
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0996).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_332 :
    (∫ x in (83/128:ℝ)..(333/512:ℝ), x^0*thetaFirstMode x) ≤ (10799514647444203/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (83/128:ℝ) (333/512:ℝ)
    (2825895597/100000000000000:ℝ) (2704252613/100000000000000:ℝ) (2506234554697104736573/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_332 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_0997).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_333 :
    (3229247976268787/62500000000000000000000:ℝ) ≤ ∫ x in (333/512:ℝ)..(167/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15255801634371376874784358983/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (333/512:ℝ) (167/256:ℝ)-(8851515743072711040057/13609210458953895708160:ℝ)*thetaPowerMass 0 (333/512:ℝ) (167/256:ℝ)) ≤
      thetaFirstModeFirst (8851515743072711040057/13609210458953895708160:ℝ)*(thetaPowerMass 1 (333/512:ℝ) (167/256:ℝ)-(8851515743072711040057/13609210458953895708160:ℝ)*thetaPowerMass 0 (333/512:ℝ) (167/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0504.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (333/512:ℝ) (167/256:ℝ)
    (8851515743072711040057/13609210458953895708160:ℝ) (1351644067/50000000000000:ℝ) (-15255801634371376874784358983/25000000000000000000000000000000:ℝ) (12090669538846831606073/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_333
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1001).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_333 :
    (∫ x in (333/512:ℝ)..(167/256:ℝ), x^0*thetaFirstMode x) ≤ (25834346947914273/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (333/512:ℝ) (167/256:ℝ)
    (2704252613/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (12090669538846831606073/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_333 (thetaFirstMode_refined_node_0997).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_334 :
    (49430823439666487/1000000000000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(335/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3664908547132780791895251203/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (167/256:ℝ) (335/512:ℝ)-(167/256:ℝ)*thetaPowerMass 0 (167/256:ℝ) (335/512:ℝ)) ≤
      thetaFirstModeFirst (167/256:ℝ)*(thetaPowerMass 1 (167/256:ℝ) (335/512:ℝ)-(167/256:ℝ)*thetaPowerMass 0 (167/256:ℝ) (335/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0505.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (167/256:ℝ) (335/512:ℝ)
    (167/256:ℝ) (2587380807/100000000000000:ℝ) (-3664908547132780791895251203/6250000000000000000000000000000:ℝ) (11663559777958023968721/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_334
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1002).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_334 :
    (∫ x in (167/256:ℝ)..(335/512:ℝ), x^0*thetaFirstMode x) ≤ (49431538514063733/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (167/256:ℝ) (335/512:ℝ)
    (1293695173/50000000000000:ℝ) (2475140747/100000000000000:ℝ) (11663559777958023968721/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_334 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1003).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_335 :
    (47282195641691377/1000000000000000000000000:ℝ) ≤ ∫ x in (335/512:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-14075215871695182252788843799/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (335/512:ℝ) (21/32:ℝ)-(1868324221273231476315/2855400814247135293952:ℝ)*thetaPowerMass 0 (335/512:ℝ) (21/32:ℝ)) ≤
      thetaFirstModeFirst (1868324221273231476315/2855400814247135293952:ℝ)*(thetaPowerMass 1 (335/512:ℝ) (21/32:ℝ)-(1868324221273231476315/2855400814247135293952:ℝ)*thetaPowerMass 0 (335/512:ℝ) (21/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0507.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (335/512:ℝ) (21/32:ℝ)
    (1868324221273231476315/2855400814247135293952:ℝ) (2474256163/100000000000000:ℝ) (-14075215871695182252788843799/25000000000000000000000000000000:ℝ) (449980526649808350319/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_335
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1007).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_335 :
    (∫ x in (335/512:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x) ≤ (47282874963034687/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (335/512:ℝ) (21/32:ℝ)
    (2475140747/100000000000000:ℝ) (1183670437/50000000000000:ℝ) (449980526649808350319/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_335 (thetaFirstMode_refined_node_1003).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_336 :
    (45218901067169903/1000000000000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(337/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6760198740043604216894630911/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (21/32:ℝ) (337/512:ℝ)-(21/32:ℝ)*thetaPowerMass 0 (21/32:ℝ) (337/512:ℝ)) ≤
      thetaFirstModeFirst (21/32:ℝ)*(thetaPowerMass 1 (21/32:ℝ) (337/512:ℝ)-(21/32:ℝ)*thetaPowerMass 0 (21/32:ℝ) (337/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0508.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (21/32:ℝ) (337/512:ℝ)
    (21/32:ℝ) (2367332077/100000000000000:ℝ) (-6760198740043604216894630911/12500000000000000000000000000000:ℝ) (2712051236299203677233/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_336
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1008).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_336 :
    (∫ x in (21/32:ℝ)..(337/512:ℝ), x^0*thetaFirstMode x) ≤ (11304892416270289/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/32:ℝ) (337/512:ℝ)
    (1183670437/50000000000000:ℝ) (226383277/10000000000000:ℝ) (2712051236299203677233/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_336 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1009).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_337 :
    (8647590048234013/200000000000000000000000:ℝ) ≤ ∫ x in (337/512:ℝ)..(169/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-12976760702627967184139025547/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (337/512:ℝ) (169/256:ℝ)-(9855701543199181141593/14973295882550797212160:ℝ)*thetaPowerMass 0 (337/512:ℝ) (169/256:ℝ)) ≤
      thetaFirstModeFirst (9855701543199181141593/14973295882550797212160:ℝ)*(thetaPowerMass 1 (337/512:ℝ) (169/256:ℝ)-(9855701543199181141593/14973295882550797212160:ℝ)*thetaPowerMass 0 (337/512:ℝ) (169/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0510.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (337/512:ℝ) (169/256:ℝ)
    (9855701543199181141593/14973295882550797212160:ℝ) (565755503/25000000000000:ℝ) (-12976760702627967184139025547/25000000000000000000000000000000:ℝ) (1045931593457899070031/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_337
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1013).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_337 :
    (∫ x in (337/512:ℝ)..(169/256:ℝ), x^0*thetaFirstMode x) ≤ (21619292595711593/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (337/512:ℝ) (169/256:ℝ)
    (226383277/10000000000000:ℝ) (2164463339/100000000000000:ℝ) (1045931593457899070031/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_337 (thetaFirstMode_refined_node_1009).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_338 :
    (10334088274656213/250000000000000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(339/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4984318413074371467019038923/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (169/256:ℝ) (339/512:ℝ)-(169/256:ℝ)*thetaPowerMass 0 (169/256:ℝ) (339/512:ℝ)) ≤
      thetaFirstModeFirst (169/256:ℝ)*(thetaPowerMass 1 (169/256:ℝ) (339/512:ℝ)-(169/256:ℝ)*thetaPowerMass 0 (169/256:ℝ) (339/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0511.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (169/256:ℝ) (339/512:ℝ)
    (169/256:ℝ) (2164455233/100000000000000:ℝ) (-4984318413074371467019038923/10000000000000000000000000000000:ℝ) (5041266247114722322963/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_338
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1014).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_338 :
    (∫ x in (169/256:ℝ)..(339/512:ℝ), x^0*thetaFirstMode x) ≤ (10334244455194649/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (169/256:ℝ) (339/512:ℝ)
    (2164463339/100000000000000:ℝ) (103454211/5000000000000:ℝ) (5041266247114722322963/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_338 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1015).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_339 :
    (1234728190376061/31250000000000000000000:ℝ) ≤ ∫ x in (339/512:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-747216294124166881302501399/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (339/512:ℝ) (85/128:ℝ)-(10394777066482805050791/15699122035309073589760:ℝ)*thetaPowerMass 0 (339/512:ℝ) (85/128:ℝ)) ≤
      thetaFirstModeFirst (10394777066482805050791/15699122035309073589760:ℝ)*(thetaPowerMass 1 (339/512:ℝ) (85/128:ℝ)-(10394777066482805050791/15699122035309073589760:ℝ)*thetaPowerMass 0 (339/512:ℝ) (85/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0513.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (339/512:ℝ) (85/128:ℝ)
    (10394777066482805050791/15699122035309073589760:ℝ) (16158919/781250000000:ℝ) (-747216294124166881302501399/1562500000000000000000000000000:ℝ) (9717546511209071045359/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_339
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1019).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_339 :
    (∫ x in (339/512:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x) ≤ (39511895176089699/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (339/512:ℝ) (85/128:ℝ)
    (103454211/5000000000000:ℝ) (1977551671/100000000000000:ℝ) (9717546511209071045359/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_339 (thetaFirstMode_refined_node_1015).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_340 :
    (37759990620877321/1000000000000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(341/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-22951955363285474286510489193/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (85/128:ℝ) (341/512:ℝ)-(85/128:ℝ)*thetaPowerMass 0 (85/128:ℝ) (341/512:ℝ)) ≤
      thetaFirstModeFirst (85/128:ℝ)*(thetaPowerMass 1 (85/128:ℝ) (341/512:ℝ)-(85/128:ℝ)*thetaPowerMass 0 (85/128:ℝ) (341/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0514.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (85/128:ℝ) (341/512:ℝ)
    (85/128:ℝ) (1977544207/100000000000000:ℝ) (-22951955363285474286510489193/50000000000000000000000000000000:ℝ) (1170506923053822489801/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_340
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1020).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_340 :
    (∫ x in (85/128:ℝ)..(341/512:ℝ), x^0*thetaFirstMode x) ≤ (37760573949142229/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (85/128:ℝ) (341/512:ℝ)
    (1977551671/100000000000000:ℝ) (472431613/25000000000000:ℝ) (1170506923053822489801/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_340 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1021).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_341 :
    (18039891986753653/500000000000000000000000:ℝ) ≤ ∫ x in (341/512:ℝ)..(171/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2751646894917022496316655149/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (341/512:ℝ) (171/256:ℝ)-(10959904662371742259809/16455549877310448463360:ℝ)*thetaPowerMass 0 (341/512:ℝ) (171/256:ℝ)) ≤
      thetaFirstModeFirst (10959904662371742259809/16455549877310448463360:ℝ)*(thetaPowerMass 1 (341/512:ℝ) (171/256:ℝ)-(10959904662371742259809/16455549877310448463360:ℝ)*thetaPowerMass 0 (341/512:ℝ) (171/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0516.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (341/512:ℝ) (171/256:ℝ)
    (10959904662371742259809/16455549877310448463360:ℝ) (1889046769/100000000000000:ℝ) (-2751646894917022496316655149/6250000000000000000000000000000:ℝ) (902176198681593383143/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_341
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1025).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_341 :
    (∫ x in (341/512:ℝ)..(171/256:ℝ), x^0*thetaFirstMode x) ≤ (36080337595901331/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (341/512:ℝ) (171/256:ℝ)
    (472431613/25000000000000:ℝ) (902736853/50000000000000:ℝ) (902176198681593383143/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_341 (thetaFirstMode_refined_node_1021).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_342 :
    (34468049776771631/1000000000000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(343/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5280666568894931310560870199/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (171/256:ℝ) (343/512:ℝ)-(171/256:ℝ)*thetaPowerMass 0 (171/256:ℝ) (343/512:ℝ)) ≤
      thetaFirstModeFirst (171/256:ℝ)*(thetaPowerMass 1 (171/256:ℝ) (343/512:ℝ)-(171/256:ℝ)*thetaPowerMass 0 (171/256:ℝ) (343/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0517.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (171/256:ℝ) (343/512:ℝ)
    (171/256:ℝ) (1805466837/100000000000000:ℝ) (-5280666568894931310560870199/12500000000000000000000000000000:ℝ) (4345187324651066737441/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_342
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1026).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_342 :
    (∫ x in (171/256:ℝ)..(343/512:ℝ), x^0*thetaFirstMode x) ≤ (34468594090427743/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (171/256:ℝ) (343/512:ℝ)
    (902736853/50000000000000:ℝ) (26947857/1562500000000:ℝ) (4345187324651066737441/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_342 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1027).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_343 :
    (32922317359634501/1000000000000000000000000:ℝ) ≤ ∫ x in (343/512:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-10125651529677904809646813429/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (343/512:ℝ) (43/64:ℝ)-(11552179400427359855007/17243678709113286300160:ℝ)*thetaPowerMass 0 (343/512:ℝ) (43/64:ℝ)) ≤
      thetaFirstModeFirst (11552179400427359855007/17243678709113286300160:ℝ)*(thetaPowerMass 1 (343/512:ℝ) (43/64:ℝ)-(11552179400427359855007/17243678709113286300160:ℝ)*thetaPowerMass 0 (343/512:ℝ) (43/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0519.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (343/512:ℝ) (43/64:ℝ)
    (11552179400427359855007/17243678709113286300160:ℝ) (1724041173/100000000000000:ℝ) (-10125651529677904809646813429/25000000000000000000000000000000:ℝ) (4184803553622849574231/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_343
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1031).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_343 :
    (∫ x in (343/512:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x) ≤ (16461416888236787/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (343/512:ℝ) (43/64:ℝ)
    (26947857/1562500000000:ℝ) (51473983/3125000000000:ℝ) (4184803553622849574231/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_343 (thetaFirstMode_refined_node_1027).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_344 :
    (31440119628168699/1000000000000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(345/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-607030460935915500212139521/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (43/64:ℝ) (345/512:ℝ)-(43/64:ℝ)*thetaPowerMass 0 (43/64:ℝ) (345/512:ℝ)) ≤
      thetaFirstModeFirst (43/64:ℝ)*(thetaPowerMass 1 (43/64:ℝ) (345/512:ℝ)-(43/64:ℝ)*thetaPowerMass 0 (43/64:ℝ) (345/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0520.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (43/64:ℝ) (345/512:ℝ)
    (43/64:ℝ) (82358057/5000000000000:ℝ) (-607030460935915500212139521/1562500000000000000000000000000:ℝ) (8059178514888556234447/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_344
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1032).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_344 :
    (∫ x in (43/64:ℝ)..(345/512:ℝ), x^0*thetaFirstMode x) ≤ (31440627179973319/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/64:ℝ) (345/512:ℝ)
    (51473983/3125000000000:ℝ) (393216289/25000000000000:ℝ) (8059178514888556234447/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_344 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1033).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_345 :
    (30019141505011719/1000000000000000000000000:ℝ) ≤ ∫ x in (345/512:ℝ)..(173/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9308392710025231478938235433/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (345/512:ℝ) (173/256:ℝ)-(2434547114057885834205/3612928108949549783552:ℝ)*thetaPowerMass 0 (345/512:ℝ) (173/256:ℝ)) ≤
      thetaFirstModeFirst (2434547114057885834205/3612928108949549783552:ℝ)*(thetaPowerMass 1 (345/512:ℝ) (173/256:ℝ)-(2434547114057885834205/3612928108949549783552:ℝ)*thetaPowerMass 0 (345/512:ℝ) (173/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0522.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (345/512:ℝ) (173/256:ℝ)
    (2434547114057885834205/3612928108949549783552:ℝ) (314459387/20000000000000:ℝ) (-9308392710025231478938235433/25000000000000000000000000000000:ℝ) (12123145869520086023/1562500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_345
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1037).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_345 :
    (∫ x in (345/512:ℝ)..(173/256:ℝ), x^0*thetaFirstMode x) ≤ (15009811444979207/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (345/512:ℝ) (173/256:ℝ)
    (393216289/25000000000000:ℝ) (18770469/1250000000000:ℝ) (12123145869520086023/1562500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_345 (thetaFirstMode_refined_node_1033).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_346 :
    (1791067037937223/62500000000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(347/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-111566139282853864069123869/312500000000000000000000000000:ℝ)*(thetaPowerMass 1 (173/256:ℝ) (347/512:ℝ)-(173/256:ℝ)*thetaPowerMass 0 (173/256:ℝ) (347/512:ℝ)) ≤
      thetaFirstModeFirst (173/256:ℝ)*(thetaPowerMass 1 (173/256:ℝ) (347/512:ℝ)-(173/256:ℝ)*thetaPowerMass 0 (173/256:ℝ) (347/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0523.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (173/256:ℝ) (347/512:ℝ)
    (173/256:ℝ) (750815859/50000000000000:ℝ) (-111566139282853864069123869/312500000000000000000000000000:ℝ) (466765090716006631209/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_346
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1038).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_346 :
    (∫ x in (173/256:ℝ)..(347/512:ℝ), x^0*thetaFirstMode x) ≤ (14328772763652027/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (173/256:ℝ) (347/512:ℝ)
    (18770469/1250000000000:ℝ) (35834249/2500000000000:ℝ) (466765090716006631209/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_346 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1039).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_347 :
    (27351745277893817/1000000000000000000000000:ℝ) ≤ ∫ x in (347/512:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17101545515717541399376803969/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (347/512:ℝ) (87/128:ℝ)-(12822747845328599226543/18919600885932177948160:ℝ)*thetaPowerMass 0 (347/512:ℝ) (87/128:ℝ)) ≤
      thetaFirstModeFirst (12822747845328599226543/18919600885932177948160:ℝ)*(thetaPowerMass 1 (347/512:ℝ) (87/128:ℝ)-(12822747845328599226543/18919600885932177948160:ℝ)*thetaPowerMass 0 (347/512:ℝ) (87/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0525.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (347/512:ℝ) (87/128:ℝ)
    (12822747845328599226543/18919600885932177948160:ℝ) (286570193/20000000000000:ℝ) (-17101545515717541399376803969/50000000000000000000000000000000:ℝ) (3593598945580688865067/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_347
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1043).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_347 :
    (∫ x in (347/512:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x) ≤ (13676096837227953/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (347/512:ℝ) (87/128:ℝ)
    (35834249/2500000000000:ℝ) (683975811/50000000000000:ℝ) (3593598945580688865067/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_347 (thetaFirstMode_refined_node_1039).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_348 :
    (26100997500095631/1000000000000000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(349/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-8195812544053763035534074477/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (87/128:ℝ) (349/512:ℝ)-(87/128:ℝ)*thetaPowerMass 0 (87/128:ℝ) (349/512:ℝ)) ≤
      thetaFirstModeFirst (87/128:ℝ)*(thetaPowerMass 1 (87/128:ℝ) (349/512:ℝ)-(87/128:ℝ)*thetaPowerMass 0 (87/128:ℝ) (349/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0526.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (87/128:ℝ) (349/512:ℝ)
    (87/128:ℝ) (683973147/50000000000000:ℝ) (-8195812544053763035534074477/25000000000000000000000000000000:ℝ) (1383084605119152080019/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_348
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1044).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_348 :
    (∫ x in (87/128:ℝ)..(349/512:ℝ), x^0*thetaFirstMode x) ≤ (2610143787348529/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (87/128:ℝ) (349/512:ℝ)
    (683975811/50000000000000:ℝ) (1305275287/100000000000000:ℝ) (1383084605119152080019/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_348 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1045).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_349 :
    (1245140065578959/50000000000000000000000:ℝ) ≤ ∫ x in (349/512:ℝ)..(175/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3924483208224762998804737941/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (349/512:ℝ) (175/256:ℝ)-(13503432473757098003241/19809759509951338370560:ℝ)*thetaPowerMass 0 (349/512:ℝ) (175/256:ℝ)) ≤
      thetaFirstModeFirst (13503432473757098003241/19809759509951338370560:ℝ)*(thetaPowerMass 1 (349/512:ℝ) (175/256:ℝ)-(13503432473757098003241/19809759509951338370560:ℝ)*thetaPowerMass 0 (349/512:ℝ) (175/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0528.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (349/512:ℝ) (175/256:ℝ)
    (13503432473757098003241/19809759509951338370560:ℝ) (1304801589/100000000000000:ℝ) (-3924483208224762998804737941/12500000000000000000000000000000:ℝ) (415791399088820588141/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_349
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1049).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_349 :
    (∫ x in (349/512:ℝ)..(175/256:ℝ), x^0*thetaFirstMode x) ≤ (24903218712075067/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (349/512:ℝ) (175/256:ℝ)
    (1305275287/100000000000000:ℝ) (622618637/50000000000000:ℝ) (415791399088820588141/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_349 (thetaFirstMode_refined_node_1045).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_350 :
    (5938783780903849/250000000000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(351/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3760164344589066833865008699/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (175/256:ℝ) (351/512:ℝ)-(175/256:ℝ)*thetaPowerMass 0 (175/256:ℝ) (351/512:ℝ)) ≤
      thetaFirstModeFirst (175/256:ℝ)*(thetaPowerMass 1 (175/256:ℝ) (351/512:ℝ)-(175/256:ℝ)*thetaPowerMass 0 (175/256:ℝ) (351/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0529.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (175/256:ℝ) (351/512:ℝ)
    (175/256:ℝ) (622616193/50000000000000:ℝ) (-3760164344589066833865008699/12500000000000000000000000000000:ℝ) (3199333338005062984983/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_350
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1050).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_350 :
    (∫ x in (175/256:ℝ)..(351/512:ℝ), x^0*thetaFirstMode x) ≤ (23755544889929587/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (175/256:ℝ) (351/512:ℝ)
    (622618637/50000000000000:ℝ) (1187737339/100000000000000:ℝ) (3199333338005062984983/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_350 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1051).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_351 :
    (22656103075495751/1000000000000000000000000:ℝ) ≤ ∫ x in (351/512:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7199353298200506036368577071/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (351/512:ℝ) (11/16:ℝ)-(14216048497680767340759/20736351271356306434560:ℝ)*thetaPowerMass 0 (351/512:ℝ) (11/16:ℝ)) ≤
      thetaFirstModeFirst (14216048497680767340759/20736351271356306434560:ℝ)*(thetaPowerMass 1 (351/512:ℝ) (11/16:ℝ)-(14216048497680767340759/20736351271356306434560:ℝ)*thetaPowerMass 0 (351/512:ℝ) (11/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0531.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (351/512:ℝ) (11/16:ℝ)
    (14216048497680767340759/20736351271356306434560:ℝ) (74206581/6250000000000:ℝ) (-7199353298200506036368577071/25000000000000000000000000000000:ℝ) (1538297928038724187807/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_351
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1055).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_351 :
    (∫ x in (351/512:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x) ≤ (22656491324283981/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (351/512:ℝ) (11/16:ℝ)
    (1187737339/100000000000000:ℝ) (566339291/50000000000000:ℝ) (1538297928038724187807/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_351 (thetaFirstMode_refined_node_1051).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator

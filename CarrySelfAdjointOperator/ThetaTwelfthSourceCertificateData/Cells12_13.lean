import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature13
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative19
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative20
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative21

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_12_416 :
    (28125694610399/500000000000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(417/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-262182886591060890091/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (13/16:ℝ) (417/512:ℝ)-(417/512:ℝ)*thetaPowerMass 12 (13/16:ℝ) (417/512:ℝ)) ≤
      thetaFirstModeFirst (417/512:ℝ)*(thetaPowerMass 13 (13/16:ℝ) (417/512:ℝ)-(417/512:ℝ)*thetaPowerMass 12 (13/16:ℝ) (417/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0629.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (13/16:ℝ) (417/512:ℝ)
    (417/512:ℝ) (16628833/50000000000000:ℝ) (-262182886591060890091/25000000000000000000000000:ℝ) (154697424799214552691/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_416
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1249).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_416 :
    (∫ x in (13/16:ℝ)..(417/512:ℝ), x^12*thetaFirstMode x) ≤ (5625254606813/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (13/16:ℝ) (417/512:ℝ)
    (35366227/100000000000000:ℝ) (33257837/100000000000000:ℝ) (154697424799214552691/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_416 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1249).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_417 :
    (10886962102983/200000000000000000000000:ℝ) ≤ ∫ x in (417/512:ℝ)..(209/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-262087729107131110010299747/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (417/512:ℝ) (209/256:ℝ)-(67023486088292228081193/82291363666684906908160:ℝ)*thetaPowerMass 12 (417/512:ℝ) (209/256:ℝ)) ≤
      thetaFirstModeFirst (67023486088292228081193/82291363666684906908160:ℝ)*(thetaPowerMass 13 (417/512:ℝ) (209/256:ℝ)-(67023486088292228081193/82291363666684906908160:ℝ)*thetaPowerMass 12 (417/512:ℝ) (209/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0630.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (417/512:ℝ) (209/256:ℝ)
    (67023486088292228081193/82291363666684906908160:ℝ) (33244571/100000000000000:ℝ) (-262087729107131110010299747/25000000000000000000000000000000:ℝ) (36659716912842526041/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_417
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1253).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_417 :
    (∫ x in (417/512:ℝ)..(209/256:ℝ), x^12*thetaFirstMode x) ≤ (3402299541197/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (417/512:ℝ) (209/256:ℝ)
    (33257837/100000000000000:ℝ) (15633749/50000000000000:ℝ) (36659716912842526041/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_417 (thetaFirstMode_refined_node_1249).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_418 :
    (52662020747099/1000000000000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(419/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-467059859576881899207/50000000000000000000000000:ℝ)*(thetaPowerMass 13 (209/256:ℝ) (419/512:ℝ)-(419/512:ℝ)*thetaPowerMass 12 (209/256:ℝ) (419/512:ℝ)) ≤
      thetaFirstModeFirst (419/512:ℝ)*(thetaPowerMass 13 (209/256:ℝ) (419/512:ℝ)-(419/512:ℝ)*thetaPowerMass 12 (209/256:ℝ) (419/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0632.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (209/256:ℝ) (419/512:ℝ)
    (419/512:ℝ) (29388909/100000000000000:ℝ) (-467059859576881899207/50000000000000000000000000:ℝ) (277931522703706091913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_418
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1255).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_418 :
    (∫ x in (209/256:ℝ)..(419/512:ℝ), x^12*thetaFirstMode x) ≤ (10532625215309/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (209/256:ℝ) (419/512:ℝ)
    (15633749/50000000000000:ℝ) (29389061/100000000000000:ℝ) (277931522703706091913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_418 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1255).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_419 :
    (50929338470129/1000000000000000000000000:ℝ) ≤ ∫ x in (419/512:ℝ)..(105/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-58361215101033611177754681/6250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (419/512:ℝ) (105/128:ℝ)-(69972668969052009938391/85502296803586871580160:ℝ)*thetaPowerMass 12 (419/512:ℝ) (105/128:ℝ)) ≤
      thetaFirstModeFirst (69972668969052009938391/85502296803586871580160:ℝ)*(thetaPowerMass 13 (419/512:ℝ) (105/128:ℝ)-(69972668969052009938391/85502296803586871580160:ℝ)*thetaPowerMass 12 (419/512:ℝ) (105/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0633.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (419/512:ℝ) (105/128:ℝ)
    (69972668969052009938391/85502296803586871580160:ℝ) (293773/1000000000000:ℝ) (-58361215101033611177754681/6250000000000000000000000000000:ℝ) (16457687982596865951/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_419
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1259).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_419 :
    (∫ x in (419/512:ℝ)..(105/128:ℝ), x^12*thetaFirstMode x) ≤ (20372494839/400000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (419/512:ℝ) (105/128:ℝ)
    (29389061/100000000000000:ℝ) (2761667/10000000000000:ℝ) (16457687982596865951/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_419 (thetaFirstMode_refined_node_1255).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_420 :
    (49239735863831/1000000000000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(421/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-103901649138329984669/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (105/128:ℝ) (421/512:ℝ)-(421/512:ℝ)*thetaPowerMass 12 (105/128:ℝ) (421/512:ℝ)) ≤
      thetaFirstModeFirst (421/512:ℝ)*(thetaPowerMass 13 (105/128:ℝ) (421/512:ℝ)-(421/512:ℝ)*thetaPowerMass 12 (105/128:ℝ) (421/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0635.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (105/128:ℝ) (421/512:ℝ)
    (421/512:ℝ) (25944617/100000000000000:ℝ) (-103901649138329984669/12500000000000000000000000:ℝ) (249420229777245076453/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_420
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1261).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_420 :
    (∫ x in (105/128:ℝ)..(421/512:ℝ), x^12*thetaFirstMode x) ≤ (49240791181103/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (105/128:ℝ) (421/512:ℝ)
    (2761667/10000000000000:ℝ) (1621547/6250000000000:ℝ) (249420229777245076453/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_420 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1261).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_421 :
    (47589614351217/1000000000000000000000000:ℝ) ≤ ∫ x in (421/512:ℝ)..(211/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-207727320810335136609106977/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (421/512:ℝ) (211/256:ℝ)-(73036644780581807459409/88822326679864764136960:ℝ)*thetaPowerMass 12 (421/512:ℝ) (211/256:ℝ)) ≤
      thetaFirstModeFirst (73036644780581807459409/88822326679864764136960:ℝ)*(thetaPowerMass 13 (421/512:ℝ) (211/256:ℝ)-(73036644780581807459409/88822326679864764136960:ℝ)*thetaPowerMass 12 (421/512:ℝ) (211/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0636.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (421/512:ℝ) (211/256:ℝ)
    (73036644780581807459409/88822326679864764136960:ℝ) (50653/195312500000:ℝ) (-207727320810335136609106977/25000000000000000000000000000000:ℝ) (236192444692696261033/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_421
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1265).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_421 :
    (∫ x in (421/512:ℝ)..(211/256:ℝ), x^12*thetaFirstMode x) ≤ (11897857377723/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (421/512:ℝ) (211/256:ℝ)
    (1621547/6250000000000:ℝ) (12184001/50000000000000:ℝ) (236192444692696261033/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_421 (thetaFirstMode_refined_node_1261).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_422 :
    (45981762012337/1000000000000000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(423/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-73890845283712051279/10000000000000000000000000:ℝ)*(thetaPowerMass 13 (211/256:ℝ) (423/512:ℝ)-(423/512:ℝ)*thetaPowerMass 12 (211/256:ℝ) (423/512:ℝ)) ≤
      thetaFirstModeFirst (423/512:ℝ)*(thetaPowerMass 13 (211/256:ℝ) (423/512:ℝ)-(423/512:ℝ)*thetaPowerMass 12 (211/256:ℝ) (423/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0638.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (211/256:ℝ) (423/512:ℝ)
    (423/512:ℝ) (22881253/100000000000000:ℝ) (-73890845283712051279/10000000000000000000000000:ℝ) (223610065160718119631/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_422
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1267).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_422 :
    (∫ x in (211/256:ℝ)..(423/512:ℝ), x^12*thetaFirstMode x) ≤ (11495692532179/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (211/256:ℝ) (423/512:ℝ)
    (12184001/50000000000000:ℝ) (11440687/50000000000000:ℝ) (223610065160718119631/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_422 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1267).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_423 :
    (88825344777/2000000000000000000000:ℝ) ≤ ∫ x in (423/512:ℝ)..(53/64:ℝ), x^12*thetaFirstMode x := by
  have hd : (-46164833162719103188474261/6250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (423/512:ℝ) (53/64:ℝ)-(76219304315222090354607/92254615216783819932160:ℝ)*thetaPowerMass 12 (423/512:ℝ) (53/64:ℝ)) ≤
      thetaFirstModeFirst (76219304315222090354607/92254615216783819932160:ℝ)*(thetaPowerMass 13 (423/512:ℝ) (53/64:ℝ)-(76219304315222090354607/92254615216783819932160:ℝ)*thetaPowerMass 12 (423/512:ℝ) (53/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0639.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (423/512:ℝ) (53/64:ℝ)
    (76219304315222090354607/92254615216783819932160:ℝ) (22872157/100000000000000:ℝ) (-46164833162719103188474261/6250000000000000000000000000000:ℝ) (264555831899039919/1250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_423
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1271).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_423 :
    (∫ x in (423/512:ℝ)..(53/64:ℝ), x^12*thetaFirstMode x) ≤ (173493781603/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (423/512:ℝ) (53/64:ℝ)
    (11440687/50000000000000:ℝ) (10740033/50000000000000:ℝ) (264555831899039919/1250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_423 (thetaFirstMode_refined_node_1267).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_424 :
    (42884956509827/1000000000000000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(425/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-82024544432356675749/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (53/64:ℝ) (425/512:ℝ)-(425/512:ℝ)*thetaPowerMass 12 (53/64:ℝ) (425/512:ℝ)) ≤
      thetaFirstModeFirst (425/512:ℝ)*(thetaPowerMass 13 (53/64:ℝ) (425/512:ℝ)-(425/512:ℝ)*thetaPowerMass 12 (53/64:ℝ) (425/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0641.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (53/64:ℝ) (425/512:ℝ)
    (425/512:ℝ) (10079703/50000000000000:ℝ) (-82024544432356675749/12500000000000000000000000:ℝ) (40053779141744391673/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_424
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1273).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_424 :
    (∫ x in (53/64:ℝ)..(425/512:ℝ), x^12*thetaFirstMode x) ≤ (42885916672983/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (53/64:ℝ) (425/512:ℝ)
    (10740033/50000000000000:ℝ) (20159513/100000000000000:ℝ) (40053779141744391673/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_424 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1273).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_425 :
    (10348798923241/250000000000000000000000:ℝ) ≤ ∫ x in (425/512:ℝ)..(213/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-327977334446131963136579723/50000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (425/512:ℝ) (213/256:ℝ)-(15904930171669675505325/19160480067509209098752:ℝ)*thetaPowerMass 12 (425/512:ℝ) (213/256:ℝ)) ≤
      thetaFirstModeFirst (15904930171669675505325/19160480067509209098752:ℝ)*(thetaPowerMass 13 (425/512:ℝ) (213/256:ℝ)-(15904930171669675505325/19160480067509209098752:ℝ)*thetaPowerMass 12 (425/512:ℝ) (213/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0642.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (425/512:ℝ) (213/256:ℝ)
    (15904930171669675505325/19160480067509209098752:ℝ) (10075683/50000000000000:ℝ) (-327977334446131963136579723/50000000000000000000000000000000:ℝ) (189456469475912015979/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_425
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1277).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_425 :
    (∫ x in (425/512:ℝ)..(213/256:ℝ), x^12*thetaFirstMode x) ≤ (41396850805281/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (425/512:ℝ) (213/256:ℝ)
    (20159513/100000000000000:ℝ) (151323/800000000000:ℝ) (189456469475912015979/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_425 (thetaFirstMode_refined_node_1273).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_426 :
    (19972915788599/500000000000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(427/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-145538713209367669413/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (213/256:ℝ) (427/512:ℝ)-(427/512:ℝ)*thetaPowerMass 12 (213/256:ℝ) (427/512:ℝ)) ≤
      thetaFirstModeFirst (427/512:ℝ)*(thetaPowerMass 13 (213/256:ℝ) (427/512:ℝ)-(427/512:ℝ)*thetaPowerMass 12 (213/256:ℝ) (427/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0644.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (213/256:ℝ) (427/512:ℝ)
    (427/512:ℝ) (17743431/100000000000000:ℝ) (-145538713209367669413/25000000000000000000000000:ℝ) (179182140372564781941/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_426
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1279).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_426 :
    (∫ x in (213/256:ℝ)..(427/512:ℝ), x^12*thetaFirstMode x) ≤ (39946745665109/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (213/256:ℝ) (427/512:ℝ)
    (151323/800000000000:ℝ) (8871763/50000000000000:ℝ) (179182140372564781941/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_426 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1279).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_427 :
    (3853354304633/100000000000000000000000:ℝ) ≤ ∫ x in (427/512:ℝ)..(107/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-58193965464152993522552829/10000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (427/512:ℝ) (107/128:ℝ)-(82956802885821125866143/99468997421790285852160:ℝ)*thetaPowerMass 12 (427/512:ℝ) (107/128:ℝ)) ≤
      thetaFirstModeFirst (82956802885821125866143/99468997421790285852160:ℝ)*(thetaPowerMass 13 (427/512:ℝ) (107/128:ℝ)-(82956802885821125866143/99468997421790285852160:ℝ)*thetaPowerMass 12 (427/512:ℝ) (107/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0645.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (427/512:ℝ) (107/128:ℝ)
    (82956802885821125866143/99468997421790285852160:ℝ) (4434083/25000000000000:ℝ) (-58193965464152993522552829/10000000000000000000000000000000:ℝ) (42355413677653710627/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_427
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1283).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_427 :
    (∫ x in (427/512:ℝ)..(107/128:ℝ), x^12*thetaFirstMode x) ≤ (9633779885569/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (427/512:ℝ) (107/128:ℝ)
    (8871763/50000000000000:ℝ) (16640047/100000000000000:ℝ) (42355413677653710627/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_427 (thetaFirstMode_refined_node_1279).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_428 :
    (37160603764689/1000000000000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(429/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-32246409507344621121/6250000000000000000000000:ℝ)*(thetaPowerMass 13 (107/128:ℝ) (429/512:ℝ)-(429/512:ℝ)*thetaPowerMass 12 (107/128:ℝ) (429/512:ℝ)) ≤
      thetaFirstModeFirst (429/512:ℝ)*(thetaPowerMass 13 (107/128:ℝ) (429/512:ℝ)-(429/512:ℝ)*thetaPowerMass 12 (107/128:ℝ) (429/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0647.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (107/128:ℝ) (429/512:ℝ)
    (429/512:ℝ) (1950141/12500000000000:ℝ) (-32246409507344621121/6250000000000000000000000:ℝ) (80075860635909528499/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_428
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1285).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_428 :
    (∫ x in (107/128:ℝ)..(429/512:ℝ), x^12*thetaFirstMode x) ≤ (3716147374891/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (107/128:ℝ) (429/512:ℝ)
    (16640047/100000000000000:ℝ) (15601213/100000000000000:ℝ) (80075860635909528499/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_428 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1285).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_429 :
    (35823791777579/1000000000000000000000000:ℝ) ≤ ∫ x in (429/512:ℝ)..(215/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-10315022379513419488123/2000000000000000000000000000:ℝ)*(thetaPowerMass 13 (429/512:ℝ) (215/256:ℝ)-(86519996812935046058841/103257800780870084584960:ℝ)*thetaPowerMass 12 (429/512:ℝ) (215/256:ℝ)) ≤
      thetaFirstModeFirst (86519996812935046058841/103257800780870084584960:ℝ)*(thetaPowerMass 13 (429/512:ℝ) (215/256:ℝ)-(86519996812935046058841/103257800780870084584960:ℝ)*thetaPowerMass 12 (429/512:ℝ) (215/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0648.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (429/512:ℝ) (215/256:ℝ)
    (86519996812935046058841/103257800780870084584960:ℝ) (7797433/50000000000000:ℝ) (-10315022379513419488123/2000000000000000000000000000:ℝ) (75674989066615317153/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_429
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1289).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_429 :
    (∫ x in (429/512:ℝ)..(215/256:ℝ), x^12*thetaFirstMode x) ≤ (17912646337807/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (429/512:ℝ) (215/256:ℝ)
    (15601213/100000000000000:ℝ) (14623487/100000000000000:ℝ) (75674989066615317153/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_429 (thetaFirstMode_refined_node_1285).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_430 :
    (17262611143809/500000000000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(431/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-57099046627044903519/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (215/256:ℝ) (431/512:ℝ)-(431/512:ℝ)*thetaPowerMass 12 (215/256:ℝ) (431/512:ℝ)) ≤
      thetaFirstModeFirst (431/512:ℝ)*(thetaPowerMass 13 (215/256:ℝ) (431/512:ℝ)-(431/512:ℝ)*thetaPowerMass 12 (215/256:ℝ) (431/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0650.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (215/256:ℝ) (431/512:ℝ)
    (431/512:ℝ) (3425859/25000000000000:ℝ) (-57099046627044903519/12500000000000000000000000:ℝ) (142994966948344169319/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_430
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1291).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_430 :
    (∫ x in (215/256:ℝ)..(431/512:ℝ), x^12*thetaFirstMode x) ≤ (34526047602009/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (215/256:ℝ) (431/512:ℝ)
    (14623487/100000000000000:ℝ) (13703511/100000000000000:ℝ) (142994966948344169319/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_430 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1291).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_431 :
    (33261769147457/1000000000000000000000000:ℝ) ≤ ∫ x in (431/512:ℝ)..(27/32:ℝ), x^12*thetaFirstMode x := by
  have hd : (-28538890652579743145831737/6250000000000000000000000000000:ℝ)*(thetaPowerMass 13 (431/512:ℝ) (27/32:ℝ)-(90218589795601773832359/107172285154106278812160:ℝ)*thetaPowerMass 12 (431/512:ℝ) (27/32:ℝ)) ≤
      thetaFirstModeFirst (90218589795601773832359/107172285154106278812160:ℝ)*(thetaPowerMass 13 (431/512:ℝ) (27/32:ℝ)-(90218589795601773832359/107172285154106278812160:ℝ)*thetaPowerMass 12 (431/512:ℝ) (27/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0651.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (431/512:ℝ) (27/32:ℝ)
    (90218589795601773832359/107172285154106278812160:ℝ) (13697917/100000000000000:ℝ) (-28538890652579743145831737/6250000000000000000000000000000:ℝ) (67533041812260745961/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_431
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1295).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_431 :
    (∫ x in (431/512:ℝ)..(27/32:ℝ), x^12*thetaFirstMode x) ≤ (332631963557/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (431/512:ℝ) (27/32:ℝ)
    (13703511/100000000000000:ℝ) (12838097/100000000000000:ℝ) (67533041812260745961/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_431 (thetaFirstMode_refined_node_1291).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_432 :
    (6407080607659/200000000000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(433/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-101001430243798734633/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (27/32:ℝ) (433/512:ℝ)-(433/512:ℝ)*thetaPowerMass 12 (27/32:ℝ) (433/512:ℝ)) ≤
      thetaFirstModeFirst (433/512:ℝ)*(thetaPowerMass 13 (27/32:ℝ) (433/512:ℝ)-(433/512:ℝ)*thetaPowerMass 12 (27/32:ℝ) (433/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0653.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (27/32:ℝ) (433/512:ℝ)
    (433/512:ℝ) (6012077/50000000000000:ℝ) (-101001430243798734633/25000000000000000000000000:ℝ) (12754359956592189627/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_432
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1297).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_432 :
    (∫ x in (27/32:ℝ)..(433/512:ℝ), x^12*thetaFirstMode x) ≤ (16018092207037/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (27/32:ℝ) (433/512:ℝ)
    (12838097/100000000000000:ℝ) (601211/5000000000000:ℝ) (12754359956592189627/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_432 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1297).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_433 :
    (15421545621121/500000000000000000000000:ℝ) ≤ ∫ x in (433/512:ℝ)..(217/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-100963667168440885867516937/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (433/512:ℝ) (217/256:ℝ)-(94057062584506765152057/111216007226212200348160:ℝ)*thetaPowerMass 12 (433/512:ℝ) (217/256:ℝ)) ≤
      thetaFirstModeFirst (94057062584506765152057/111216007226212200348160:ℝ)*(thetaPowerMass 13 (433/512:ℝ) (217/256:ℝ)-(94057062584506765152057/111216007226212200348160:ℝ)*thetaPowerMass 12 (433/512:ℝ) (217/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0654.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (433/512:ℝ) (217/256:ℝ)
    (94057062584506765152057/111216007226212200348160:ℝ) (2403859/20000000000000:ℝ) (-100963667168440885867516937/25000000000000000000000000000000:ℝ) (30102135937187152831/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_433
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1301).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_433 :
    (∫ x in (433/512:ℝ)..(217/256:ℝ), x^12*thetaFirstMode x) ≤ (481944455027/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (433/512:ℝ) (217/256:ℝ)
    (601211/5000000000000:ℝ) (11259009/100000000000000:ℝ) (30102135937187152831/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_433 (thetaFirstMode_refined_node_1297).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_434 :
    (29686661525127/1000000000000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(435/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-44618380725938895207/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (217/256:ℝ) (435/512:ℝ)-(435/512:ℝ)*thetaPowerMass 12 (217/256:ℝ) (435/512:ℝ)) ≤
      thetaFirstModeFirst (435/512:ℝ)*(thetaPowerMass 13 (217/256:ℝ) (435/512:ℝ)-(435/512:ℝ)*thetaPowerMass 12 (217/256:ℝ) (435/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0656.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (217/256:ℝ) (435/512:ℝ)
    (435/512:ℝ) (2634921/25000000000000:ℝ) (-44618380725938895207/12500000000000000000000000:ℝ) (28410692966885968931/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_434
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1303).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_434 :
    (∫ x in (217/256:ℝ)..(435/512:ℝ), x^12*thetaFirstMode x) ≤ (14843701505199/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (217/256:ℝ) (435/512:ℝ)
    (11259009/100000000000000:ℝ) (10539743/100000000000000:ℝ) (28410692966885968931/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_434 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1303).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_435 :
    (28563190704313/1000000000000000000000000:ℝ) ≤ ∫ x in (435/512:ℝ)..(109/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-17840655793648345212111183/5000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (435/512:ℝ) (109/128:ℝ)-(19608004486597651322715/23078521433218056637952:ℝ)*thetaPowerMass 12 (435/512:ℝ) (109/128:ℝ)) ≤
      thetaFirstModeFirst (19608004486597651322715/23078521433218056637952:ℝ)*(thetaPowerMass 13 (435/512:ℝ) (109/128:ℝ)-(19608004486597651322715/23078521433218056637952:ℝ)*thetaPowerMass 12 (435/512:ℝ) (109/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0657.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (435/512:ℝ) (109/128:ℝ)
    (19608004486597651322715/23078521433218056637952:ℝ) (2633853/25000000000000:ℝ) (-17840655793648345212111183/5000000000000000000000000000000:ℝ) (107228885635937195173/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_435
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1307).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_435 :
    (∫ x in (435/512:ℝ)..(109/128:ℝ), x^12*thetaFirstMode x) ≤ (3570559046629/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (435/512:ℝ) (109/128:ℝ)
    (10539743/100000000000000:ℝ) (9863839/100000000000000:ℝ) (107228885635937195173/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_435 (thetaFirstMode_refined_node_1303).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_436 :
    (27474357867017/1000000000000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(437/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-39379864891416292301/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (109/128:ℝ) (437/512:ℝ)-(437/512:ℝ)*thetaPowerMass 12 (109/128:ℝ) (437/512:ℝ)) ≤
      thetaFirstModeFirst (437/512:ℝ)*(thetaPowerMass 13 (109/128:ℝ) (437/512:ℝ)-(437/512:ℝ)*thetaPowerMass 12 (109/128:ℝ) (437/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0659.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (109/128:ℝ) (437/512:ℝ)
    (437/512:ℝ) (9228799/100000000000000:ℝ) (-39379864891416292301/12500000000000000000000000:ℝ) (101150201789825405357/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_436
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1309).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_436 :
    (∫ x in (109/128:ℝ)..(437/512:ℝ), x^12*thetaFirstMode x) ≤ (27475058989141/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (109/128:ℝ) (437/512:ℝ)
    (9863839/100000000000000:ℝ) (9228851/100000000000000:ℝ) (101150201789825405357/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_436 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1309).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_437 :
    (26417349342357/1000000000000000000000000:ℝ) ≤ ∫ x in (437/512:ℝ)..(219/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-78730065960210806203937833/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (437/512:ℝ) (219/256:ℝ)-(102172206059393137678593/119705810187199806492160:ℝ)*thetaPowerMass 12 (437/512:ℝ) (219/256:ℝ)) ≤
      thetaFirstModeFirst (102172206059393137678593/119705810187199806492160:ℝ)*(thetaPowerMass 13 (437/512:ℝ) (219/256:ℝ)-(102172206059393137678593/119705810187199806492160:ℝ)*thetaPowerMass 12 (437/512:ℝ) (219/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0660.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (437/512:ℝ) (219/256:ℝ)
    (102172206059393137678593/119705810187199806492160:ℝ) (4612523/50000000000000:ℝ) (-78730065960210806203937833/25000000000000000000000000000000:ℝ) (95390762738773861167/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_437
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1313).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_437 :
    (∫ x in (437/512:ℝ)..(219/256:ℝ), x^12*thetaFirstMode x) ≤ (26418562461809/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (437/512:ℝ) (219/256:ℝ)
    (9228851/100000000000000:ℝ) (8632459/100000000000000:ℝ) (95390762738773861167/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_437 (thetaFirstMode_refined_node_1309).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_438 :
    (25393713015717/1000000000000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(439/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-216997748208405979/78125000000000000000000:ℝ)*(thetaPowerMass 13 (219/256:ℝ) (439/512:ℝ)-(439/512:ℝ)*thetaPowerMass 12 (219/256:ℝ) (439/512:ℝ)) ≤
      thetaFirstModeFirst (439/512:ℝ)*(thetaPowerMass 13 (219/256:ℝ) (439/512:ℝ)-(439/512:ℝ)*thetaPowerMass 12 (219/256:ℝ) (439/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0662.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (219/256:ℝ) (439/512:ℝ)
    (439/512:ℝ) (403621/5000000000000:ℝ) (-216997748208405979/78125000000000000000000:ℝ) (17987049298196460369/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_438
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1315).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_438 :
    (∫ x in (219/256:ℝ)..(439/512:ℝ), x^12*thetaFirstMode x) ≤ (25394375028801/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (219/256:ℝ) (439/512:ℝ)
    (8632459/100000000000000:ℝ) (4036233/50000000000000:ℝ) (17987049298196460369/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_438 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1315).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_439 :
    (4880146353423/200000000000000000000000:ℝ) ≤ ∫ x in (439/512:ℝ)..(55/64:ℝ), x^12*thetaFirstMode x := by
  have hd : (-27765209890924093176995901/10000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (439/512:ℝ) (55/64:ℝ)-(106458482664671619457791/124159428129696431157760:ℝ)*thetaPowerMass 12 (439/512:ℝ) (55/64:ℝ)) ≤
      thetaFirstModeFirst (106458482664671619457791/124159428129696431157760:ℝ)*(thetaPowerMass 13 (439/512:ℝ) (55/64:ℝ)-(106458482664671619457791/124159428129696431157760:ℝ)*thetaPowerMass 12 (439/512:ℝ) (55/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0663.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (439/512:ℝ) (55/64:ℝ)
    (106458482664671619457791/124159428129696431157760:ℝ) (64553/800000000000:ℝ) (-27765209890924093176995901/10000000000000000000000000000000:ℝ) (84769028413781074171/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_439
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1319).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_439 :
    (∫ x in (439/512:ℝ)..(55/64:ℝ), x^12*thetaFirstMode x) ≤ (381279408921/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (439/512:ℝ) (55/64:ℝ)
    (4036233/50000000000000:ℝ) (7546789/100000000000000:ℝ) (84769028413781074171/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_439 (thetaFirstMode_refined_node_1315).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_440 :
    (11719920927397/500000000000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(441/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-12231313792804261279/5000000000000000000000000:ℝ)*(thetaPowerMass 13 (55/64:ℝ) (441/512:ℝ)-(441/512:ℝ)*thetaPowerMass 12 (55/64:ℝ) (441/512:ℝ)) ≤
      thetaFirstModeFirst (441/512:ℝ)*(thetaPowerMass 13 (55/64:ℝ) (441/512:ℝ)-(441/512:ℝ)*thetaPowerMass 12 (55/64:ℝ) (441/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0665.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (55/64:ℝ) (441/512:ℝ)
    (441/512:ℝ) (3526709/50000000000000:ℝ) (-12231313792804261279/5000000000000000000000000:ℝ) (3195123917450644637/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_440
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1321).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_440 :
    (∫ x in (55/64:ℝ)..(441/512:ℝ), x^12*thetaFirstMode x) ≤ (468809345753/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (55/64:ℝ) (441/512:ℝ)
    (7546789/100000000000000:ℝ) (7053459/100000000000000:ℝ) (3195123917450644637/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_440 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1321).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_441 :
    (22508423283891/1000000000000000000000000:ℝ) ≤ ∫ x in (441/512:ℝ)..(221/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1528333998050377289643369/625000000000000000000000000000:ℝ)*(thetaPowerMass 13 (441/512:ℝ) (221/256:ℝ)-(110903857005979655461809/128757361064545117135360:ℝ)*thetaPowerMass 12 (441/512:ℝ) (221/256:ℝ)) ≤
      thetaFirstModeFirst (110903857005979655461809/128757361064545117135360:ℝ)*(thetaPowerMass 13 (441/512:ℝ) (221/256:ℝ)-(110903857005979655461809/128757361064545117135360:ℝ)*thetaPowerMass 12 (441/512:ℝ) (221/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0666.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (441/512:ℝ) (221/256:ℝ)
    (110903857005979655461809/128757361064545117135360:ℝ) (705053/10000000000000:ℝ) (-1528333998050377289643369/625000000000000000000000000000:ℝ) (188122596808558179/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_441
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1325).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_441 :
    (∫ x in (441/512:ℝ)..(221/256:ℝ), x^12*thetaFirstMode x) ≤ (2813688676133/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (441/512:ℝ) (221/256:ℝ)
    (7053459/100000000000000:ℝ) (411913/6250000000000:ℝ) (188122596808558179/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_441 (thetaFirstMode_refined_node_1321).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_442 :
    (10803895615231/500000000000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(443/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-53803975444308041999/25000000000000000000000000:ℝ)*(thetaPowerMass 13 (221/256:ℝ) (443/512:ℝ)-(443/512:ℝ)*thetaPowerMass 12 (221/256:ℝ) (443/512:ℝ)) ≤
      thetaFirstModeFirst (443/512:ℝ)*(thetaPowerMass 13 (221/256:ℝ) (443/512:ℝ)-(443/512:ℝ)*thetaPowerMass 12 (221/256:ℝ) (443/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0668.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (221/256:ℝ) (443/512:ℝ)
    (443/512:ℝ) (3078217/50000000000000:ℝ) (-53803975444308041999/25000000000000000000000000:ℝ) (566952332575732811/8000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_442
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1327).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_442 :
    (∫ x in (221/256:ℝ)..(443/512:ℝ), x^12*thetaFirstMode x) ≤ (5402095358241/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (221/256:ℝ) (443/512:ℝ)
    (411913/6250000000000:ℝ) (615647/10000000000000:ℝ) (566952332575732811/8000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_442 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1327).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_443 :
    (20735431738589/1000000000000000000000000:ℝ) ≤ ∫ x in (443/512:ℝ)..(111/128:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1344586981700192143839367/625000000000000000000000000000:ℝ)*(thetaPowerMass 13 (443/512:ℝ) (111/128:ℝ)-(115513472527065173117007/133503598919808937500160:ℝ)*thetaPowerMass 12 (443/512:ℝ) (111/128:ℝ)) ≤
      thetaFirstModeFirst (115513472527065173117007/133503598919808937500160:ℝ)*(thetaPowerMass 13 (443/512:ℝ) (111/128:ℝ)-(115513472527065173117007/133503598919808937500160:ℝ)*thetaPowerMass 12 (443/512:ℝ) (111/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0669.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (443/512:ℝ) (111/128:ℝ)
    (115513472527065173117007/133503598919808937500160:ℝ) (384619/6250000000000:ℝ) (-1344586981700192143839367/625000000000000000000000000000:ℝ) (13345164857540070351/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_443
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1331).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_443 :
    (∫ x in (443/512:ℝ)..(111/128:ℝ), x^12*thetaFirstMode x) ≤ (207364574169/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (443/512:ℝ) (111/128:ℝ)
    (615647/10000000000000:ℝ) (2874687/50000000000000:ℝ) (13345164857540070351/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_443 (thetaFirstMode_refined_node_1327).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_444 :
    (994627804627/50000000000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(445/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-23642058480249863763/12500000000000000000000000:ℝ)*(thetaPowerMass 13 (111/128:ℝ) (445/512:ℝ)-(445/512:ℝ)*thetaPowerMass 12 (111/128:ℝ) (445/512:ℝ)) ≤
      thetaFirstModeFirst (445/512:ℝ)*(thetaPowerMass 13 (111/128:ℝ) (445/512:ℝ)-(445/512:ℝ)*thetaPowerMass 12 (111/128:ℝ) (445/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0671.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (111/128:ℝ) (445/512:ℝ)
    (445/512:ℝ) (1341927/25000000000000:ℝ) (-23642058480249863763/12500000000000000000000000:ℝ) (6280768722054132469/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_444
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1333).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_444 :
    (∫ x in (111/128:ℝ)..(445/512:ℝ), x^12*thetaFirstMode x) ≤ (9946554745593/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (111/128:ℝ) (445/512:ℝ)
    (2874687/50000000000000:ℝ) (5367739/100000000000000:ℝ) (6280768722054132469/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_444 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1333).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_445 :
    (1907674759607/100000000000000000000000:ℝ) ≤ ∫ x in (445/512:ℝ)..(223/256:ℝ), x^12*thetaFirstMode x := by
  have hd : (-1890641322490252181259421/1000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (445/512:ℝ) (223/256:ℝ)-(24058522909244262175605/27680444625863446871552:ℝ)*thetaPowerMass 12 (445/512:ℝ) (223/256:ℝ)) ≤
      thetaFirstModeFirst (24058522909244262175605/27680444625863446871552:ℝ)*(thetaPowerMass 13 (445/512:ℝ) (223/256:ℝ)-(24058522909244262175605/27680444625863446871552:ℝ)*thetaPowerMass 12 (445/512:ℝ) (223/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0672.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (445/512:ℝ) (223/256:ℝ)
    (24058522909244262175605/27680444625863446871552:ℝ) (1073099/20000000000000:ℝ) (-1890641322490252181259421/1000000000000000000000000000000:ℝ) (14775851413730711587/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_445
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1337).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_445 :
    (∫ x in (445/512:ℝ)..(223/256:ℝ), x^12*thetaFirstMode x) ≤ (19077710672047/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (445/512:ℝ) (223/256:ℝ)
    (5367739/100000000000000:ℝ) (5010071/100000000000000:ℝ) (14775851413730711587/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_445 (thetaFirstMode_refined_node_1333).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_446 :
    (18289108553281/1000000000000000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(447/512:ℝ), x^12*thetaFirstMode x := by
  have hd : (-83017970264052112557/50000000000000000000000000:ℝ)*(thetaPowerMass 13 (223/256:ℝ) (447/512:ℝ)-(447/512:ℝ)*thetaPowerMass 12 (223/256:ℝ) (447/512:ℝ)) ≤
      thetaFirstModeFirst (447/512:ℝ)*(thetaPowerMass 13 (223/256:ℝ) (447/512:ℝ)-(447/512:ℝ)*thetaPowerMass 12 (223/256:ℝ) (447/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0674.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (223/256:ℝ) (447/512:ℝ)
    (447/512:ℝ) (4674927/100000000000000:ℝ) (-83017970264052112557/50000000000000000000000000:ℝ) (27801147271290414531/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_446
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1339).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_446 :
    (∫ x in (223/256:ℝ)..(447/512:ℝ), x^12*thetaFirstMode x) ≤ (18289631479157/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (223/256:ℝ) (447/512:ℝ)
    (5010071/100000000000000:ℝ) (934991/20000000000000:ℝ) (27801147271290414531/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_446 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1339).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_12_447 :
    (17527335304377/1000000000000000000000000:ℝ) ≤ ∫ x in (447/512:ℝ)..(7/8:ℝ), x^12*thetaFirstMode x := by
  have hd : (-41493055534829519713612419/25000000000000000000000000000000:ℝ)*(thetaPowerMass 13 (447/512:ℝ) (7/8:ℝ)-(125246713502597024463543/143457408303917490588160:ℝ)*thetaPowerMass 12 (447/512:ℝ) (7/8:ℝ)) ≤
      thetaFirstModeFirst (125246713502597024463543/143457408303917490588160:ℝ)*(thetaPowerMass 13 (447/512:ℝ) (7/8:ℝ)-(125246713502597024463543/143457408303917490588160:ℝ)*thetaPowerMass 12 (447/512:ℝ) (7/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0675.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 12 (447/512:ℝ) (7/8:ℝ)
    (125246713502597024463543/143457408303917490588160:ℝ) (4672993/100000000000000:ℝ) (-41493055534829519713612419/25000000000000000000000000000000:ℝ) (13073532968807063897/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_447
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1343).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_12_447 :
    (∫ x in (447/512:ℝ)..(7/8:ℝ), x^12*thetaFirstMode x) ≤ (3505648596947/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 12 (447/512:ℝ) (7/8:ℝ)
    (934991/20000000000000:ℝ) (136283/3125000000000:ℝ) (13073532968807063897/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_447 (thetaFirstMode_refined_node_1339).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

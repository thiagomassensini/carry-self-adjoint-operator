import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature13
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative19
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative20
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative21

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_10_416 :
    (85005976185073/1000000000000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(417/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-262182886591060890091/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (13/16:ℝ) (417/512:ℝ)-(417/512:ℝ)*thetaPowerMass 10 (13/16:ℝ) (417/512:ℝ)) ≤
      thetaFirstModeFirst (417/512:ℝ)*(thetaPowerMass 11 (13/16:ℝ) (417/512:ℝ)-(417/512:ℝ)*thetaPowerMass 10 (13/16:ℝ) (417/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0629.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (13/16:ℝ) (417/512:ℝ)
    (417/512:ℝ) (16628833/50000000000000:ℝ) (-262182886591060890091/25000000000000000000000000:ℝ) (154697424799214552691/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_416
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1249).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_416 :
    (∫ x in (13/16:ℝ)..(417/512:ℝ), x^10*thetaFirstMode x) ≤ (1700154508233/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/16:ℝ) (417/512:ℝ)
    (35366227/100000000000000:ℝ) (33257837/100000000000000:ℝ) (154697424799214552691/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_416 (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1249).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_417 :
    (8186721714251/100000000000000000000000:ℝ) ≤ ∫ x in (417/512:ℝ)..(209/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-262087729107131110010299747/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (417/512:ℝ) (209/256:ℝ)-(67023486088292228081193/82291363666684906908160:ℝ)*thetaPowerMass 10 (417/512:ℝ) (209/256:ℝ)) ≤
      thetaFirstModeFirst (67023486088292228081193/82291363666684906908160:ℝ)*(thetaPowerMass 11 (417/512:ℝ) (209/256:ℝ)-(67023486088292228081193/82291363666684906908160:ℝ)*thetaPowerMass 10 (417/512:ℝ) (209/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0630.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (417/512:ℝ) (209/256:ℝ)
    (67023486088292228081193/82291363666684906908160:ℝ) (33244571/100000000000000:ℝ) (-262087729107131110010299747/25000000000000000000000000000000:ℝ) (36659716912842526041/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_417
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1253).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_417 :
    (∫ x in (417/512:ℝ)..(209/256:ℝ), x^10*thetaFirstMode x) ≤ (16374039217789/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (417/512:ℝ) (209/256:ℝ)
    (33257837/100000000000000:ℝ) (15633749/50000000000000:ℝ) (36659716912842526041/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_417 (thetaFirstMode_refined_node_1249).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_418 :
    (3152919480383/40000000000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(419/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-467059859576881899207/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (209/256:ℝ) (419/512:ℝ)-(419/512:ℝ)*thetaPowerMass 10 (209/256:ℝ) (419/512:ℝ)) ≤
      thetaFirstModeFirst (419/512:ℝ)*(thetaPowerMass 11 (209/256:ℝ) (419/512:ℝ)-(419/512:ℝ)*thetaPowerMass 10 (209/256:ℝ) (419/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0632.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (209/256:ℝ) (419/512:ℝ)
    (419/512:ℝ) (29388909/100000000000000:ℝ) (-467059859576881899207/50000000000000000000000000:ℝ) (277931522703706091913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_418
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1255).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_418 :
    (∫ x in (209/256:ℝ)..(419/512:ℝ), x^10*thetaFirstMode x) ≤ (39412321200781/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (209/256:ℝ) (419/512:ℝ)
    (15633749/50000000000000:ℝ) (29389061/100000000000000:ℝ) (277931522703706091913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_418 (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1255).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_419 :
    (9483321310247/125000000000000000000000:ℝ) ≤ ∫ x in (419/512:ℝ)..(105/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-58361215101033611177754681/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (419/512:ℝ) (105/128:ℝ)-(69972668969052009938391/85502296803586871580160:ℝ)*thetaPowerMass 10 (419/512:ℝ) (105/128:ℝ)) ≤
      thetaFirstModeFirst (69972668969052009938391/85502296803586871580160:ℝ)*(thetaPowerMass 11 (419/512:ℝ) (105/128:ℝ)-(69972668969052009938391/85502296803586871580160:ℝ)*thetaPowerMass 10 (419/512:ℝ) (105/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0633.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (419/512:ℝ) (105/128:ℝ)
    (69972668969052009938391/85502296803586871580160:ℝ) (293773/1000000000000:ℝ) (-58361215101033611177754681/6250000000000000000000000000000:ℝ) (16457687982596865951/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_419
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1259).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_419 :
    (∫ x in (419/512:ℝ)..(105/128:ℝ), x^10*thetaFirstMode x) ≤ (37934698387037/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (419/512:ℝ) (105/128:ℝ)
    (29389061/100000000000000:ℝ) (2761667/10000000000000:ℝ) (16457687982596865951/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_419 (thetaFirstMode_refined_node_1255).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_420 :
    (36500607022619/500000000000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(421/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-103901649138329984669/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (105/128:ℝ) (421/512:ℝ)-(421/512:ℝ)*thetaPowerMass 10 (105/128:ℝ) (421/512:ℝ)) ≤
      thetaFirstModeFirst (421/512:ℝ)*(thetaPowerMass 11 (105/128:ℝ) (421/512:ℝ)-(421/512:ℝ)*thetaPowerMass 10 (105/128:ℝ) (421/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0635.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (105/128:ℝ) (421/512:ℝ)
    (421/512:ℝ) (25944617/100000000000000:ℝ) (-103901649138329984669/12500000000000000000000000:ℝ) (249420229777245076453/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_420
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1261).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_420 :
    (∫ x in (105/128:ℝ)..(421/512:ℝ), x^10*thetaFirstMode x) ≤ (7300277953811/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (105/128:ℝ) (421/512:ℝ)
    (2761667/10000000000000:ℝ) (1621547/6250000000000:ℝ) (249420229777245076453/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_420 (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1261).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_421 :
    (35110212242937/500000000000000000000000:ℝ) ≤ ∫ x in (421/512:ℝ)..(211/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-207727320810335136609106977/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (421/512:ℝ) (211/256:ℝ)-(73036644780581807459409/88822326679864764136960:ℝ)*thetaPowerMass 10 (421/512:ℝ) (211/256:ℝ)) ≤
      thetaFirstModeFirst (73036644780581807459409/88822326679864764136960:ℝ)*(thetaPowerMass 11 (421/512:ℝ) (211/256:ℝ)-(73036644780581807459409/88822326679864764136960:ℝ)*thetaPowerMass 10 (421/512:ℝ) (211/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0636.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (421/512:ℝ) (211/256:ℝ)
    (73036644780581807459409/88822326679864764136960:ℝ) (50653/195312500000:ℝ) (-207727320810335136609106977/25000000000000000000000000000000:ℝ) (236192444692696261033/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_421
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1265).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_421 :
    (∫ x in (421/512:ℝ)..(211/256:ℝ), x^10*thetaFirstMode x) ≤ (8777887618831/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (421/512:ℝ) (211/256:ℝ)
    (1621547/6250000000000:ℝ) (12184001/50000000000000:ℝ) (236192444692696261033/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_421 (thetaFirstMode_refined_node_1261).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_422 :
    (3376359096663/50000000000000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(423/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-73890845283712051279/10000000000000000000000000:ℝ)*(thetaPowerMass 11 (211/256:ℝ) (423/512:ℝ)-(423/512:ℝ)*thetaPowerMass 10 (211/256:ℝ) (423/512:ℝ)) ≤
      thetaFirstModeFirst (423/512:ℝ)*(thetaPowerMass 11 (211/256:ℝ) (423/512:ℝ)-(423/512:ℝ)*thetaPowerMass 10 (211/256:ℝ) (423/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0638.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (211/256:ℝ) (423/512:ℝ)
    (423/512:ℝ) (22881253/100000000000000:ℝ) (-73890845283712051279/10000000000000000000000000:ℝ) (223610065160718119631/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_422
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1267).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_422 :
    (∫ x in (211/256:ℝ)..(423/512:ℝ), x^10*thetaFirstMode x) ≤ (1350573265593/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (211/256:ℝ) (423/512:ℝ)
    (12184001/50000000000000:ℝ) (11440687/50000000000000:ℝ) (223610065160718119631/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_422 (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1267).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_423 :
    (811440327771/12500000000000000000000:ℝ) ≤ ∫ x in (423/512:ℝ)..(53/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-46164833162719103188474261/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (423/512:ℝ) (53/64:ℝ)-(76219304315222090354607/92254615216783819932160:ℝ)*thetaPowerMass 10 (423/512:ℝ) (53/64:ℝ)) ≤
      thetaFirstModeFirst (76219304315222090354607/92254615216783819932160:ℝ)*(thetaPowerMass 11 (423/512:ℝ) (53/64:ℝ)-(76219304315222090354607/92254615216783819932160:ℝ)*thetaPowerMass 10 (423/512:ℝ) (53/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0639.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (423/512:ℝ) (53/64:ℝ)
    (76219304315222090354607/92254615216783819932160:ℝ) (22872157/100000000000000:ℝ) (-46164833162719103188474261/6250000000000000000000000000000:ℝ) (264555831899039919/1250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_423
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1271).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_423 :
    (∫ x in (423/512:ℝ)..(53/64:ℝ), x^10*thetaFirstMode x) ≤ (8114720176933/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (423/512:ℝ) (53/64:ℝ)
    (11440687/50000000000000:ℝ) (10740033/50000000000000:ℝ) (264555831899039919/1250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_423 (thetaFirstMode_refined_node_1267).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_424 :
    (31193643680293/500000000000000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(425/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-82024544432356675749/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (53/64:ℝ) (425/512:ℝ)-(425/512:ℝ)*thetaPowerMass 10 (53/64:ℝ) (425/512:ℝ)) ≤
      thetaFirstModeFirst (425/512:ℝ)*(thetaPowerMass 11 (53/64:ℝ) (425/512:ℝ)-(425/512:ℝ)*thetaPowerMass 10 (53/64:ℝ) (425/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0641.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (53/64:ℝ) (425/512:ℝ)
    (425/512:ℝ) (10079703/50000000000000:ℝ) (-82024544432356675749/12500000000000000000000000:ℝ) (40053779141744391673/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_424
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1273).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_424 :
    (∫ x in (53/64:ℝ)..(425/512:ℝ), x^10*thetaFirstMode x) ≤ (15597171245231/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (53/64:ℝ) (425/512:ℝ)
    (10740033/50000000000000:ℝ) (20159513/100000000000000:ℝ) (40053779141744391673/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_424 (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1273).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_425 :
    (14984332200453/250000000000000000000000:ℝ) ≤ ∫ x in (425/512:ℝ)..(213/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-327977334446131963136579723/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (425/512:ℝ) (213/256:ℝ)-(15904930171669675505325/19160480067509209098752:ℝ)*thetaPowerMass 10 (425/512:ℝ) (213/256:ℝ)) ≤
      thetaFirstModeFirst (15904930171669675505325/19160480067509209098752:ℝ)*(thetaPowerMass 11 (425/512:ℝ) (213/256:ℝ)-(15904930171669675505325/19160480067509209098752:ℝ)*thetaPowerMass 10 (425/512:ℝ) (213/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0642.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (425/512:ℝ) (213/256:ℝ)
    (15904930171669675505325/19160480067509209098752:ℝ) (10075683/50000000000000:ℝ) (-327977334446131963136579723/50000000000000000000000000000000:ℝ) (189456469475912015979/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_425
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1277).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_425 :
    (∫ x in (425/512:ℝ)..(213/256:ℝ), x^10*thetaFirstMode x) ≤ (59939723615971/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (425/512:ℝ) (213/256:ℝ)
    (20159513/100000000000000:ℝ) (151323/800000000000:ℝ) (189456469475912015979/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_425 (thetaFirstMode_refined_node_1273).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_426 :
    (11513569408179/200000000000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(427/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-145538713209367669413/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (213/256:ℝ) (427/512:ℝ)-(427/512:ℝ)*thetaPowerMass 10 (213/256:ℝ) (427/512:ℝ)) ≤
      thetaFirstModeFirst (427/512:ℝ)*(thetaPowerMass 11 (213/256:ℝ) (427/512:ℝ)-(427/512:ℝ)*thetaPowerMass 10 (213/256:ℝ) (427/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0644.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (213/256:ℝ) (427/512:ℝ)
    (427/512:ℝ) (17743431/100000000000000:ℝ) (-145538713209367669413/25000000000000000000000000:ℝ) (179182140372564781941/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_426
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1279).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_426 :
    (∫ x in (213/256:ℝ)..(427/512:ℝ), x^10*thetaFirstMode x) ≤ (57569165143733/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (213/256:ℝ) (427/512:ℝ)
    (151323/800000000000:ℝ) (8871763/50000000000000:ℝ) (179182140372564781941/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_426 (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1279).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_427 :
    (55273040130011/1000000000000000000000000:ℝ) ≤ ∫ x in (427/512:ℝ)..(107/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-58193965464152993522552829/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (427/512:ℝ) (107/128:ℝ)-(82956802885821125866143/99468997421790285852160:ℝ)*thetaPowerMass 10 (427/512:ℝ) (107/128:ℝ)) ≤
      thetaFirstModeFirst (82956802885821125866143/99468997421790285852160:ℝ)*(thetaPowerMass 11 (427/512:ℝ) (107/128:ℝ)-(82956802885821125866143/99468997421790285852160:ℝ)*thetaPowerMass 10 (427/512:ℝ) (107/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0645.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (427/512:ℝ) (107/128:ℝ)
    (82956802885821125866143/99468997421790285852160:ℝ) (4434083/25000000000000:ℝ) (-58193965464152993522552829/10000000000000000000000000000000:ℝ) (42355413677653710627/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_427
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1283).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_427 :
    (∫ x in (427/512:ℝ)..(107/128:ℝ), x^10*thetaFirstMode x) ≤ (13818824975551/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (427/512:ℝ) (107/128:ℝ)
    (8871763/50000000000000:ℝ) (16640047/100000000000000:ℝ) (42355413677653710627/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_427 (thetaFirstMode_refined_node_1279).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_428 :
    (13263794482889/250000000000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(429/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-32246409507344621121/6250000000000000000000000:ℝ)*(thetaPowerMass 11 (107/128:ℝ) (429/512:ℝ)-(429/512:ℝ)*thetaPowerMass 10 (107/128:ℝ) (429/512:ℝ)) ≤
      thetaFirstModeFirst (429/512:ℝ)*(thetaPowerMass 11 (107/128:ℝ) (429/512:ℝ)-(429/512:ℝ)*thetaPowerMass 10 (107/128:ℝ) (429/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0647.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (107/128:ℝ) (429/512:ℝ)
    (429/512:ℝ) (1950141/12500000000000:ℝ) (-32246409507344621121/6250000000000000000000000:ℝ) (80075860635909528499/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_428
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1285).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_428 :
    (∫ x in (107/128:ℝ)..(429/512:ℝ), x^10*thetaFirstMode x) ≤ (26528210375957/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (107/128:ℝ) (429/512:ℝ)
    (16640047/100000000000000:ℝ) (15601213/100000000000000:ℝ) (80075860635909528499/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_428 (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1285).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_429 :
    (10181738370053/200000000000000000000000:ℝ) ≤ ∫ x in (429/512:ℝ)..(215/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-10315022379513419488123/2000000000000000000000000000:ℝ)*(thetaPowerMass 11 (429/512:ℝ) (215/256:ℝ)-(86519996812935046058841/103257800780870084584960:ℝ)*thetaPowerMass 10 (429/512:ℝ) (215/256:ℝ)) ≤
      thetaFirstModeFirst (86519996812935046058841/103257800780870084584960:ℝ)*(thetaPowerMass 11 (429/512:ℝ) (215/256:ℝ)-(86519996812935046058841/103257800780870084584960:ℝ)*thetaPowerMass 10 (429/512:ℝ) (215/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0648.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (429/512:ℝ) (215/256:ℝ)
    (86519996812935046058841/103257800780870084584960:ℝ) (7797433/50000000000000:ℝ) (-10315022379513419488123/2000000000000000000000000000:ℝ) (75674989066615317153/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_429
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1289).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_429 :
    (∫ x in (429/512:ℝ)..(215/256:ℝ), x^10*thetaFirstMode x) ≤ (50910823274401/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (429/512:ℝ) (215/256:ℝ)
    (15601213/100000000000000:ℝ) (14623487/100000000000000:ℝ) (75674989066615317153/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_429 (thetaFirstMode_refined_node_1285).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_430 :
    (24417821604643/500000000000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(431/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-57099046627044903519/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (215/256:ℝ) (431/512:ℝ)-(431/512:ℝ)*thetaPowerMass 10 (215/256:ℝ) (431/512:ℝ)) ≤
      thetaFirstModeFirst (431/512:ℝ)*(thetaPowerMass 11 (215/256:ℝ) (431/512:ℝ)-(431/512:ℝ)*thetaPowerMass 10 (215/256:ℝ) (431/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0650.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (215/256:ℝ) (431/512:ℝ)
    (431/512:ℝ) (3425859/25000000000000:ℝ) (-57099046627044903519/12500000000000000000000000:ℝ) (142994966948344169319/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_430
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1291).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_430 :
    (∫ x in (215/256:ℝ)..(431/512:ℝ), x^10*thetaFirstMode x) ≤ (48836811287177/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (215/256:ℝ) (431/512:ℝ)
    (14623487/100000000000000:ℝ) (13703511/100000000000000:ℝ) (142994966948344169319/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_430 (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1291).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_431 :
    (23415344159869/500000000000000000000000:ℝ) ≤ ∫ x in (431/512:ℝ)..(27/32:ℝ), x^10*thetaFirstMode x := by
  have hd : (-28538890652579743145831737/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (431/512:ℝ) (27/32:ℝ)-(90218589795601773832359/107172285154106278812160:ℝ)*thetaPowerMass 10 (431/512:ℝ) (27/32:ℝ)) ≤
      thetaFirstModeFirst (90218589795601773832359/107172285154106278812160:ℝ)*(thetaPowerMass 11 (431/512:ℝ) (27/32:ℝ)-(90218589795601773832359/107172285154106278812160:ℝ)*thetaPowerMass 10 (431/512:ℝ) (27/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0651.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (431/512:ℝ) (27/32:ℝ)
    (90218589795601773832359/107172285154106278812160:ℝ) (13697917/100000000000000:ℝ) (-28538890652579743145831737/6250000000000000000000000000000:ℝ) (67533041812260745961/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_431
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1295).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_431 :
    (∫ x in (431/512:ℝ)..(27/32:ℝ), x^10*thetaFirstMode x) ≤ (182940220143/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (431/512:ℝ) (27/32:ℝ)
    (13703511/100000000000000:ℝ) (12838097/100000000000000:ℝ) (67533041812260745961/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_431 (thetaFirstMode_refined_node_1291).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_432 :
    (22447851827581/500000000000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(433/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-101001430243798734633/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (27/32:ℝ) (433/512:ℝ)-(433/512:ℝ)*thetaPowerMass 10 (27/32:ℝ) (433/512:ℝ)) ≤
      thetaFirstModeFirst (433/512:ℝ)*(thetaPowerMass 11 (27/32:ℝ) (433/512:ℝ)-(433/512:ℝ)*thetaPowerMass 10 (27/32:ℝ) (433/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0653.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (27/32:ℝ) (433/512:ℝ)
    (433/512:ℝ) (6012077/50000000000000:ℝ) (-101001430243798734633/25000000000000000000000000:ℝ) (12754359956592189627/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_432
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1297).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_432 :
    (∫ x in (27/32:ℝ)..(433/512:ℝ), x^10*thetaFirstMode x) ≤ (11224199835553/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/32:ℝ) (433/512:ℝ)
    (12838097/100000000000000:ℝ) (601211/5000000000000:ℝ) (12754359956592189627/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_432 (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1297).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_433 :
    (21512781668003/500000000000000000000000:ℝ) ≤ ∫ x in (433/512:ℝ)..(217/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-100963667168440885867516937/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (433/512:ℝ) (217/256:ℝ)-(94057062584506765152057/111216007226212200348160:ℝ)*thetaPowerMass 10 (433/512:ℝ) (217/256:ℝ)) ≤
      thetaFirstModeFirst (94057062584506765152057/111216007226212200348160:ℝ)*(thetaPowerMass 11 (433/512:ℝ) (217/256:ℝ)-(94057062584506765152057/111216007226212200348160:ℝ)*thetaPowerMass 10 (433/512:ℝ) (217/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0654.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (433/512:ℝ) (217/256:ℝ)
    (94057062584506765152057/111216007226212200348160:ℝ) (2403859/20000000000000:ℝ) (-100963667168440885867516937/25000000000000000000000000000000:ℝ) (30102135937187152831/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_433
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1301).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_433 :
    (∫ x in (433/512:ℝ)..(217/256:ℝ), x^10*thetaFirstMode x) ≤ (21513725334359/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (433/512:ℝ) (217/256:ℝ)
    (601211/5000000000000:ℝ) (11259009/100000000000000:ℝ) (30102135937187152831/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_433 (thetaFirstMode_refined_node_1297).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_434 :
    (329775717511/8000000000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(435/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-44618380725938895207/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (217/256:ℝ) (435/512:ℝ)-(435/512:ℝ)*thetaPowerMass 10 (217/256:ℝ) (435/512:ℝ)) ≤
      thetaFirstModeFirst (435/512:ℝ)*(thetaPowerMass 11 (217/256:ℝ) (435/512:ℝ)-(435/512:ℝ)*thetaPowerMass 10 (217/256:ℝ) (435/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0656.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (217/256:ℝ) (435/512:ℝ)
    (435/512:ℝ) (2634921/25000000000000:ℝ) (-44618380725938895207/12500000000000000000000000:ℝ) (28410692966885968931/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_434
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1303).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_434 :
    (∫ x in (217/256:ℝ)..(435/512:ℝ), x^10*thetaFirstMode x) ≤ (20611497443687/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (217/256:ℝ) (435/512:ℝ)
    (11259009/100000000000000:ℝ) (10539743/100000000000000:ℝ) (28410692966885968931/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_434 (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1303).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_435 :
    (39480018270521/1000000000000000000000000:ℝ) ≤ ∫ x in (435/512:ℝ)..(109/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-17840655793648345212111183/5000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (435/512:ℝ) (109/128:ℝ)-(19608004486597651322715/23078521433218056637952:ℝ)*thetaPowerMass 10 (435/512:ℝ) (109/128:ℝ)) ≤
      thetaFirstModeFirst (19608004486597651322715/23078521433218056637952:ℝ)*(thetaPowerMass 11 (435/512:ℝ) (109/128:ℝ)-(19608004486597651322715/23078521433218056637952:ℝ)*thetaPowerMass 10 (435/512:ℝ) (109/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0657.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (435/512:ℝ) (109/128:ℝ)
    (19608004486597651322715/23078521433218056637952:ℝ) (2633853/25000000000000:ℝ) (-17840655793648345212111183/5000000000000000000000000000000:ℝ) (107228885635937195173/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_435
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1307).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_435 :
    (∫ x in (435/512:ℝ)..(109/128:ℝ), x^10*thetaFirstMode x) ≤ (39481788568877/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (435/512:ℝ) (109/128:ℝ)
    (10539743/100000000000000:ℝ) (9863839/100000000000000:ℝ) (107228885635937195173/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_435 (thetaFirstMode_refined_node_1303).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_436 :
    (7560247469589/200000000000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(437/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-39379864891416292301/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (109/128:ℝ) (437/512:ℝ)-(437/512:ℝ)*thetaPowerMass 10 (109/128:ℝ) (437/512:ℝ)) ≤
      thetaFirstModeFirst (437/512:ℝ)*(thetaPowerMass 11 (109/128:ℝ) (437/512:ℝ)-(437/512:ℝ)*thetaPowerMass 10 (109/128:ℝ) (437/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0659.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (109/128:ℝ) (437/512:ℝ)
    (437/512:ℝ) (9228799/100000000000000:ℝ) (-39379864891416292301/12500000000000000000000000:ℝ) (101150201789825405357/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_436
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1309).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_436 :
    (∫ x in (109/128:ℝ)..(437/512:ℝ), x^10*thetaFirstMode x) ≤ (37802202560677/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (109/128:ℝ) (437/512:ℝ)
    (9863839/100000000000000:ℝ) (9228851/100000000000000:ℝ) (101150201789825405357/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_436 (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1309).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_437 :
    (36180964716077/1000000000000000000000000:ℝ) ≤ ∫ x in (437/512:ℝ)..(219/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-78730065960210806203937833/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (437/512:ℝ) (219/256:ℝ)-(102172206059393137678593/119705810187199806492160:ℝ)*thetaPowerMass 10 (437/512:ℝ) (219/256:ℝ)) ≤
      thetaFirstModeFirst (102172206059393137678593/119705810187199806492160:ℝ)*(thetaPowerMass 11 (437/512:ℝ) (219/256:ℝ)-(102172206059393137678593/119705810187199806492160:ℝ)*thetaPowerMass 10 (437/512:ℝ) (219/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0660.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (437/512:ℝ) (219/256:ℝ)
    (102172206059393137678593/119705810187199806492160:ℝ) (4612523/50000000000000:ℝ) (-78730065960210806203937833/25000000000000000000000000000000:ℝ) (95390762738773861167/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_437
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1313).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_437 :
    (∫ x in (437/512:ℝ)..(219/256:ℝ), x^10*thetaFirstMode x) ≤ (36182625048247/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (437/512:ℝ) (219/256:ℝ)
    (9228851/100000000000000:ℝ) (8632459/100000000000000:ℝ) (95390762738773861167/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_437 (thetaFirstMode_refined_node_1309).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_438 :
    (34620556620429/1000000000000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(439/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-216997748208405979/78125000000000000000000:ℝ)*(thetaPowerMass 11 (219/256:ℝ) (439/512:ℝ)-(439/512:ℝ)*thetaPowerMass 10 (219/256:ℝ) (439/512:ℝ)) ≤
      thetaFirstModeFirst (439/512:ℝ)*(thetaPowerMass 11 (219/256:ℝ) (439/512:ℝ)-(439/512:ℝ)*thetaPowerMass 10 (219/256:ℝ) (439/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0662.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (219/256:ℝ) (439/512:ℝ)
    (439/512:ℝ) (403621/5000000000000:ℝ) (-216997748208405979/78125000000000000000000:ℝ) (17987049298196460369/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_438
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1315).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_438 :
    (∫ x in (219/256:ℝ)..(439/512:ℝ), x^10*thetaFirstMode x) ≤ (34621459697487/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (219/256:ℝ) (439/512:ℝ)
    (8632459/100000000000000:ℝ) (4036233/50000000000000:ℝ) (17987049298196460369/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_438 (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1315).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_439 :
    (33115566099033/1000000000000000000000000:ℝ) ≤ ∫ x in (439/512:ℝ)..(55/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-27765209890924093176995901/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (439/512:ℝ) (55/64:ℝ)-(106458482664671619457791/124159428129696431157760:ℝ)*thetaPowerMass 10 (439/512:ℝ) (55/64:ℝ)) ≤
      thetaFirstModeFirst (106458482664671619457791/124159428129696431157760:ℝ)*(thetaPowerMass 11 (439/512:ℝ) (55/64:ℝ)-(106458482664671619457791/124159428129696431157760:ℝ)*thetaPowerMass 10 (439/512:ℝ) (55/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0663.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (439/512:ℝ) (55/64:ℝ)
    (106458482664671619457791/124159428129696431157760:ℝ) (64553/800000000000:ℝ) (-27765209890924093176995901/10000000000000000000000000000000:ℝ) (84769028413781074171/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_439
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1319).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_439 :
    (∫ x in (439/512:ℝ)..(55/64:ℝ), x^10*thetaFirstMode x) ≤ (8279281576233/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (439/512:ℝ) (55/64:ℝ)
    (4036233/50000000000000:ℝ) (7546789/100000000000000:ℝ) (84769028413781074171/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_439 (thetaFirstMode_refined_node_1315).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_440 :
    (3166722145421/100000000000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(441/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-12231313792804261279/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (55/64:ℝ) (441/512:ℝ)-(441/512:ℝ)*thetaPowerMass 10 (55/64:ℝ) (441/512:ℝ)) ≤
      thetaFirstModeFirst (441/512:ℝ)*(thetaPowerMass 11 (55/64:ℝ) (441/512:ℝ)-(441/512:ℝ)*thetaPowerMass 10 (55/64:ℝ) (441/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0665.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (55/64:ℝ) (441/512:ℝ)
    (441/512:ℝ) (3526709/50000000000000:ℝ) (-12231313792804261279/5000000000000000000000000:ℝ) (3195123917450644637/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_440
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1321).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_440 :
    (∫ x in (55/64:ℝ)..(441/512:ℝ), x^10*thetaFirstMode x) ≤ (15834033449639/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (55/64:ℝ) (441/512:ℝ)
    (7546789/100000000000000:ℝ) (7053459/100000000000000:ℝ) (3195123917450644637/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_440 (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1321).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_441 :
    (7567820657327/250000000000000000000000:ℝ) ≤ ∫ x in (441/512:ℝ)..(221/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1528333998050377289643369/625000000000000000000000000000:ℝ)*(thetaPowerMass 11 (441/512:ℝ) (221/256:ℝ)-(110903857005979655461809/128757361064545117135360:ℝ)*thetaPowerMass 10 (441/512:ℝ) (221/256:ℝ)) ≤
      thetaFirstModeFirst (110903857005979655461809/128757361064545117135360:ℝ)*(thetaPowerMass 11 (441/512:ℝ) (221/256:ℝ)-(110903857005979655461809/128757361064545117135360:ℝ)*thetaPowerMass 10 (441/512:ℝ) (221/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0666.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (441/512:ℝ) (221/256:ℝ)
    (110903857005979655461809/128757361064545117135360:ℝ) (705053/10000000000000:ℝ) (-1528333998050377289643369/625000000000000000000000000000:ℝ) (188122596808558179/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_441
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1325).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_441 :
    (∫ x in (441/512:ℝ)..(221/256:ℝ), x^10*thetaFirstMode x) ≤ (30272742344779/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (441/512:ℝ) (221/256:ℝ)
    (7053459/100000000000000:ℝ) (411913/6250000000000:ℝ) (188122596808558179/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_441 (thetaFirstMode_refined_node_1321).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_442 :
    (14464419533431/500000000000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(443/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-53803975444308041999/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (221/256:ℝ) (443/512:ℝ)-(443/512:ℝ)*thetaPowerMass 10 (221/256:ℝ) (443/512:ℝ)) ≤
      thetaFirstModeFirst (443/512:ℝ)*(thetaPowerMass 11 (221/256:ℝ) (443/512:ℝ)-(443/512:ℝ)*thetaPowerMass 10 (221/256:ℝ) (443/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0668.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (221/256:ℝ) (443/512:ℝ)
    (443/512:ℝ) (3078217/50000000000000:ℝ) (-53803975444308041999/25000000000000000000000000:ℝ) (566952332575732811/8000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_442
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1327).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_442 :
    (∫ x in (221/256:ℝ)..(443/512:ℝ), x^10*thetaFirstMode x) ≤ (28929629692861/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (221/256:ℝ) (443/512:ℝ)
    (411913/6250000000000:ℝ) (615647/10000000000000:ℝ) (566952332575732811/8000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_442 (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1327).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_443 :
    (13817932814637/500000000000000000000000:ℝ) ≤ ∫ x in (443/512:ℝ)..(111/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1344586981700192143839367/625000000000000000000000000000:ℝ)*(thetaPowerMass 11 (443/512:ℝ) (111/128:ℝ)-(115513472527065173117007/133503598919808937500160:ℝ)*thetaPowerMass 10 (443/512:ℝ) (111/128:ℝ)) ≤
      thetaFirstModeFirst (115513472527065173117007/133503598919808937500160:ℝ)*(thetaPowerMass 11 (443/512:ℝ) (111/128:ℝ)-(115513472527065173117007/133503598919808937500160:ℝ)*thetaPowerMass 10 (443/512:ℝ) (111/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0669.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (443/512:ℝ) (111/128:ℝ)
    (115513472527065173117007/133503598919808937500160:ℝ) (384619/6250000000000:ℝ) (-1344586981700192143839367/625000000000000000000000000000:ℝ) (13345164857540070351/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_443
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1331).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_443 :
    (∫ x in (443/512:ℝ)..(111/128:ℝ), x^10*thetaFirstMode x) ≤ (6909307926437/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (443/512:ℝ) (111/128:ℝ)
    (615647/10000000000000:ℝ) (2874687/50000000000000:ℝ) (13345164857540070351/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_443 (thetaFirstMode_refined_node_1327).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_444 :
    (3299167208101/125000000000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(445/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-23642058480249863763/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (111/128:ℝ) (445/512:ℝ)-(445/512:ℝ)*thetaPowerMass 10 (111/128:ℝ) (445/512:ℝ)) ≤
      thetaFirstModeFirst (445/512:ℝ)*(thetaPowerMass 11 (111/128:ℝ) (445/512:ℝ)-(445/512:ℝ)*thetaPowerMass 10 (111/128:ℝ) (445/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0671.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (111/128:ℝ) (445/512:ℝ)
    (445/512:ℝ) (1341927/25000000000000:ℝ) (-23642058480249863763/12500000000000000000000000:ℝ) (6280768722054132469/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_444
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1333).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_444 :
    (∫ x in (111/128:ℝ)..(445/512:ℝ), x^10*thetaFirstMode x) ≤ (6598518083607/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (111/128:ℝ) (445/512:ℝ)
    (2874687/50000000000000:ℝ) (5367739/100000000000000:ℝ) (6280768722054132469/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_444 (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1333).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_445 :
    (5039485780301/200000000000000000000000:ℝ) ≤ ∫ x in (445/512:ℝ)..(223/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1890641322490252181259421/1000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (445/512:ℝ) (223/256:ℝ)-(24058522909244262175605/27680444625863446871552:ℝ)*thetaPowerMass 10 (445/512:ℝ) (223/256:ℝ)) ≤
      thetaFirstModeFirst (24058522909244262175605/27680444625863446871552:ℝ)*(thetaPowerMass 11 (445/512:ℝ) (223/256:ℝ)-(24058522909244262175605/27680444625863446871552:ℝ)*thetaPowerMass 10 (445/512:ℝ) (223/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0672.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (445/512:ℝ) (223/256:ℝ)
    (24058522909244262175605/27680444625863446871552:ℝ) (1073099/20000000000000:ℝ) (-1890641322490252181259421/1000000000000000000000000000000:ℝ) (14775851413730711587/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_445
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1337).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_445 :
    (∫ x in (445/512:ℝ)..(223/256:ℝ), x^10*thetaFirstMode x) ≤ (25198700106911/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (445/512:ℝ) (223/256:ℝ)
    (5367739/100000000000000:ℝ) (5010071/100000000000000:ℝ) (14775851413730711587/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_445 (thetaFirstMode_refined_node_1333).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_446 :
    (1202449764049/50000000000000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(447/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-83017970264052112557/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (223/256:ℝ) (447/512:ℝ)-(447/512:ℝ)*thetaPowerMass 10 (223/256:ℝ) (447/512:ℝ)) ≤
      thetaFirstModeFirst (447/512:ℝ)*(thetaPowerMass 11 (223/256:ℝ) (447/512:ℝ)-(447/512:ℝ)*thetaPowerMass 10 (223/256:ℝ) (447/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0674.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (223/256:ℝ) (447/512:ℝ)
    (447/512:ℝ) (4674927/100000000000000:ℝ) (-83017970264052112557/50000000000000000000000000:ℝ) (27801147271290414531/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_446
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1339).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_446 :
    (∫ x in (223/256:ℝ)..(447/512:ℝ), x^10*thetaFirstMode x) ≤ (961987331529/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (223/256:ℝ) (447/512:ℝ)
    (5010071/100000000000000:ℝ) (934991/20000000000000:ℝ) (27801147271290414531/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_446 (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1339).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_447 :
    (11472213077287/500000000000000000000000:ℝ) ≤ ∫ x in (447/512:ℝ)..(7/8:ℝ), x^10*thetaFirstMode x := by
  have hd : (-41493055534829519713612419/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (447/512:ℝ) (7/8:ℝ)-(125246713502597024463543/143457408303917490588160:ℝ)*thetaPowerMass 10 (447/512:ℝ) (7/8:ℝ)) ≤
      thetaFirstModeFirst (125246713502597024463543/143457408303917490588160:ℝ)*(thetaPowerMass 11 (447/512:ℝ) (7/8:ℝ)-(125246713502597024463543/143457408303917490588160:ℝ)*thetaPowerMass 10 (447/512:ℝ) (7/8:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0675.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (447/512:ℝ) (7/8:ℝ)
    (125246713502597024463543/143457408303917490588160:ℝ) (4672993/100000000000000:ℝ) (-41493055534829519713612419/25000000000000000000000000000000:ℝ) (13073532968807063897/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_447
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1343).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_447 :
    (∫ x in (447/512:ℝ)..(7/8:ℝ), x^10*thetaFirstMode x) ≤ (4589122712077/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (447/512:ℝ) (7/8:ℝ)
    (934991/20000000000000:ℝ) (136283/3125000000000:ℝ) (13073532968807063897/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_447 (thetaFirstMode_refined_node_1339).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

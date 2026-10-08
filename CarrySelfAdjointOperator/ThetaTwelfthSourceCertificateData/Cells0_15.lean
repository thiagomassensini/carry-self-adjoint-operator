import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature15
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative22
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative23
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative24

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_480 :
    (7610029571409/1000000000000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(481/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-8201168928069159195281523/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (15/16:ℝ) (481/512:ℝ)-(15/16:ℝ)*thetaPowerMass 0 (15/16:ℝ) (481/512:ℝ)) ≤
      thetaFirstModeFirst (15/16:ℝ)*(thetaPowerMass 1 (15/16:ℝ) (481/512:ℝ)-(15/16:ℝ)*thetaPowerMass 0 (15/16:ℝ) (481/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0724.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (15/16:ℝ) (481/512:ℝ)
    (15/16:ℝ) (202639/50000000000000:ℝ) (-8201168928069159195281523/50000000000000000000000000000000:ℝ) (5873422074674114321/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_480
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1440).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_480 :
    (∫ x in (15/16:ℝ)..(481/512:ℝ), x^0*thetaFirstMode x) ≤ (7610620877747/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/16:ℝ) (481/512:ℝ)
    (405281/100000000000000:ℝ) (18721/5000000000000:ℝ) (5873422074674114321/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_480 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1441).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_481 :
    (1757363077153/250000000000000000000000:ℝ) ≤ ∫ x in (481/512:ℝ)..(241/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-475220539914251346587007/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (481/512:ℝ) (241/256:ℝ)-(242270625732500482869609/257881768625375876508160:ℝ)*thetaPowerMass 0 (481/512:ℝ) (241/256:ℝ)) ≤
      thetaFirstModeFirst (242270625732500482869609/257881768625375876508160:ℝ)*(thetaPowerMass 1 (481/512:ℝ) (241/256:ℝ)-(242270625732500482869609/257881768625375876508160:ℝ)*thetaPowerMass 0 (481/512:ℝ) (241/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0726.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (481/512:ℝ) (241/256:ℝ)
    (242270625732500482869609/257881768625375876508160:ℝ) (93563/25000000000000:ℝ) (-475220539914251346587007/3125000000000000000000000000000:ℝ) (2734347372851105041/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_481
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1445).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_481 :
    (∫ x in (481/512:ℝ)..(241/256:ℝ), x^0*thetaFirstMode x) ≤ (1406002558109/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (481/512:ℝ) (241/256:ℝ)
    (18721/5000000000000:ℝ) (345801/100000000000000:ℝ) (2734347372851105041/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_481 (thetaFirstMode_refined_node_1441).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_482 :
    (3245566696561/500000000000000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(483/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-7053106411687972662787101/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (241/256:ℝ) (483/512:ℝ)-(241/256:ℝ)*thetaPowerMass 0 (241/256:ℝ) (483/512:ℝ)) ≤
      thetaFirstModeFirst (241/256:ℝ)*(thetaPowerMass 1 (241/256:ℝ) (483/512:ℝ)-(241/256:ℝ)*thetaPowerMass 0 (241/256:ℝ) (483/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0727.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (241/256:ℝ) (483/512:ℝ)
    (241/256:ℝ) (172899/50000000000000:ℝ) (-7053106411687972662787101/50000000000000000000000000000000:ℝ) (5090231265906272769/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_482
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1446).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_482 :
    (∫ x in (241/256:ℝ)..(483/512:ℝ), x^0*thetaFirstMode x) ≤ (8114567527/1250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (241/256:ℝ) (483/512:ℝ)
    (345801/100000000000000:ℝ) (79817/25000000000000:ℝ) (5090231265906272769/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_482 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1447).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_483 :
    (74901726627/12500000000000000000000:ℝ) ≤ ∫ x in (483/512:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6534982617101774456742169/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (483/512:ℝ) (121/128:ℝ)-(251489040682132561926807/266585749541721770268160:ℝ)*thetaPowerMass 0 (483/512:ℝ) (121/128:ℝ)) ≤
      thetaFirstModeFirst (251489040682132561926807/266585749541721770268160:ℝ)*(thetaPowerMass 1 (483/512:ℝ) (121/128:ℝ)-(251489040682132561926807/266585749541721770268160:ℝ)*thetaPowerMass 0 (483/512:ℝ) (121/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0729.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (483/512:ℝ) (121/128:ℝ)
    (251489040682132561926807/266585749541721770268160:ℝ) (79781/25000000000000:ℝ) (-6534982617101774456742169/50000000000000000000000000000000:ℝ) (4736460730020299177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_483
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1451).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_483 :
    (∫ x in (483/512:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x) ≤ (5992625624383/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (483/512:ℝ) (121/128:ℝ)
    (79817/25000000000000:ℝ) (147339/50000000000000:ℝ) (4736460730020299177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_483 (thetaFirstMode_refined_node_1447).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_484 :
    (552974407613/100000000000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(485/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-94657772384040863625399/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (121/128:ℝ) (485/512:ℝ)-(121/128:ℝ)*thetaPowerMass 0 (121/128:ℝ) (485/512:ℝ)) ≤
      thetaFirstModeFirst (121/128:ℝ)*(thetaPowerMass 1 (121/128:ℝ) (485/512:ℝ)-(121/128:ℝ)*thetaPowerMass 0 (121/128:ℝ) (485/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0730.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (121/128:ℝ) (485/512:ℝ)
    (121/128:ℝ) (11787/4000000000000:ℝ) (-94657772384040863625399/781250000000000000000000000000:ℝ) (2202939523384069869/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_484
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1452).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_484 :
    (∫ x in (121/128:ℝ)..(485/512:ℝ), x^0*thetaFirstMode x) ≤ (2765106844503/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (121/128:ℝ) (485/512:ℝ)
    (147339/50000000000000:ℝ) (33987/12500000000000:ℝ) (2202939523384069869/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_484 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1453).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_485 :
    (5101437943879/1000000000000000000000000:ℝ) ≤ ∫ x in (485/512:ℝ)..(243/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-224380198710388463775431/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (485/512:ℝ) (243/256:ℝ)-(52203587185640050827165/55109141525919324349952:ℝ)*thetaPowerMass 0 (485/512:ℝ) (243/256:ℝ)) ≤
      thetaFirstModeFirst (52203587185640050827165/55109141525919324349952:ℝ)*(thetaPowerMass 1 (485/512:ℝ) (243/256:ℝ)-(52203587185640050827165/55109141525919324349952:ℝ)*thetaPowerMass 0 (485/512:ℝ) (243/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0732.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (485/512:ℝ) (243/256:ℝ)
    (52203587185640050827165/55109141525919324349952:ℝ) (271773/100000000000000:ℝ) (-224380198710388463775431/2000000000000000000000000000000:ℝ) (4097052885021176591/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_485
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1457).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_485 :
    (∫ x in (485/512:ℝ)..(243/256:ℝ), x^0*thetaFirstMode x) ≤ (159433140989/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (485/512:ℝ) (243/256:ℝ)
    (33987/12500000000000:ℝ) (50159/20000000000000:ℝ) (4097052885021176591/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_485 (thetaFirstMode_refined_node_1453).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_486 :
    (4704766032829/1000000000000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(487/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1039373003619910424765159/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (243/256:ℝ) (487/512:ℝ)-(243/256:ℝ)*thetaPowerMass 0 (243/256:ℝ) (487/512:ℝ)) ≤
      thetaFirstModeFirst (243/256:ℝ)*(thetaPowerMass 1 (243/256:ℝ) (487/512:ℝ)-(243/256:ℝ)*thetaPowerMass 0 (243/256:ℝ) (487/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0733.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (243/256:ℝ) (487/512:ℝ)
    (243/256:ℝ) (31349/12500000000000:ℝ) (-1039373003619910424765159/10000000000000000000000000000000:ℝ) (761731332756242597/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_486
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1458).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_486 :
    (∫ x in (243/256:ℝ)..(487/512:ℝ), x^0*thetaFirstMode x) ≤ (4705184102839/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (243/256:ℝ) (487/512:ℝ)
    (50159/20000000000000:ℝ) (115629/50000000000000:ℝ) (761731332756242597/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_486 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1459).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_487 :
    (4337572096073/1000000000000000000000000:ℝ) ≤ ∫ x in (487/512:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-240448542877429540890287/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (487/512:ℝ) (61/64:ℝ)-(270866423231695777103343/284768068631243160732160:ℝ)*thetaPowerMass 0 (487/512:ℝ) (61/64:ℝ)) ≤
      thetaFirstModeFirst (270866423231695777103343/284768068631243160732160:ℝ)*(thetaPowerMass 1 (487/512:ℝ) (61/64:ℝ)-(270866423231695777103343/284768068631243160732160:ℝ)*thetaPowerMass 0 (487/512:ℝ) (61/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0735.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (487/512:ℝ) (61/64:ℝ)
    (270866423231695777103343/284768068631243160732160:ℝ) (14447/6250000000000:ℝ) (-240448542877429540890287/2500000000000000000000000000000:ℝ) (3539411636629536411/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_487
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1463).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_487 :
    (∫ x in (487/512:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x) ≤ (1084489673507/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (487/512:ℝ) (61/64:ℝ)
    (115629/50000000000000:ℝ) (106587/50000000000000:ℝ) (3539411636629536411/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_487 (thetaFirstMode_refined_node_1459).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_488 :
    (999433760471/250000000000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(489/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-445236229421342117894889/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (61/64:ℝ) (489/512:ℝ)-(61/64:ℝ)*thetaPowerMass 0 (61/64:ℝ) (489/512:ℝ)) ≤
      thetaFirstModeFirst (61/64:ℝ)*(thetaPowerMass 1 (61/64:ℝ) (489/512:ℝ)-(61/64:ℝ)*thetaPowerMass 0 (61/64:ℝ) (489/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0736.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (61/64:ℝ) (489/512:ℝ)
    (61/64:ℝ) (213171/100000000000000:ℝ) (-445236229421342117894889/5000000000000000000000000000000:ℝ) (822034761104539841/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_488
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1464).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_488 :
    (∫ x in (61/64:ℝ)..(489/512:ℝ), x^0*thetaFirstMode x) ≤ (1999052469481/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/64:ℝ) (489/512:ℝ)
    (106587/50000000000000:ℝ) (196441/100000000000000:ℝ) (822034761104539841/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_488 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1465).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_489 :
    (3683358575357/1000000000000000000000000:ℝ) ≤ ∫ x in (489/512:ℝ)..(245/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-51467124688020112266333/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (489/512:ℝ) (245/256:ℝ)-(281043842605185699355041/294259392150867570741760:ℝ)*thetaPowerMass 0 (489/512:ℝ) (245/256:ℝ)) ≤
      thetaFirstModeFirst (281043842605185699355041/294259392150867570741760:ℝ)*(thetaPowerMass 1 (489/512:ℝ) (245/256:ℝ)-(281043842605185699355041/294259392150867570741760:ℝ)*thetaPowerMass 0 (489/512:ℝ) (245/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0738.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (489/512:ℝ) (245/256:ℝ)
    (281043842605185699355041/294259392150867570741760:ℝ) (196351/100000000000000:ℝ) (-51467124688020112266333/625000000000000000000000000000:ℝ) (610742909844803541/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_489
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1469).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_489 :
    (∫ x in (489/512:ℝ)..(245/256:ℝ), x^0*thetaFirstMode x) ≤ (736736035269/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (489/512:ℝ) (245/256:ℝ)
    (196441/100000000000000:ℝ) (90481/50000000000000:ℝ) (610742909844803541/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_489 (thetaFirstMode_refined_node_1465).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_490 :
    (424071445949/125000000000000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(491/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1904789688877763790284471/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (245/256:ℝ) (491/512:ℝ)-(245/256:ℝ)*thetaPowerMass 0 (245/256:ℝ) (491/512:ℝ)) ≤
      thetaFirstModeFirst (245/256:ℝ)*(thetaPowerMass 1 (245/256:ℝ) (491/512:ℝ)-(245/256:ℝ)*thetaPowerMass 0 (245/256:ℝ) (491/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0739.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (245/256:ℝ) (491/512:ℝ)
    (245/256:ℝ) (1131/625000000000:ℝ) (-1904789688877763790284471/25000000000000000000000000000000:ℝ) (177191960167171811/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_490
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1470).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_490 :
    (∫ x in (245/256:ℝ)..(491/512:ℝ), x^0*thetaFirstMode x) ≤ (1696439213951/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (245/256:ℝ) (491/512:ℝ)
    (90481/50000000000000:ℝ) (166649/100000000000000:ℝ) (177191960167171811/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_490 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1471).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_491 :
    (1561874607291/500000000000000000000000:ℝ) ≤ ∫ x in (491/512:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-70413405472474475513691/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (491/512:ℝ) (123/128:ℝ)-(291559767057868215806559/304026373876319976271360:ℝ)*thetaPowerMass 0 (491/512:ℝ) (123/128:ℝ)) ≤
      thetaFirstModeFirst (291559767057868215806559/304026373876319976271360:ℝ)*(thetaPowerMass 1 (491/512:ℝ) (123/128:ℝ)-(291559767057868215806559/304026373876319976271360:ℝ)*thetaPowerMass 0 (491/512:ℝ) (123/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0741.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (491/512:ℝ) (123/128:ℝ)
    (291559767057868215806559/304026373876319976271360:ℝ) (166573/100000000000000:ℝ) (-70413405472474475513691/1000000000000000000000000000000:ℝ) (2631237758612373687/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_491
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1475).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_491 :
    (∫ x in (491/512:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x) ≤ (624806075017/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (491/512:ℝ) (123/128:ℝ)
    (166649/100000000000000:ℝ) (153419/100000000000000:ℝ) (2631237758612373687/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_491 (thetaFirstMode_refined_node_1471).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_492 :
    (718818571249/250000000000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(493/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-813845291719680726809457/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (123/128:ℝ) (493/512:ℝ)-(123/128:ℝ)*thetaPowerMass 0 (123/128:ℝ) (493/512:ℝ)) ≤
      thetaFirstModeFirst (123/128:ℝ)*(thetaPowerMass 1 (123/128:ℝ) (493/512:ℝ)-(123/128:ℝ)*thetaPowerMass 0 (123/128:ℝ) (493/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0742.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (123/128:ℝ) (493/512:ℝ)
    (123/128:ℝ) (153417/100000000000000:ℝ) (-813845291719680726809457/12500000000000000000000000000000:ℝ) (2441238021041889237/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_492
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1476).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_492 :
    (∫ x in (123/128:ℝ)..(493/512:ℝ), x^0*thetaFirstMode x) ≤ (2875544826823/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (123/128:ℝ) (493/512:ℝ)
    (153419/100000000000000:ℝ) (17649/12500000000000:ℝ) (2441238021041889237/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_492 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1477).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_493 :
    (661421287813/250000000000000000000000:ℝ) ≤ ∫ x in (493/512:ℝ)..(247/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-375812822403357945730059/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (493/512:ℝ) (247/256:ℝ)-(302424007419219829279257/314075847828315644700160:ℝ)*thetaPowerMass 0 (493/512:ℝ) (247/256:ℝ)) ≤
      thetaFirstModeFirst (302424007419219829279257/314075847828315644700160:ℝ)*(thetaPowerMass 1 (493/512:ℝ) (247/256:ℝ)-(302424007419219829279257/314075847828315644700160:ℝ)*thetaPowerMass 0 (493/512:ℝ) (247/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0744.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (493/512:ℝ) (247/256:ℝ)
    (302424007419219829279257/314075847828315644700160:ℝ) (70563/50000000000000:ℝ) (-375812822403357945730059/6250000000000000000000000000000:ℝ) (2264215051628209499/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_493
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1481).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_493 :
    (∫ x in (493/512:ℝ)..(247/256:ℝ), x^0*thetaFirstMode x) ≤ (1322973852949/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (493/512:ℝ) (247/256:ℝ)
    (17649/12500000000000:ℝ) (129897/100000000000000:ℝ) (2264215051628209499/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_493 (thetaFirstMode_refined_node_1477).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_494 :
    (121682042681/50000000000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(495/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1389071394193664609057079/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (247/256:ℝ) (495/512:ℝ)-(247/256:ℝ)*thetaPowerMass 0 (247/256:ℝ) (495/512:ℝ)) ≤
      thetaFirstModeFirst (247/256:ℝ)*(thetaPowerMass 1 (247/256:ℝ) (495/512:ℝ)-(247/256:ℝ)*thetaPowerMass 0 (247/256:ℝ) (495/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0745.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (247/256:ℝ) (495/512:ℝ)
    (247/256:ℝ) (25979/20000000000000:ℝ) (-1389071394193664609057079/25000000000000000000000000000000:ℝ) (2099330505113338621/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_494
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1482).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_494 :
    (∫ x in (247/256:ℝ)..(495/512:ℝ), x^0*thetaFirstMode x) ≤ (608470527737/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (247/256:ℝ) (495/512:ℝ)
    (129897/100000000000000:ℝ) (59733/50000000000000:ℝ) (2099330505113338621/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_494 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1483).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_495 :
    (223784651629/100000000000000000000000:ℝ) ≤ ∫ x in (495/512:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-80127009761065797301587/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (495/512:ℝ) (31/32:ℝ)-(62729323448440729602555/64882957727484714455552:ℝ)*thetaPowerMass 0 (495/512:ℝ) (31/32:ℝ)) ≤
      thetaFirstModeFirst (62729323448440729602555/64882957727484714455552:ℝ)*(thetaPowerMass 1 (495/512:ℝ) (31/32:ℝ)-(62729323448440729602555/64882957727484714455552:ℝ)*thetaPowerMass 0 (495/512:ℝ) (31/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0747.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (495/512:ℝ) (31/32:ℝ)
    (62729323448440729602555/64882957727484714455552:ℝ) (11941/10000000000000:ℝ) (-80127009761065797301587/1562500000000000000000000000000:ℝ) (1945819361608664979/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_495
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1487).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_495 :
    (∫ x in (495/512:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x) ≤ (447613844017/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (495/512:ℝ) (31/32:ℝ)
    (59733/50000000000000:ℝ) (27459/25000000000000:ℝ) (1945819361608664979/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_495 (thetaFirstMode_refined_node_1483).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_496 :
    (41142636619/20000000000000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(497/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-295966525198217195480013/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (31/32:ℝ) (497/512:ℝ)-(31/32:ℝ)*thetaPowerMass 0 (31/32:ℝ) (497/512:ℝ)) ≤
      thetaFirstModeFirst (31/32:ℝ)*(thetaPowerMass 1 (31/32:ℝ) (497/512:ℝ)-(31/32:ℝ)*thetaPowerMass 0 (31/32:ℝ) (497/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0748.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (31/32:ℝ) (497/512:ℝ)
    (31/32:ℝ) (21967/20000000000000:ℝ) (-295966525198217195480013/6250000000000000000000000000000:ℝ) (225365264048970199/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_496
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1488).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_496 :
    (∫ x in (31/32:ℝ)..(497/512:ℝ), x^0*thetaFirstMode x) ≤ (8229311457/4000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/32:ℝ) (497/512:ℝ)
    (27459/25000000000000:ℝ) (100949/100000000000000:ℝ) (225365264048970199/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_496 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1489).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_497 :
    (472592401563/250000000000000000000000:ℝ) ≤ ∫ x in (497/512:ℝ)..(249/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-27298046771651250923247/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (497/512:ℝ) (249/256:ℝ)-(325237897787019494300793/335050313849050052508160:ℝ)*thetaPowerMass 0 (497/512:ℝ) (249/256:ℝ)) ≤
      thetaFirstModeFirst (325237897787019494300793/335050313849050052508160:ℝ)*(thetaPowerMass 1 (497/512:ℝ) (249/256:ℝ)-(325237897787019494300793/335050313849050052508160:ℝ)*thetaPowerMass 0 (497/512:ℝ) (249/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0750.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (497/512:ℝ) (249/256:ℝ)
    (325237897787019494300793/335050313849050052508160:ℝ) (50451/50000000000000:ℝ) (-27298046771651250923247/625000000000000000000000000000:ℝ) (1669957593656032913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_497
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1493).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_497 :
    (∫ x in (497/512:ℝ)..(249/256:ℝ), x^0*thetaFirstMode x) ≤ (945277475369/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (497/512:ℝ) (249/256:ℝ)
    (100949/100000000000000:ℝ) (371/400000000000:ℝ) (1669957593656032913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_497 (thetaFirstMode_refined_node_1489).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_498 :
    (347309488507/200000000000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(499/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-806109242827375992953/20000000000000000000000000000:ℝ)*(thetaPowerMass 1 (249/256:ℝ) (499/512:ℝ)-(249/256:ℝ)*thetaPowerMass 0 (249/256:ℝ) (499/512:ℝ)) ≤
      thetaFirstModeFirst (249/256:ℝ)*(thetaPowerMass 1 (249/256:ℝ) (499/512:ℝ)-(249/256:ℝ)*thetaPowerMass 0 (249/256:ℝ) (499/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0751.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (249/256:ℝ) (499/512:ℝ)
    (249/256:ℝ) (92749/100000000000000:ℝ) (-806109242827375992953/20000000000000000000000000000:ℝ) (1546272297162852323/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_498
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1494).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_498 :
    (∫ x in (249/256:ℝ)..(499/512:ℝ), x^0*thetaFirstMode x) ≤ (868362747339/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (249/256:ℝ) (499/512:ℝ)
    (371/400000000000:ℝ) (85189/100000000000000:ℝ) (1546272297162852323/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_498 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1495).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_499 :
    (797347504291/500000000000000000000000:ℝ) ≤ ∫ x in (499/512:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4643759990130725618479/125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (499/512:ℝ) (125/128:ℝ)-(337208403086384037209991/345989686256645754242560:ℝ)*thetaPowerMass 0 (499/512:ℝ) (125/128:ℝ)) ≤
      thetaFirstModeFirst (337208403086384037209991/345989686256645754242560:ℝ)*(thetaPowerMass 1 (499/512:ℝ) (125/128:ℝ)-(337208403086384037209991/345989686256645754242560:ℝ)*thetaPowerMass 0 (499/512:ℝ) (125/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0753.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (499/512:ℝ) (125/128:ℝ)
    (337208403086384037209991/345989686256645754242560:ℝ) (21287/25000000000000:ℝ) (-4643759990130725618479/125000000000000000000000000000:ℝ) (1431278615296834699/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_499
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1499).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_499 :
    (∫ x in (499/512:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x) ≤ (1594873064027/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (499/512:ℝ) (125/128:ℝ)
    (85189/100000000000000:ℝ) (78217/100000000000000:ℝ) (1431278615296834699/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_499 (thetaFirstMode_refined_node_1495).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_500 :
    (1463955720797/1000000000000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(501/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-85649130923928930152121/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (125/128:ℝ) (501/512:ℝ)-(125/128:ℝ)*thetaPowerMass 0 (125/128:ℝ) (501/512:ℝ)) ≤
      thetaFirstModeFirst (125/128:ℝ)*(thetaPowerMass 1 (125/128:ℝ) (501/512:ℝ)-(125/128:ℝ)*thetaPowerMass 0 (125/128:ℝ) (501/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0754.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (125/128:ℝ) (501/512:ℝ)
    (125/128:ℝ) (9777/12500000000000:ℝ) (-85649130923928930152121/2500000000000000000000000000000:ℝ) (165548028491786147/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_500
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1500).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_500 :
    (∫ x in (125/128:ℝ)..(501/512:ℝ), x^0*thetaFirstMode x) ≤ (1464109354673/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (125/128:ℝ) (501/512:ℝ)
    (78217/100000000000000:ℝ) (4487/6250000000000:ℝ) (165548028491786147/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_500 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1501).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_501 :
    (41983523721/31250000000000000000000:ℝ) ≤ ∫ x in (501/512:ℝ)..(251/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-788902089583851834247571/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (501/512:ℝ) (251/256:ℝ)-(349568945093337212835009/357240316263365765762560:ℝ)*thetaPowerMass 0 (501/512:ℝ) (251/256:ℝ)) ≤
      thetaFirstModeFirst (349568945093337212835009/357240316263365765762560:ℝ)*(thetaPowerMass 1 (501/512:ℝ) (251/256:ℝ)-(349568945093337212835009/357240316263365765762560:ℝ)*thetaPowerMass 0 (501/512:ℝ) (251/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0756.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (501/512:ℝ) (251/256:ℝ)
    (349568945093337212835009/357240316263365765762560:ℝ) (35879/50000000000000:ℝ) (-788902089583851834247571/25000000000000000000000000000000:ℝ) (612524077747350281/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_501
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1505).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_501 :
    (∫ x in (501/512:ℝ)..(251/256:ℝ), x^0*thetaFirstMode x) ≤ (1343614389999/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (501/512:ℝ) (251/256:ℝ)
    (4487/6250000000000:ℝ) (4117/6250000000000:ℝ) (612524077747350281/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_501 (thetaFirstMode_refined_node_1501).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_502 :
    (1232481397079/1000000000000000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(503/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-90879132539126594960337/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (251/256:ℝ) (503/512:ℝ)-(251/256:ℝ)*thetaPowerMass 0 (251/256:ℝ) (503/512:ℝ)) ≤
      thetaFirstModeFirst (251/256:ℝ)*(thetaPowerMass 1 (251/256:ℝ) (503/512:ℝ)-(251/256:ℝ)*thetaPowerMass 0 (251/256:ℝ) (503/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0757.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (251/256:ℝ) (503/512:ℝ)
    (251/256:ℝ) (65871/100000000000000:ℝ) (-90879132539126594960337/3125000000000000000000000000000:ℝ) (70798955969898033/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_502
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1506).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_502 :
    (∫ x in (251/256:ℝ)..(503/512:ℝ), x^0*thetaFirstMode x) ≤ (38519280877/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (251/256:ℝ) (503/512:ℝ)
    (4117/6250000000000:ℝ) (3021/5000000000000:ℝ) (70798955969898033/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_502 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1507).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_503 :
    (1130276654053/1000000000000000000000000:ℝ) ≤ ∫ x in (503/512:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-167300586946877247705661/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (503/512:ℝ) (63/64:ℝ)-(362330598912579278694207/368809764272412990108160:ℝ)*thetaPowerMass 0 (503/512:ℝ) (63/64:ℝ)) ≤
      thetaFirstModeFirst (362330598912579278694207/368809764272412990108160:ℝ)*(thetaPowerMass 1 (503/512:ℝ) (63/64:ℝ)-(362330598912579278694207/368809764272412990108160:ℝ)*thetaPowerMass 0 (503/512:ℝ) (63/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0759.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (503/512:ℝ) (63/64:ℝ)
    (362330598912579278694207/368809764272412990108160:ℝ) (60391/100000000000000:ℝ) (-167300586946877247705661/6250000000000000000000000000000:ℝ) (209420464077006753/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_503
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1511).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_503 :
    (∫ x in (503/512:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x) ≤ (226080912163/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (503/512:ℝ) (63/64:ℝ)
    (3021/5000000000000:ℝ) (277/500000000000:ℝ) (209420464077006753/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_503 (thetaFirstMode_refined_node_1507).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_504 :
    (1036193007867/1000000000000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(505/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3081514957510231482467/125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (63/64:ℝ) (505/512:ℝ)-(63/64:ℝ)*thetaPowerMass 0 (63/64:ℝ) (505/512:ℝ)) ≤
      thetaFirstModeFirst (63/64:ℝ)*(thetaPowerMass 1 (63/64:ℝ) (505/512:ℝ)-(63/64:ℝ)*thetaPowerMass 0 (63/64:ℝ) (505/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0760.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (63/64:ℝ) (505/512:ℝ)
    (63/64:ℝ) (55399/100000000000000:ℝ) (-3081514957510231482467/125000000000000000000000000000:ℝ) (967556150380563339/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_504
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1512).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_504 :
    (∫ x in (63/64:ℝ)..(505/512:ℝ), x^0*thetaFirstMode x) ≤ (1036313324577/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/64:ℝ) (505/512:ℝ)
    (277/500000000000:ℝ) (2539/5000000000000:ℝ) (967556150380563339/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_504 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1513).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_505 :
    (237401919413/250000000000000000000000:ℝ) ≤ ∫ x in (505/512:ℝ)..(253/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-283443465793226403186967/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (505/512:ℝ) (253/256:ℝ)-(75100941623270192936445/76141148621259241175552:ℝ)*thetaPowerMass 0 (505/512:ℝ) (253/256:ℝ)) ≤
      thetaFirstModeFirst (75100941623270192936445/76141148621259241175552:ℝ)*(thetaPowerMass 1 (505/512:ℝ) (253/256:ℝ)-(75100941623270192936445/76141148621259241175552:ℝ)*thetaPowerMass 0 (505/512:ℝ) (253/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0762.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (505/512:ℝ) (253/256:ℝ)
    (75100941623270192936445/76141148621259241175552:ℝ) (10151/20000000000000:ℝ) (-283443465793226403186967/12500000000000000000000000000000:ℝ) (223443573900565599/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_505
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1517).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_505 :
    (∫ x in (505/512:ℝ)..(253/256:ℝ), x^0*thetaFirstMode x) ≤ (949728275007/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (505/512:ℝ) (253/256:ℝ)
    (2539/5000000000000:ℝ) (46529/100000000000000:ℝ) (223443573900565599/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_505 (thetaFirstMode_refined_node_1513).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_506 :
    (34798824651/40000000000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(507/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1043443949409156743993629/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (253/256:ℝ) (507/512:ℝ)-(253/256:ℝ)*thetaPowerMass 0 (253/256:ℝ) (507/512:ℝ)) ≤
      thetaFirstModeFirst (253/256:ℝ)*(thetaPowerMass 1 (253/256:ℝ) (507/512:ℝ)-(253/256:ℝ)*thetaPowerMass 0 (253/256:ℝ) (507/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0763.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (253/256:ℝ) (507/512:ℝ)
    (253/256:ℝ) (727/1562500000000:ℝ) (-1043443949409156743993629/50000000000000000000000000000000:ℝ) (825313465073590469/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_506
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1518).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_506 :
    (∫ x in (253/256:ℝ)..(507/512:ℝ), x^0*thetaFirstMode x) ≤ (43503675773/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (253/256:ℝ) (507/512:ℝ)
    (46529/100000000000000:ℝ) (42619/100000000000000:ℝ) (825313465073590469/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_506 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1519).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_507 :
    (796721013853/1000000000000000000000000:ℝ) ≤ ∫ x in (507/512:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-239777914527258129755283/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (507/512:ℝ) (127/128:ℝ)-(389102890145877331465743/392936120455235036700160:ℝ)*thetaPowerMass 0 (507/512:ℝ) (127/128:ℝ)) ≤
      thetaFirstModeFirst (389102890145877331465743/392936120455235036700160:ℝ)*(thetaPowerMass 1 (507/512:ℝ) (127/128:ℝ)-(389102890145877331465743/392936120455235036700160:ℝ)*thetaPowerMass 0 (507/512:ℝ) (127/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0765.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (507/512:ℝ) (127/128:ℝ)
    (389102890145877331465743/392936120455235036700160:ℝ) (21299/50000000000000:ℝ) (-239777914527258129755283/12500000000000000000000000000000:ℝ) (152366120075123307/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_507
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1523).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_507 :
    (∫ x in (507/512:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x) ≤ (159364383037/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (507/512:ℝ) (127/128:ℝ)
    (42619/100000000000000:ℝ) (2439/6250000000000:ℝ) (152366120075123307/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_507 (thetaFirstMode_refined_node_1519).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_508 :
    (29175689893/40000000000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(509/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-55129976500948996224537/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (127/128:ℝ) (509/512:ℝ)-(127/128:ℝ)*thetaPowerMass 0 (127/128:ℝ) (509/512:ℝ)) ≤
      thetaFirstModeFirst (127/128:ℝ)*(thetaPowerMass 1 (127/128:ℝ) (509/512:ℝ)-(127/128:ℝ)*thetaPowerMass 0 (127/128:ℝ) (509/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0766.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (127/128:ℝ) (509/512:ℝ)
    (127/128:ℝ) (39023/100000000000000:ℝ) (-55129976500948996224537/3125000000000000000000000000000:ℝ) (702988870739379477/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_508
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1524).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_508 :
    (∫ x in (127/128:ℝ)..(509/512:ℝ), x^0*thetaFirstMode x) ≤ (45592837629/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (127/128:ℝ) (509/512:ℝ)
    (2439/6250000000000:ℝ) (893/2500000000000:ℝ) (702988870739379477/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_508 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1525).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_509 :
    (667513597207/1000000000000000000000000:ℝ) ≤ ∫ x in (509/512:ℝ)..(255/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-810223604736024861834831/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (509/512:ℝ) (255/256:ℝ)-(403137041799404128338441/405508921354945001551360:ℝ)*thetaPowerMass 0 (509/512:ℝ) (255/256:ℝ)) ≤
      thetaFirstModeFirst (403137041799404128338441/405508921354945001551360:ℝ)*(thetaPowerMass 1 (509/512:ℝ) (255/256:ℝ)-(403137041799404128338441/405508921354945001551360:ℝ)*thetaPowerMass 0 (509/512:ℝ) (255/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0768.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (509/512:ℝ) (255/256:ℝ)
    (403137041799404128338441/405508921354945001551360:ℝ) (17851/50000000000000:ℝ) (-810223604736024861834831/50000000000000000000000000000000:ℝ) (324229093938615553/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_509
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1529).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_509 :
    (∫ x in (509/512:ℝ)..(255/256:ℝ), x^0*thetaFirstMode x) ≤ (166901299167/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (509/512:ℝ) (255/256:ℝ)
    (893/2500000000000:ℝ) (8171/25000000000000:ℝ) (324229093938615553/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_509 (thetaFirstMode_refined_node_1525).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_510 :
    (610676918717/1000000000000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(511/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-186157921755989475768913/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (255/256:ℝ) (511/512:ℝ)-(255/256:ℝ)*thetaPowerMass 0 (255/256:ℝ) (511/512:ℝ)) ≤
      thetaFirstModeFirst (255/256:ℝ)*(thetaPowerMass 1 (255/256:ℝ) (511/512:ℝ)-(255/256:ℝ)*thetaPowerMass 0 (255/256:ℝ) (511/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0769.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (255/256:ℝ) (511/512:ℝ)
    (255/256:ℝ) (32683/100000000000000:ℝ) (-186157921755989475768913/12500000000000000000000000000000:ℝ) (597955739038740007/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_510
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1530).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_510 :
    (∫ x in (255/256:ℝ)..(511/512:ℝ), x^0*thetaFirstMode x) ≤ (122152310543/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (255/256:ℝ) (511/512:ℝ)
    (8171/25000000000000:ℝ) (3737/12500000000000:ℝ) (597955739038740007/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_510 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1531).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_511 :
    (27924282483/50000000000000000000000:ℝ) ≤ ∫ x in (511/512:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x := by
  have hd : (-170875568653144961453789/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (511/512:ℝ) (1/1:ℝ)-(417619344807863656339959/418432330694036747061760:ℝ)*thetaPowerMass 0 (511/512:ℝ) (1/1:ℝ)) ≤
      thetaFirstModeFirst (417619344807863656339959/418432330694036747061760:ℝ)*(thetaPowerMass 1 (511/512:ℝ) (1/1:ℝ)-(417619344807863656339959/418432330694036747061760:ℝ)*thetaPowerMass 0 (511/512:ℝ) (1/1:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0771.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (511/512:ℝ) (1/1:ℝ)
    (417619344807863656339959/418432330694036747061760:ℝ) (29881/100000000000000:ℝ) (-170875568653144961453789/12500000000000000000000000000000:ℝ) (275593830843204751/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_511
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1535).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_511 :
    (∫ x in (511/512:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x) ≤ (558564027659/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (511/512:ℝ) (1/1:ℝ)
    (3737/12500000000000:ℝ) (3417/12500000000000:ℝ) (275593830843204751/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_511 (thetaFirstMode_refined_node_1531).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator

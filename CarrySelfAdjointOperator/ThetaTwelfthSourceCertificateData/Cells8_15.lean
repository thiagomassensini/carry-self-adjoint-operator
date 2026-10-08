import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature15
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative22
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative23
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative24

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_8_480 :
    (2289368327073/500000000000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(481/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-3803315184435321557/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (15/16:ℝ) (481/512:ℝ)-(481/512:ℝ)*thetaPowerMass 8 (15/16:ℝ) (481/512:ℝ)) ≤
      thetaFirstModeFirst (481/512:ℝ)*(thetaPowerMass 9 (15/16:ℝ) (481/512:ℝ)-(481/512:ℝ)*thetaPowerMass 8 (15/16:ℝ) (481/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0725.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (15/16:ℝ) (481/512:ℝ)
    (481/512:ℝ) (374417/100000000000000:ℝ) (-3803315184435321557/25000000000000000000000000:ℝ) (5873422074674114321/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_480
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1441).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_480 :
    (∫ x in (15/16:ℝ)..(481/512:ℝ), x^8*thetaFirstMode x) ≤ (1144733020553/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/16:ℝ) (481/512:ℝ)
    (405281/100000000000000:ℝ) (18721/5000000000000:ℝ) (5873422074674114321/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_480 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1441).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_481 :
    (2150099741583/500000000000000000000000:ℝ) ≤ ∫ x in (481/512:ℝ)..(241/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-475220539914251346587007/3125000000000000000000000000000:ℝ)*(thetaPowerMass 9 (481/512:ℝ) (241/256:ℝ)-(242270625732500482869609/257881768625375876508160:ℝ)*thetaPowerMass 8 (481/512:ℝ) (241/256:ℝ)) ≤
      thetaFirstModeFirst (242270625732500482869609/257881768625375876508160:ℝ)*(thetaPowerMass 9 (481/512:ℝ) (241/256:ℝ)-(242270625732500482869609/257881768625375876508160:ℝ)*thetaPowerMass 8 (481/512:ℝ) (241/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0726.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (481/512:ℝ) (241/256:ℝ)
    (242270625732500482869609/257881768625375876508160:ℝ) (93563/25000000000000:ℝ) (-475220539914251346587007/3125000000000000000000000000000:ℝ) (2734347372851105041/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_481
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1445).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_481 :
    (∫ x in (481/512:ℝ)..(241/256:ℝ), x^8*thetaFirstMode x) ≤ (2150271615247/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (481/512:ℝ) (241/256:ℝ)
    (18721/5000000000000:ℝ) (345801/100000000000000:ℝ) (2734347372851105041/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_481 (thetaFirstMode_refined_node_1441).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_482 :
    (4037484520987/1000000000000000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(483/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-653766371643753437/5000000000000000000000000:ℝ)*(thetaPowerMass 9 (241/256:ℝ) (483/512:ℝ)-(483/512:ℝ)*thetaPowerMass 8 (241/256:ℝ) (483/512:ℝ)) ≤
      thetaFirstModeFirst (483/512:ℝ)*(thetaPowerMass 9 (241/256:ℝ) (483/512:ℝ)-(483/512:ℝ)*thetaPowerMass 8 (241/256:ℝ) (483/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0728.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (241/256:ℝ) (483/512:ℝ)
    (483/512:ℝ) (63853/20000000000000:ℝ) (-653766371643753437/5000000000000000000000000:ℝ) (5090231265906272769/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_482
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1447).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_482 :
    (∫ x in (241/256:ℝ)..(483/512:ℝ), x^8*thetaFirstMode x) ≤ (4037668578923/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (241/256:ℝ) (483/512:ℝ)
    (345801/100000000000000:ℝ) (79817/25000000000000:ℝ) (5090231265906272769/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_482 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1447).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_483 :
    (947305843287/250000000000000000000000:ℝ) ≤ ∫ x in (483/512:ℝ)..(121/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-6534982617101774456742169/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (483/512:ℝ) (121/128:ℝ)-(251489040682132561926807/266585749541721770268160:ℝ)*thetaPowerMass 8 (483/512:ℝ) (121/128:ℝ)) ≤
      thetaFirstModeFirst (251489040682132561926807/266585749541721770268160:ℝ)*(thetaPowerMass 9 (483/512:ℝ) (121/128:ℝ)-(251489040682132561926807/266585749541721770268160:ℝ)*thetaPowerMass 8 (483/512:ℝ) (121/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0729.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (483/512:ℝ) (121/128:ℝ)
    (251489040682132561926807/266585749541721770268160:ℝ) (79781/25000000000000:ℝ) (-6534982617101774456742169/50000000000000000000000000000000:ℝ) (4736460730020299177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_483
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1451).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_483 :
    (∫ x in (483/512:ℝ)..(121/128:ℝ), x^8*thetaFirstMode x) ≤ (757906485737/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (483/512:ℝ) (121/128:ℝ)
    (79817/25000000000000:ℝ) (147339/50000000000000:ℝ) (4736460730020299177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_483 (thetaFirstMode_refined_node_1447).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_484 :
    (3555236025151/1000000000000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(485/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-2805908361233360907/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (121/128:ℝ) (485/512:ℝ)-(485/512:ℝ)*thetaPowerMass 8 (121/128:ℝ) (485/512:ℝ)) ≤
      thetaFirstModeFirst (485/512:ℝ)*(thetaPowerMass 9 (121/128:ℝ) (485/512:ℝ)-(485/512:ℝ)*thetaPowerMass 8 (121/128:ℝ) (485/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0731.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (121/128:ℝ) (485/512:ℝ)
    (485/512:ℝ) (271893/100000000000000:ℝ) (-2805908361233360907/25000000000000000000000000:ℝ) (2202939523384069869/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_484
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1453).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_484 :
    (∫ x in (121/128:ℝ)..(485/512:ℝ), x^8*thetaFirstMode x) ≤ (711080395929/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (121/128:ℝ) (485/512:ℝ)
    (147339/50000000000000:ℝ) (33987/12500000000000:ℝ) (2202939523384069869/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_484 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1453).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_485 :
    (3334285831093/1000000000000000000000000:ℝ) ≤ ∫ x in (485/512:ℝ)..(243/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-224380198710388463775431/2000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (485/512:ℝ) (243/256:ℝ)-(52203587185640050827165/55109141525919324349952:ℝ)*thetaPowerMass 8 (485/512:ℝ) (243/256:ℝ)) ≤
      thetaFirstModeFirst (52203587185640050827165/55109141525919324349952:ℝ)*(thetaPowerMass 9 (485/512:ℝ) (243/256:ℝ)-(52203587185640050827165/55109141525919324349952:ℝ)*thetaPowerMass 8 (485/512:ℝ) (243/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0732.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (485/512:ℝ) (243/256:ℝ)
    (52203587185640050827165/55109141525919324349952:ℝ) (271773/100000000000000:ℝ) (-224380198710388463775431/2000000000000000000000000000000:ℝ) (4097052885021176591/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_485
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1457).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_485 :
    (∫ x in (485/512:ℝ)..(243/256:ℝ), x^8*thetaFirstMode x) ≤ (833640680463/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (485/512:ℝ) (243/256:ℝ)
    (33987/12500000000000:ℝ) (50159/20000000000000:ℝ) (4097052885021176591/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_485 (thetaFirstMode_refined_node_1453).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_486 :
    (1563091129687/500000000000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(487/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-962189115674265387/10000000000000000000000000:ℝ)*(thetaPowerMass 9 (243/256:ℝ) (487/512:ℝ)-(487/512:ℝ)*thetaPowerMass 8 (243/256:ℝ) (487/512:ℝ)) ≤
      thetaFirstModeFirst (487/512:ℝ)*(thetaPowerMass 9 (243/256:ℝ) (487/512:ℝ)-(487/512:ℝ)*thetaPowerMass 8 (243/256:ℝ) (487/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0734.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (243/256:ℝ) (487/512:ℝ)
    (487/512:ℝ) (46251/20000000000000:ℝ) (-962189115674265387/10000000000000000000000000:ℝ) (761731332756242597/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_486
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1459).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_486 :
    (∫ x in (243/256:ℝ)..(487/512:ℝ), x^8*thetaFirstMode x) ≤ (625267278599/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (243/256:ℝ) (487/512:ℝ)
    (50159/20000000000000:ℝ) (115629/50000000000000:ℝ) (761731332756242597/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_486 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1459).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_487 :
    (2929812252779/1000000000000000000000000:ℝ) ≤ ∫ x in (487/512:ℝ)..(61/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-240448542877429540890287/2500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (487/512:ℝ) (61/64:ℝ)-(270866423231695777103343/284768068631243160732160:ℝ)*thetaPowerMass 8 (487/512:ℝ) (61/64:ℝ)) ≤
      thetaFirstModeFirst (270866423231695777103343/284768068631243160732160:ℝ)*(thetaPowerMass 9 (487/512:ℝ) (61/64:ℝ)-(270866423231695777103343/284768068631243160732160:ℝ)*thetaPowerMass 8 (487/512:ℝ) (61/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0735.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (487/512:ℝ) (61/64:ℝ)
    (270866423231695777103343/284768068631243160732160:ℝ) (14447/6250000000000:ℝ) (-240448542877429540890287/2500000000000000000000000000000:ℝ) (3539411636629536411/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_487
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1463).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_487 :
    (∫ x in (487/512:ℝ)..(61/64:ℝ), x^8*thetaFirstMode x) ≤ (183129625693/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (487/512:ℝ) (61/64:ℝ)
    (115629/50000000000000:ℝ) (106587/50000000000000:ℝ) (3539411636629536411/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_487 (thetaFirstMode_refined_node_1459).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_488 :
    (2745009248697/1000000000000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(489/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-257441390182281899/3125000000000000000000000:ℝ)*(thetaPowerMass 9 (61/64:ℝ) (489/512:ℝ)-(489/512:ℝ)*thetaPowerMass 8 (61/64:ℝ) (489/512:ℝ)) ≤
      thetaFirstModeFirst (489/512:ℝ)*(thetaPowerMass 9 (61/64:ℝ) (489/512:ℝ)-(489/512:ℝ)*thetaPowerMass 8 (61/64:ℝ) (489/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0737.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (61/64:ℝ) (489/512:ℝ)
    (489/512:ℝ) (98219/50000000000000:ℝ) (-257441390182281899/3125000000000000000000000:ℝ) (822034761104539841/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_488
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1465).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_488 :
    (∫ x in (61/64:ℝ)..(489/512:ℝ), x^8*thetaFirstMode x) ≤ (5361630503/1953125000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (61/64:ℝ) (489/512:ℝ)
    (106587/50000000000000:ℝ) (196441/100000000000000:ℝ) (822034761104539841/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_488 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1465).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_489 :
    (642689907929/250000000000000000000000:ℝ) ≤ ∫ x in (489/512:ℝ)..(245/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-51467124688020112266333/625000000000000000000000000000:ℝ)*(thetaPowerMass 9 (489/512:ℝ) (245/256:ℝ)-(281043842605185699355041/294259392150867570741760:ℝ)*thetaPowerMass 8 (489/512:ℝ) (245/256:ℝ)) ≤
      thetaFirstModeFirst (281043842605185699355041/294259392150867570741760:ℝ)*(thetaPowerMass 9 (489/512:ℝ) (245/256:ℝ)-(281043842605185699355041/294259392150867570741760:ℝ)*thetaPowerMass 8 (489/512:ℝ) (245/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0738.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (489/512:ℝ) (245/256:ℝ)
    (281043842605185699355041/294259392150867570741760:ℝ) (196351/100000000000000:ℝ) (-51467124688020112266333/625000000000000000000000000000:ℝ) (610742909844803541/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_489
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1469).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_489 :
    (∫ x in (489/512:ℝ)..(245/256:ℝ), x^8*thetaFirstMode x) ≤ (1285492320827/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (489/512:ℝ) (245/256:ℝ)
    (196441/100000000000000:ℝ) (90481/50000000000000:ℝ) (610742909844803541/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_489 (thetaFirstMode_refined_node_1465).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_490 :
    (1203438332653/500000000000000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(491/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-3522115300283345493/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (245/256:ℝ) (491/512:ℝ)-(491/512:ℝ)*thetaPowerMass 8 (245/256:ℝ) (491/512:ℝ)) ≤
      thetaFirstModeFirst (491/512:ℝ)*(thetaPowerMass 9 (245/256:ℝ) (491/512:ℝ)-(491/512:ℝ)*thetaPowerMass 8 (245/256:ℝ) (491/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0740.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (245/256:ℝ) (491/512:ℝ)
    (491/512:ℝ) (166647/100000000000000:ℝ) (-3522115300283345493/50000000000000000000000000:ℝ) (177191960167171811/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_490
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1471).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_490 :
    (∫ x in (245/256:ℝ)..(491/512:ℝ), x^8*thetaFirstMode x) ≤ (481400210327/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (245/256:ℝ) (491/512:ℝ)
    (90481/50000000000000:ℝ) (166649/100000000000000:ℝ) (177191960167171811/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_490 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1471).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_491 :
    (2252475197971/1000000000000000000000000:ℝ) ≤ ∫ x in (491/512:ℝ)..(123/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-70413405472474475513691/1000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (491/512:ℝ) (123/128:ℝ)-(291559767057868215806559/304026373876319976271360:ℝ)*thetaPowerMass 8 (491/512:ℝ) (123/128:ℝ)) ≤
      thetaFirstModeFirst (291559767057868215806559/304026373876319976271360:ℝ)*(thetaPowerMass 9 (491/512:ℝ) (123/128:ℝ)-(291559767057868215806559/304026373876319976271360:ℝ)*thetaPowerMass 8 (491/512:ℝ) (123/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0741.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (491/512:ℝ) (123/128:ℝ)
    (291559767057868215806559/304026373876319976271360:ℝ) (166573/100000000000000:ℝ) (-70413405472474475513691/1000000000000000000000000000000:ℝ) (2631237758612373687/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_491
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1475).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_491 :
    (∫ x in (491/512:ℝ)..(123/128:ℝ), x^8*thetaFirstMode x) ≤ (35198100949/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (491/512:ℝ) (123/128:ℝ)
    (166649/100000000000000:ℝ) (153419/100000000000000:ℝ) (2631237758612373687/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_491 (thetaFirstMode_refined_node_1471).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_492 :
    (2107374249141/1000000000000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(493/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-150387906164567589/2500000000000000000000000:ℝ)*(thetaPowerMass 9 (123/128:ℝ) (493/512:ℝ)-(493/512:ℝ)*thetaPowerMass 8 (123/128:ℝ) (493/512:ℝ)) ≤
      thetaFirstModeFirst (493/512:ℝ)*(thetaPowerMass 9 (123/128:ℝ) (493/512:ℝ)-(493/512:ℝ)*thetaPowerMass 8 (123/128:ℝ) (493/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0743.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (123/128:ℝ) (493/512:ℝ)
    (493/512:ℝ) (14119/10000000000000:ℝ) (-150387906164567589/2500000000000000000000000:ℝ) (2441238021041889237/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_492
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1477).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_492 :
    (∫ x in (123/128:ℝ)..(493/512:ℝ), x^8*thetaFirstMode x) ≤ (65859087453/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (123/128:ℝ) (493/512:ℝ)
    (153419/100000000000000:ℝ) (17649/12500000000000:ℝ) (2441238021041889237/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_492 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1477).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_493 :
    (39414939857/20000000000000000000000:ℝ) ≤ ∫ x in (493/512:ℝ)..(247/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-375812822403357945730059/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (493/512:ℝ) (247/256:ℝ)-(302424007419219829279257/314075847828315644700160:ℝ)*thetaPowerMass 8 (493/512:ℝ) (247/256:ℝ)) ≤
      thetaFirstModeFirst (302424007419219829279257/314075847828315644700160:ℝ)*(thetaPowerMass 9 (493/512:ℝ) (247/256:ℝ)-(302424007419219829279257/314075847828315644700160:ℝ)*thetaPowerMass 8 (493/512:ℝ) (247/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0744.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (493/512:ℝ) (247/256:ℝ)
    (302424007419219829279257/314075847828315644700160:ℝ) (70563/50000000000000:ℝ) (-375812822403357945730059/6250000000000000000000000000000:ℝ) (2264215051628209499/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_493
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1481).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_493 :
    (∫ x in (493/512:ℝ)..(247/256:ℝ), x^8*thetaFirstMode x) ≤ (197094302111/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (493/512:ℝ) (247/256:ℝ)
    (17649/12500000000000:ℝ) (129897/100000000000000:ℝ) (2264215051628209499/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_493 (thetaFirstMode_refined_node_1477).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_494 :
    (921234140167/500000000000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(495/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-320640680524480087/6250000000000000000000000:ℝ)*(thetaPowerMass 9 (247/256:ℝ) (495/512:ℝ)-(495/512:ℝ)*thetaPowerMass 8 (247/256:ℝ) (495/512:ℝ)) ≤
      thetaFirstModeFirst (495/512:ℝ)*(thetaPowerMass 9 (247/256:ℝ) (495/512:ℝ)-(495/512:ℝ)*thetaPowerMass 8 (247/256:ℝ) (495/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0746.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (247/256:ℝ) (495/512:ℝ)
    (495/512:ℝ) (14933/12500000000000:ℝ) (-320640680524480087/6250000000000000000000000:ℝ) (2099330505113338621/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_494
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1483).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_494 :
    (∫ x in (247/256:ℝ)..(495/512:ℝ), x^8*thetaFirstMode x) ≤ (230321968629/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (247/256:ℝ) (495/512:ℝ)
    (129897/100000000000000:ℝ) (59733/50000000000000:ℝ) (2099330505113338621/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_494 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1483).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_495 :
    (1721768663157/1000000000000000000000000:ℝ) ≤ ∫ x in (495/512:ℝ)..(31/32:ℝ), x^8*thetaFirstMode x := by
  have hd : (-80127009761065797301587/1562500000000000000000000000000:ℝ)*(thetaPowerMass 9 (495/512:ℝ) (31/32:ℝ)-(62729323448440729602555/64882957727484714455552:ℝ)*thetaPowerMass 8 (495/512:ℝ) (31/32:ℝ)) ≤
      thetaFirstModeFirst (62729323448440729602555/64882957727484714455552:ℝ)*(thetaPowerMass 9 (495/512:ℝ) (31/32:ℝ)-(62729323448440729602555/64882957727484714455552:ℝ)*thetaPowerMass 8 (495/512:ℝ) (31/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0747.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (495/512:ℝ) (31/32:ℝ)
    (62729323448440729602555/64882957727484714455552:ℝ) (11941/10000000000000:ℝ) (-80127009761065797301587/1562500000000000000000000000000:ℝ) (1945819361608664979/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_495
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1487).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_495 :
    (∫ x in (495/512:ℝ)..(31/32:ℝ), x^8*thetaFirstMode x) ≤ (1721940406757/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (495/512:ℝ) (31/32:ℝ)
    (59733/50000000000000:ℝ) (27459/25000000000000:ℝ) (1945819361608664979/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_495 (thetaFirstMode_refined_node_1483).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_496 :
    (1608533975247/1000000000000000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(497/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-27309362525682283/625000000000000000000000:ℝ)*(thetaPowerMass 9 (31/32:ℝ) (497/512:ℝ)-(497/512:ℝ)*thetaPowerMass 8 (31/32:ℝ) (497/512:ℝ)) ≤
      thetaFirstModeFirst (497/512:ℝ)*(thetaPowerMass 9 (31/32:ℝ) (497/512:ℝ)-(497/512:ℝ)*thetaPowerMass 8 (31/32:ℝ) (497/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0749.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (31/32:ℝ) (497/512:ℝ)
    (497/512:ℝ) (25237/25000000000000:ℝ) (-27309362525682283/625000000000000000000000:ℝ) (225365264048970199/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_496
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1489).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_496 :
    (∫ x in (31/32:ℝ)..(497/512:ℝ), x^8*thetaFirstMode x) ≤ (804308683651/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/32:ℝ) (497/512:ℝ)
    (27459/25000000000000:ℝ) (100949/100000000000000:ℝ) (225365264048970199/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_496 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1489).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_497 :
    (1502056995633/1000000000000000000000000:ℝ) ≤ ∫ x in (497/512:ℝ)..(249/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-27298046771651250923247/625000000000000000000000000000:ℝ)*(thetaPowerMass 9 (497/512:ℝ) (249/256:ℝ)-(325237897787019494300793/335050313849050052508160:ℝ)*thetaPowerMass 8 (497/512:ℝ) (249/256:ℝ)) ≤
      thetaFirstModeFirst (325237897787019494300793/335050313849050052508160:ℝ)*(thetaPowerMass 9 (497/512:ℝ) (249/256:ℝ)-(325237897787019494300793/335050313849050052508160:ℝ)*thetaPowerMass 8 (497/512:ℝ) (249/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0750.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (497/512:ℝ) (249/256:ℝ)
    (325237897787019494300793/335050313849050052508160:ℝ) (50451/50000000000000:ℝ) (-27298046771651250923247/625000000000000000000000000000:ℝ) (1669957593656032913/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_497
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1493).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_497 :
    (∫ x in (497/512:ℝ)..(249/256:ℝ), x^8*thetaFirstMode x) ≤ (1502204628081/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (497/512:ℝ) (249/256:ℝ)
    (100949/100000000000000:ℝ) (371/400000000000:ℝ) (1669957593656032913/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_497 (thetaFirstMode_refined_node_1489).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_498 :
    (1402232975291/1000000000000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(499/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-23228391227735441/625000000000000000000000:ℝ)*(thetaPowerMass 9 (249/256:ℝ) (499/512:ℝ)-(499/512:ℝ)*thetaPowerMass 8 (249/256:ℝ) (499/512:ℝ)) ≤
      thetaFirstModeFirst (499/512:ℝ)*(thetaPowerMass 9 (249/256:ℝ) (499/512:ℝ)-(499/512:ℝ)*thetaPowerMass 8 (249/256:ℝ) (499/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0752.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (249/256:ℝ) (499/512:ℝ)
    (499/512:ℝ) (85187/100000000000000:ℝ) (-23228391227735441/625000000000000000000000:ℝ) (1546272297162852323/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_498
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1495).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_498 :
    (∫ x in (249/256:ℝ)..(499/512:ℝ), x^8*thetaFirstMode x) ≤ (701160573067/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (249/256:ℝ) (499/512:ℝ)
    (371/400000000000:ℝ) (85189/100000000000000:ℝ) (1546272297162852323/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_498 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1495).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_499 :
    (1308447656783/1000000000000000000000000:ℝ) ≤ ∫ x in (499/512:ℝ)..(125/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-4643759990130725618479/125000000000000000000000000000:ℝ)*(thetaPowerMass 9 (499/512:ℝ) (125/128:ℝ)-(337208403086384037209991/345989686256645754242560:ℝ)*thetaPowerMass 8 (499/512:ℝ) (125/128:ℝ)) ≤
      thetaFirstModeFirst (337208403086384037209991/345989686256645754242560:ℝ)*(thetaPowerMass 9 (499/512:ℝ) (125/128:ℝ)-(337208403086384037209991/345989686256645754242560:ℝ)*thetaPowerMass 8 (499/512:ℝ) (125/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0753.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (499/512:ℝ) (125/128:ℝ)
    (337208403086384037209991/345989686256645754242560:ℝ) (21287/25000000000000:ℝ) (-4643759990130725618479/125000000000000000000000000000:ℝ) (1431278615296834699/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_499
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1499).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_499 :
    (∫ x in (499/512:ℝ)..(125/128:ℝ), x^8*thetaFirstMode x) ≤ (327148515789/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (499/512:ℝ) (125/128:ℝ)
    (85189/100000000000000:ℝ) (78217/100000000000000:ℝ) (1431278615296834699/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_499 (thetaFirstMode_refined_node_1495).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_500 :
    (1220608607923/1000000000000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(501/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1578474080342429057/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (125/128:ℝ) (501/512:ℝ)-(501/512:ℝ)*thetaPowerMass 8 (125/128:ℝ) (501/512:ℝ)) ≤
      thetaFirstModeFirst (501/512:ℝ)*(thetaPowerMass 9 (125/128:ℝ) (501/512:ℝ)-(501/512:ℝ)*thetaPowerMass 8 (125/128:ℝ) (501/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0755.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (125/128:ℝ) (501/512:ℝ)
    (501/512:ℝ) (71791/100000000000000:ℝ) (-1578474080342429057/50000000000000000000000000:ℝ) (165548028491786147/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_500
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1501).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_500 :
    (∫ x in (125/128:ℝ)..(501/512:ℝ), x^8*thetaFirstMode x) ≤ (61033875689/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (125/128:ℝ) (501/512:ℝ)
    (78217/100000000000000:ℝ) (4487/6250000000000:ℝ) (165548028491786147/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_500 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1501).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_501 :
    (1138127492929/1000000000000000000000000:ℝ) ≤ ∫ x in (501/512:ℝ)..(251/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-788902089583851834247571/25000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (501/512:ℝ) (251/256:ℝ)-(349568945093337212835009/357240316263365765762560:ℝ)*thetaPowerMass 8 (501/512:ℝ) (251/256:ℝ)) ≤
      thetaFirstModeFirst (349568945093337212835009/357240316263365765762560:ℝ)*(thetaPowerMass 9 (501/512:ℝ) (251/256:ℝ)-(349568945093337212835009/357240316263365765762560:ℝ)*thetaPowerMass 8 (501/512:ℝ) (251/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0756.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (501/512:ℝ) (251/256:ℝ)
    (349568945093337212835009/357240316263365765762560:ℝ) (35879/50000000000000:ℝ) (-788902089583851834247571/25000000000000000000000000000000:ℝ) (612524077747350281/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_501
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1505).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_501 :
    (∫ x in (501/512:ℝ)..(251/256:ℝ), x^8*thetaFirstMode x) ≤ (569123878269/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (501/512:ℝ) (251/256:ℝ)
    (4487/6250000000000:ℝ) (4117/6250000000000:ℝ) (612524077747350281/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_501 (thetaFirstMode_refined_node_1501).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_502 :
    (212185266603/200000000000000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(503/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-1338974595835997493/50000000000000000000000000:ℝ)*(thetaPowerMass 9 (251/256:ℝ) (503/512:ℝ)-(503/512:ℝ)*thetaPowerMass 8 (251/256:ℝ) (503/512:ℝ)) ≤
      thetaFirstModeFirst (503/512:ℝ)*(thetaPowerMass 9 (251/256:ℝ) (503/512:ℝ)-(503/512:ℝ)*thetaPowerMass 8 (251/256:ℝ) (503/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0758.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (251/256:ℝ) (503/512:ℝ)
    (503/512:ℝ) (60419/100000000000000:ℝ) (-1338974595835997493/50000000000000000000000000:ℝ) (70798955969898033/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_502
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1507).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_502 :
    (∫ x in (251/256:ℝ)..(503/512:ℝ), x^8*thetaFirstMode x) ≤ (132623730251/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (251/256:ℝ) (503/512:ℝ)
    (4117/6250000000000:ℝ) (3021/5000000000000:ℝ) (70798955969898033/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_502 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1507).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_503 :
    (98849591191/100000000000000000000000:ℝ) ≤ ∫ x in (503/512:ℝ)..(63/64:ℝ), x^8*thetaFirstMode x := by
  have hd : (-167300586946877247705661/6250000000000000000000000000000:ℝ)*(thetaPowerMass 9 (503/512:ℝ) (63/64:ℝ)-(362330598912579278694207/368809764272412990108160:ℝ)*thetaPowerMass 8 (503/512:ℝ) (63/64:ℝ)) ≤
      thetaFirstModeFirst (362330598912579278694207/368809764272412990108160:ℝ)*(thetaPowerMass 9 (503/512:ℝ) (63/64:ℝ)-(362330598912579278694207/368809764272412990108160:ℝ)*thetaPowerMass 8 (503/512:ℝ) (63/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0759.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (503/512:ℝ) (63/64:ℝ)
    (362330598912579278694207/368809764272412990108160:ℝ) (60391/100000000000000:ℝ) (-167300586946877247705661/6250000000000000000000000000000:ℝ) (209420464077006753/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_503
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1511).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_503 :
    (∫ x in (503/512:ℝ)..(63/64:ℝ), x^8*thetaFirstMode x) ≤ (988608025507/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (503/512:ℝ) (63/64:ℝ)
    (3021/5000000000000:ℝ) (277/500000000000:ℝ) (209420464077006753/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_503 (thetaFirstMode_refined_node_1507).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_504 :
    (23018589793/25000000000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(505/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-141780158809659279/6250000000000000000000000:ℝ)*(thetaPowerMass 9 (63/64:ℝ) (505/512:ℝ)-(505/512:ℝ)*thetaPowerMass 8 (63/64:ℝ) (505/512:ℝ)) ≤
      thetaFirstModeFirst (505/512:ℝ)*(thetaPowerMass 9 (63/64:ℝ) (505/512:ℝ)-(505/512:ℝ)*thetaPowerMass 8 (63/64:ℝ) (505/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0761.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (63/64:ℝ) (505/512:ℝ)
    (505/512:ℝ) (25389/50000000000000:ℝ) (-141780158809659279/6250000000000000000000000:ℝ) (967556150380563339/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_504
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1513).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_504 :
    (∫ x in (63/64:ℝ)..(505/512:ℝ), x^8*thetaFirstMode x) ≤ (920820052579/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (63/64:ℝ) (505/512:ℝ)
    (277/500000000000:ℝ) (2539/5000000000000:ℝ) (967556150380563339/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_504 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1513).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_505 :
    (857250184107/1000000000000000000000000:ℝ) ≤ ∫ x in (505/512:ℝ)..(253/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-283443465793226403186967/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (505/512:ℝ) (253/256:ℝ)-(75100941623270192936445/76141148621259241175552:ℝ)*thetaPowerMass 8 (505/512:ℝ) (253/256:ℝ)) ≤
      thetaFirstModeFirst (75100941623270192936445/76141148621259241175552:ℝ)*(thetaPowerMass 9 (505/512:ℝ) (253/256:ℝ)-(75100941623270192936445/76141148621259241175552:ℝ)*thetaPowerMass 8 (505/512:ℝ) (253/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0762.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (505/512:ℝ) (253/256:ℝ)
    (75100941623270192936445/76141148621259241175552:ℝ) (10151/20000000000000:ℝ) (-283443465793226403186967/12500000000000000000000000000000:ℝ) (223443573900565599/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_505
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1517).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_505 :
    (∫ x in (505/512:ℝ)..(253/256:ℝ), x^8*thetaFirstMode x) ≤ (428679638627/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (505/512:ℝ) (253/256:ℝ)
    (2539/5000000000000:ℝ) (46529/100000000000000:ℝ) (223443573900565599/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_505 (thetaFirstMode_refined_node_1513).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_506 :
    (15958210293/20000000000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(507/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-59969949964713963/3125000000000000000000000:ℝ)*(thetaPowerMass 9 (253/256:ℝ) (507/512:ℝ)-(507/512:ℝ)*thetaPowerMass 8 (253/256:ℝ) (507/512:ℝ)) ≤
      thetaFirstModeFirst (507/512:ℝ)*(thetaPowerMass 9 (253/256:ℝ) (507/512:ℝ)-(507/512:ℝ)*thetaPowerMass 8 (253/256:ℝ) (507/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0764.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (253/256:ℝ) (507/512:ℝ)
    (507/512:ℝ) (21309/50000000000000:ℝ) (-59969949964713963/3125000000000000000000000:ℝ) (825313465073590469/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_506
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1519).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_506 :
    (∫ x in (253/256:ℝ)..(507/512:ℝ), x^8*thetaFirstMode x) ≤ (199492073141/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (253/256:ℝ) (507/512:ℝ)
    (46529/100000000000000:ℝ) (42619/100000000000000:ℝ) (825313465073590469/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_506 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1519).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_507 :
    (185578863917/250000000000000000000000:ℝ) ≤ ∫ x in (507/512:ℝ)..(127/128:ℝ), x^8*thetaFirstMode x := by
  have hd : (-239777914527258129755283/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (507/512:ℝ) (127/128:ℝ)-(389102890145877331465743/392936120455235036700160:ℝ)*thetaPowerMass 8 (507/512:ℝ) (127/128:ℝ)) ≤
      thetaFirstModeFirst (389102890145877331465743/392936120455235036700160:ℝ)*(thetaPowerMass 9 (507/512:ℝ) (127/128:ℝ)-(389102890145877331465743/392936120455235036700160:ℝ)*thetaPowerMass 8 (507/512:ℝ) (127/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0765.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (507/512:ℝ) (127/128:ℝ)
    (389102890145877331465743/392936120455235036700160:ℝ) (21299/50000000000000:ℝ) (-239777914527258129755283/12500000000000000000000000000000:ℝ) (152366120075123307/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_507
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1523).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_507 :
    (∫ x in (507/512:ℝ)..(127/128:ℝ), x^8*thetaFirstMode x) ≤ (742409662977/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (507/512:ℝ) (127/128:ℝ)
    (42619/100000000000000:ℝ) (2439/6250000000000:ℝ) (152366120075123307/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_507 (thetaFirstMode_refined_node_1519).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_508 :
    (690407429333/1000000000000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(509/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-405284833961653439/25000000000000000000000000:ℝ)*(thetaPowerMass 9 (127/128:ℝ) (509/512:ℝ)-(509/512:ℝ)*thetaPowerMass 8 (127/128:ℝ) (509/512:ℝ)) ≤
      thetaFirstModeFirst (509/512:ℝ)*(thetaPowerMass 9 (127/128:ℝ) (509/512:ℝ)-(509/512:ℝ)*thetaPowerMass 8 (127/128:ℝ) (509/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0767.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (127/128:ℝ) (509/512:ℝ)
    (509/512:ℝ) (35719/100000000000000:ℝ) (-405284833961653439/25000000000000000000000000:ℝ) (702988870739379477/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_508
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1525).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_508 :
    (∫ x in (127/128:ℝ)..(509/512:ℝ), x^8*thetaFirstMode x) ≤ (43153710359/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (127/128:ℝ) (509/512:ℝ)
    (2439/6250000000000:ℝ) (893/2500000000000:ℝ) (702988870739379477/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_508 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1525).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_509 :
    (641811136391/1000000000000000000000000:ℝ) ≤ ∫ x in (509/512:ℝ)..(255/256:ℝ), x^8*thetaFirstMode x := by
  have hd : (-810223604736024861834831/50000000000000000000000000000000:ℝ)*(thetaPowerMass 9 (509/512:ℝ) (255/256:ℝ)-(403137041799404128338441/405508921354945001551360:ℝ)*thetaPowerMass 8 (509/512:ℝ) (255/256:ℝ)) ≤
      thetaFirstModeFirst (403137041799404128338441/405508921354945001551360:ℝ)*(thetaPowerMass 9 (509/512:ℝ) (255/256:ℝ)-(403137041799404128338441/405508921354945001551360:ℝ)*thetaPowerMass 8 (509/512:ℝ) (255/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0768.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (509/512:ℝ) (255/256:ℝ)
    (403137041799404128338441/405508921354945001551360:ℝ) (17851/50000000000000:ℝ) (-810223604736024861834831/50000000000000000000000000000000:ℝ) (324229093938615553/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_509
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1529).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_509 :
    (∫ x in (509/512:ℝ)..(255/256:ℝ), x^8*thetaFirstMode x) ≤ (320949690009/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (509/512:ℝ) (255/256:ℝ)
    (893/2500000000000:ℝ) (8171/25000000000000:ℝ) (324229093938615553/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_509 (thetaFirstMode_refined_node_1525).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_510 :
    (59648184561/100000000000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(511/512:ℝ), x^8*thetaFirstMode x := by
  have hd : (-17094632934853899/1250000000000000000000000:ℝ)*(thetaPowerMass 9 (255/256:ℝ) (511/512:ℝ)-(511/512:ℝ)*thetaPowerMass 8 (255/256:ℝ) (511/512:ℝ)) ≤
      thetaFirstModeFirst (511/512:ℝ)*(thetaPowerMass 9 (255/256:ℝ) (511/512:ℝ)-(511/512:ℝ)*thetaPowerMass 8 (255/256:ℝ) (511/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0770.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (255/256:ℝ) (511/512:ℝ)
    (511/512:ℝ) (5979/20000000000000:ℝ) (-17094632934853899/1250000000000000000000000:ℝ) (597955739038740007/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_510
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1531).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_510 :
    (∫ x in (255/256:ℝ)..(511/512:ℝ), x^8*thetaFirstMode x) ≤ (596528635111/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (255/256:ℝ) (511/512:ℝ)
    (8171/25000000000000:ℝ) (3737/12500000000000:ℝ) (597955739038740007/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_510 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1531).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_8_511 :
    (554077498193/1000000000000000000000000:ℝ) ≤ ∫ x in (511/512:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x := by
  have hd : (-170875568653144961453789/12500000000000000000000000000000:ℝ)*(thetaPowerMass 9 (511/512:ℝ) (1/1:ℝ)-(417619344807863656339959/418432330694036747061760:ℝ)*thetaPowerMass 8 (511/512:ℝ) (1/1:ℝ)) ≤
      thetaFirstModeFirst (417619344807863656339959/418432330694036747061760:ℝ)*(thetaPowerMass 9 (511/512:ℝ) (1/1:ℝ)-(417619344807863656339959/418432330694036747061760:ℝ)*thetaPowerMass 8 (511/512:ℝ) (1/1:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0771.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 8 (511/512:ℝ) (1/1:ℝ)
    (417619344807863656339959/418432330694036747061760:ℝ) (29881/100000000000000:ℝ) (-170875568653144961453789/12500000000000000000000000000000:ℝ) (275593830843204751/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_511
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1535).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_8_511 :
    (∫ x in (511/512:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x) ≤ (1385388539/2500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (511/512:ℝ) (1/1:ℝ)
    (3737/12500000000000:ℝ) (3417/12500000000000:ℝ) (275593830843204751/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_511 (thetaFirstMode_refined_node_1531).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

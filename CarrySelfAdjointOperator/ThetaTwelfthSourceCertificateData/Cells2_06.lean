import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature06
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative09
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative10

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_2_192 :
    (850536198473893679/1000000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(193/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-122199074708781032214327/3125000000000000000000000:ℝ)*(thetaPowerMass 3 (3/8:ℝ) (193/512:ℝ)-(193/512:ℝ)*thetaPowerMass 2 (3/8:ℝ) (193/512:ℝ)) ≤
      thetaFirstModeFirst (193/512:ℝ)*(thetaPowerMass 3 (3/8:ℝ) (193/512:ℝ)-(193/512:ℝ)*thetaPowerMass 2 (3/8:ℝ) (193/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0293.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (3/8:ℝ) (193/512:ℝ)
    (193/512:ℝ) (304224667353/100000000000000:ℝ) (-122199074708781032214327/3125000000000000000000000:ℝ) (421372198150856993365933/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_192
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0577).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_192 :
    (∫ x in (3/8:ℝ)..(193/512:ℝ), x^2*thetaFirstMode x) ≤ (212634651206177087/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/8:ℝ) (193/512:ℝ)
    (311943577261/100000000000000:ℝ) (475352053/156250000000:ℝ) (421372198150856993365933/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_192 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0577).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_193 :
    (838089217832598929/1000000000000000000000000:ℝ) ≤ ∫ x in (193/512:ℝ)..(97/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-244327697043121646172975414807/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (193/512:ℝ) (97/256:ℝ)-(65332341813084493257/173304480845017500160:ℝ)*thetaPowerMass 2 (193/512:ℝ) (97/256:ℝ)) ≤
      thetaFirstModeFirst (65332341813084493257/173304480845017500160:ℝ)*(thetaPowerMass 3 (193/512:ℝ) (97/256:ℝ)-(65332341813084493257/173304480845017500160:ℝ)*thetaPowerMass 2 (193/512:ℝ) (97/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0294.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (193/512:ℝ) (97/256:ℝ)
    (65332341813084493257/173304480845017500160:ℝ) (12164766849/4000000000000:ℝ) (-244327697043121646172975414807/6250000000000000000000000000000:ℝ) (82917690064399091062251/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_193
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0581).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_193 :
    (∫ x in (193/512:ℝ)..(97/256:ℝ), x^2*thetaFirstMode x) ≤ (419046089780159357/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (193/512:ℝ) (97/256:ℝ)
    (475352053/156250000000:ℝ) (296667793723/100000000000000:ℝ) (82917690064399091062251/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_193 (thetaFirstMode_refined_node_0577).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_194 :
    (412848560408524683/500000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(195/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-366056393134101133031/9765625000000000000000:ℝ)*(thetaPowerMass 3 (97/256:ℝ) (195/512:ℝ)-(195/512:ℝ)*thetaPowerMass 2 (97/256:ℝ) (195/512:ℝ)) ≤
      thetaFirstModeFirst (195/512:ℝ)*(thetaPowerMass 3 (97/256:ℝ) (195/512:ℝ)-(195/512:ℝ)*thetaPowerMass 2 (97/256:ℝ) (195/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0296.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (97/256:ℝ) (195/512:ℝ)
    (195/512:ℝ) (56497619/19531250000:ℝ) (-366056393134101133031/9765625000000000000000:ℝ) (407869947363270890347949/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_194
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0583).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_194 :
    (∫ x in (97/256:ℝ)..(195/512:ℝ), x^2*thetaFirstMode x) ≤ (825699488994912289/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (97/256:ℝ) (195/512:ℝ)
    (296667793723/100000000000000:ℝ) (289268428881/100000000000000:ℝ) (407869947363270890347949/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_194 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0583).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_195 :
    (813360760342454363/1000000000000000000000000:ℝ) ≤ ∫ x in (195/512:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-29276075031654577887586844773/781250000000000000000000000000:ℝ)*(thetaPowerMass 3 (195/512:ℝ) (49/128:ℝ)-(14336762398671353355/37640552179499351552:ℝ)*thetaPowerMass 2 (195/512:ℝ) (49/128:ℝ)) ≤
      thetaFirstModeFirst (14336762398671353355/37640552179499351552:ℝ)*(thetaPowerMass 3 (195/512:ℝ) (49/128:ℝ)-(14336762398671353355/37640552179499351552:ℝ)*thetaPowerMass 2 (195/512:ℝ) (49/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0297.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (195/512:ℝ) (49/128:ℝ)
    (14336762398671353355/37640552179499351552:ℝ) (72291929829/25000000000000:ℝ) (-29276075031654577887586844773/781250000000000000000000000000:ℝ) (200608460632174198657677/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_195
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0587).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_195 :
    (∫ x in (195/512:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x) ≤ (813363684410491601/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (195/512:ℝ) (49/128:ℝ)
    (289268428881/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (200608460632174198657677/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_195 (thetaFirstMode_refined_node_0583).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_196 :
    (801085501169700007/1000000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(197/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1795843883699179309941067/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (49/128:ℝ) (197/512:ℝ)-(197/512:ℝ)*thetaPowerMass 2 (49/128:ℝ) (197/512:ℝ)) ≤
      thetaFirstModeFirst (197/512:ℝ)*(thetaPowerMass 3 (49/128:ℝ) (197/512:ℝ)-(197/512:ℝ)*thetaPowerMass 2 (49/128:ℝ) (197/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0299.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (49/128:ℝ) (197/512:ℝ)
    (197/512:ℝ) (274933345111/100000000000000:ℝ) (-1795843883699179309941067/50000000000000000000000000:ℝ) (394629585759214226027709/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_196
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0589).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_196 :
    (∫ x in (49/128:ℝ)..(197/512:ℝ), x^2*thetaFirstMode x) ≤ (801087830507157039/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (49/128:ℝ) (197/512:ℝ)
    (282024656491/100000000000000:ℝ) (274933938627/100000000000000:ℝ) (394629585759214226027709/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_196 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0589).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_197 :
    (788872020133605107/1000000000000000000000000:ℝ) ≤ ∫ x in (197/512:ℝ)..(99/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (197/512:ℝ) (99/256:ℝ)-(78578341309131839793/204209882504936988160:ℝ)*thetaPowerMass 2 (197/512:ℝ) (99/256:ℝ)) ≤
      thetaFirstModeFirst (78578341309131839793/204209882504936988160:ℝ)*(thetaPowerMass 3 (197/512:ℝ) (99/256:ℝ)-(78578341309131839793/204209882504936988160:ℝ)*thetaPowerMass 2 (197/512:ℝ) (99/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0300.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (197/512:ℝ) (99/256:ℝ)
    (78578341309131839793/204209882504936988160:ℝ) (274838413521/100000000000000:ℝ) (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ) (194054068215068659549999/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_197
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0593).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_197 :
    (∫ x in (197/512:ℝ)..(99/256:ℝ), x^2*thetaFirstMode x) ≤ (394437452739622217/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (197/512:ℝ) (99/256:ℝ)
    (274933938627/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (194054068215068659549999/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_197 (thetaFirstMode_refined_node_0589).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_198 :
    (776725511245777491/1000000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(199/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-430009833253962321035977/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (99/256:ℝ) (199/512:ℝ)-(199/512:ℝ)*thetaPowerMass 2 (99/256:ℝ) (199/512:ℝ)) ≤
      thetaFirstModeFirst (199/512:ℝ)*(thetaPowerMass 3 (99/256:ℝ) (199/512:ℝ)-(199/512:ℝ)*thetaPowerMass 2 (99/256:ℝ) (199/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0302.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (99/256:ℝ) (199/512:ℝ)
    (199/512:ℝ) (65300267963/25000000000000:ℝ) (-430009833253962321035977/12500000000000000000000000:ℝ) (190826375409226913883677/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_198
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0595).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_198 :
    (∫ x in (99/256:ℝ)..(199/512:ℝ), x^2*thetaFirstMode x) ≤ (776727801127425129/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (99/256:ℝ) (199/512:ℝ)
    (33499220303/12500000000000:ℝ) (52240328029/20000000000000:ℝ) (190826375409226913883677/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_198 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0595).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_199 :
    (597380060482479/781250000000000000000:ℝ) ≤ ∫ x in (199/512:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-429886080618259761215196442893/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (199/512:ℝ) (25/64:ℝ)-(86056132492075958991/221395846441879298560:ℝ)*thetaPowerMass 2 (199/512:ℝ) (25/64:ℝ)) ≤
      thetaFirstModeFirst (86056132492075958991/221395846441879298560:ℝ)*(thetaPowerMass 3 (199/512:ℝ) (25/64:ℝ)-(86056132492075958991/221395846441879298560:ℝ)*thetaPowerMass 2 (199/512:ℝ) (25/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0303.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (199/512:ℝ) (25/64:ℝ)
    (86056132492075958991/221395846441879298560:ℝ) (261111060999/100000000000000:ℝ) (-429886080618259761215196442893/12500000000000000000000000000000:ℝ) (375263588556175193661479/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_199
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0599).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_199 :
    (∫ x in (199/512:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x) ≤ (152929864606563341/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (199/512:ℝ) (25/64:ℝ)
    (52240328029/20000000000000:ℝ) (12727755463/5000000000000:ℝ) (375263588556175193661479/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_199 (thetaFirstMode_refined_node_0595).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_200 :
    (47039996306374251/62500000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(201/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-32934869486208662412563/1000000000000000000000000:ℝ)*(thetaPowerMass 3 (25/64:ℝ) (201/512:ℝ)-(201/512:ℝ)*thetaPowerMass 2 (25/64:ℝ) (201/512:ℝ)) ≤
      thetaFirstModeFirst (201/512:ℝ)*(thetaPowerMass 3 (25/64:ℝ) (201/512:ℝ)-(201/512:ℝ)*thetaPowerMass 2 (25/64:ℝ) (201/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0305.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (25/64:ℝ) (201/512:ℝ)
    (201/512:ℝ) (248051188579/100000000000000:ℝ) (-32934869486208662412563/1000000000000000000000000:ℝ) (368940791481683951042041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_200
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0601).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_200 :
    (∫ x in (25/64:ℝ)..(201/512:ℝ), x^2*thetaFirstMode x) ≤ (150528438154935943/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (25/64:ℝ) (201/512:ℝ)
    (12727755463/5000000000000:ℝ) (15503233281/6250000000000:ℝ) (368940791481683951042041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_200 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0601).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_201 :
    (740706233243273151/1000000000000000000000000:ℝ) ≤ ∫ x in (201/512:ℝ)..(101/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (201/512:ℝ) (101/256:ℝ)-(94159912870084059009/239834298071963906560:ℝ)*thetaPowerMass 2 (201/512:ℝ) (101/256:ℝ)) ≤
      thetaFirstModeFirst (94159912870084059009/239834298071963906560:ℝ)*(thetaPowerMass 3 (201/512:ℝ) (101/256:ℝ)-(94159912870084059009/239834298071963906560:ℝ)*thetaPowerMass 2 (201/512:ℝ) (101/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0306.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (201/512:ℝ) (101/256:ℝ)
    (94159912870084059009/239834298071963906560:ℝ) (247965870591/100000000000000:ℝ) (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ) (181342241891124615302757/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_201
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0605).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_201 :
    (∫ x in (201/512:ℝ)..(101/256:ℝ), x^2*thetaFirstMode x) ≤ (185177259546449799/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (201/512:ℝ) (101/256:ℝ)
    (15503233281/6250000000000:ℝ) (30211137237/12500000000000:ℝ) (181342241891124615302757/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_201 (thetaFirstMode_refined_node_0601).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_202 :
    (728850204313822751/1000000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(203/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1575904465507159884915987/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (101/256:ℝ) (203/512:ℝ)-(203/512:ℝ)*thetaPowerMass 2 (101/256:ℝ) (203/512:ℝ)) ≤
      thetaFirstModeFirst (203/512:ℝ)*(thetaPowerMass 3 (101/256:ℝ) (203/512:ℝ)-(203/512:ℝ)*thetaPowerMass 2 (101/256:ℝ) (203/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0308.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (101/256:ℝ) (203/512:ℝ)
    (203/512:ℝ) (235464298503/100000000000000:ℝ) (-1575904465507159884915987/50000000000000000000000000:ℝ) (356494772124939210200983/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_202
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0607).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_202 :
    (∫ x in (101/256:ℝ)..(203/512:ℝ), x^2*thetaFirstMode x) ≤ (364426206837031943/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (101/256:ℝ) (203/512:ℝ)
    (30211137237/12500000000000:ℝ) (235464818869/100000000000000:ℝ) (356494772124939210200983/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_202 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0607).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_203 :
    (71707201719660757/100000000000000000000000:ℝ) ≤ ∫ x in (203/512:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-393862812547991790702588742107/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (203/512:ℝ) (51/128:ℝ)-(102935065125197358207/259602677601152028160:ℝ)*thetaPowerMass 2 (203/512:ℝ) (51/128:ℝ)) ≤
      thetaFirstModeFirst (102935065125197358207/259602677601152028160:ℝ)*(thetaPowerMass 3 (203/512:ℝ) (51/128:ℝ)-(102935065125197358207/259602677601152028160:ℝ)*thetaPowerMass 2 (203/512:ℝ) (51/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0309.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (203/512:ℝ) (51/128:ℝ)
    (102935065125197358207/259602677601152028160:ℝ) (2353834549/1000000000000:ℝ) (-393862812547991790702588742107/12500000000000000000000000000000:ℝ) (875929364510965849653/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_203
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0611).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_203 :
    (∫ x in (203/512:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x) ≤ (89634347571676777/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (203/512:ℝ) (51/128:ℝ)
    (235464818869/100000000000000:ℝ) (9175061369/4000000000000:ℝ) (875929364510965849653/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_203 (thetaFirstMode_refined_node_0607).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_204 :
    (705376349143697309/1000000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(205/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1507470284078181177087227/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (51/128:ℝ) (205/512:ℝ)-(205/512:ℝ)*thetaPowerMass 2 (51/128:ℝ) (205/512:ℝ)) ≤
      thetaFirstModeFirst (205/512:ℝ)*(thetaPowerMass 3 (51/128:ℝ) (205/512:ℝ)-(205/512:ℝ)*thetaPowerMass 2 (51/128:ℝ) (205/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0311.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (51/128:ℝ) (205/512:ℝ)
    (205/512:ℝ) (223421410591/100000000000000:ℝ) (-1507470284078181177087227/50000000000000000000000000:ℝ) (172157738447815749517883/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_204
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0613).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_204 :
    (∫ x in (51/128:ℝ)..(205/512:ℝ), x^2*thetaFirstMode x) ≤ (88172314692956713/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (51/128:ℝ) (205/512:ℝ)
    (9175061369/4000000000000:ℝ) (44684381643/20000000000000:ℝ) (172157738447815749517883/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_204 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0613).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_205 :
    (173440799508051039/250000000000000000000000:ℝ) ≤ ∫ x in (205/512:ℝ)..(103/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-5886862690187487516232156083/195312500000000000000000000000:ℝ)*(thetaPowerMass 3 (205/512:ℝ) (103/256:ℝ)-(22485952682885662245/56156474985950039552:ℝ)*thetaPowerMass 2 (205/512:ℝ) (103/256:ℝ)) ≤
      thetaFirstModeFirst (22485952682885662245/56156474985950039552:ℝ)*(thetaPowerMass 3 (205/512:ℝ) (103/256:ℝ)-(22485952682885662245/56156474985950039552:ℝ)*thetaPowerMass 2 (205/512:ℝ) (103/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0312.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (205/512:ℝ) (103/256:ℝ)
    (22485952682885662245/56156474985950039552:ℝ) (223344831929/100000000000000:ℝ) (-5886862690187487516232156083/195312500000000000000000000000:ℝ) (169163010199648404157571/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_205
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0617).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_205 :
    (∫ x in (205/512:ℝ)..(103/256:ℝ), x^2*thetaFirstMode x) ≤ (693765919010209699/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (205/512:ℝ) (103/256:ℝ)
    (44684381643/20000000000000:ℝ) (217598630551/100000000000000:ℝ) (169163010199648404157571/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_205 (thetaFirstMode_refined_node_0613).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_206 :
    (1091579309761627/1600000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(207/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1441388781320946589070937/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (103/256:ℝ) (207/512:ℝ)-(207/512:ℝ)*thetaPowerMass 2 (103/256:ℝ) (207/512:ℝ)) ≤
      thetaFirstModeFirst (207/512:ℝ)*(thetaPowerMass 3 (103/256:ℝ) (207/512:ℝ)-(207/512:ℝ)*thetaPowerMass 2 (103/256:ℝ) (207/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0314.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (103/256:ℝ) (207/512:ℝ)
    (207/512:ℝ) (211903940763/100000000000000:ℝ) (-1441388781320946589070937/50000000000000000000000000:ℝ) (332403414418076337135631/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_206
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0619).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_206 :
    (∫ x in (103/256:ℝ)..(207/512:ℝ), x^2*thetaFirstMode x) ≤ (136447839130085397/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (103/256:ℝ) (207/512:ℝ)
    (217598630551/100000000000000:ℝ) (52976104109/25000000000000:ℝ) (332403414418076337135631/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_206 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0619).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_207 :
    (670797797117209609/1000000000000000000000000:ℝ) ≤ ∫ x in (207/512:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x := by
  have hd : (-180121801082870474100554348559/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (207/512:ℝ) (13/32:ℝ)-(122695115016799804743/303458889196134300160:ℝ)*thetaPowerMass 2 (207/512:ℝ) (13/32:ℝ)) ≤
      thetaFirstModeFirst (122695115016799804743/303458889196134300160:ℝ)*(thetaPowerMass 3 (207/512:ℝ) (13/32:ℝ)-(122695115016799804743/303458889196134300160:ℝ)*thetaPowerMass 2 (207/512:ℝ) (13/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0315.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (207/512:ℝ) (13/32:ℝ)
    (122695115016799804743/303458889196134300160:ℝ) (211831426291/100000000000000:ℝ) (-180121801082870474100554348559/6250000000000000000000000000000:ℝ) (326547680306461325909969/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_207
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0623).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_207 :
    (∫ x in (207/512:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x) ≤ (26832018996817703/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (207/512:ℝ) (13/32:ℝ)
    (52976104109/25000000000000:ℝ) (206337006571/100000000000000:ℝ) (326547680306461325909969/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_207 (thetaFirstMode_refined_node_0619).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_208 :
    (329724858126887727/500000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(209/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-43050241740776315862587/1562500000000000000000000:ℝ)*(thetaPowerMass 3 (13/32:ℝ) (209/512:ℝ)-(209/512:ℝ)*thetaPowerMass 2 (13/32:ℝ) (209/512:ℝ)) ≤
      thetaFirstModeFirst (209/512:ℝ)*(thetaPowerMass 3 (13/32:ℝ) (209/512:ℝ)-(209/512:ℝ)*thetaPowerMass 2 (13/32:ℝ) (209/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0317.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (13/32:ℝ) (209/512:ℝ)
    (209/512:ℝ) (6277928521/3125000000000:ℝ) (-43050241740776315862587/1562500000000000000000000:ℝ) (160379411427857512154149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_208
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0625).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_208 :
    (∫ x in (13/32:ℝ)..(209/512:ℝ), x^2*thetaFirstMode x) ≤ (82431475201670147/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (13/32:ℝ) (209/512:ℝ)
    (206337006571/100000000000000:ℝ) (200894167167/100000000000000:ℝ) (160379411427857512154149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_208 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0625).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_209 :
    (324096252276866241/500000000000000000000000:ℝ) ≤ ∫ x in (209/512:ℝ)..(105/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-344302932232714622490896993499/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (209/512:ℝ) (105/256:ℝ)-(133785307673187732441/327721993105999567360:ℝ)*thetaPowerMass 2 (209/512:ℝ) (105/256:ℝ)) ≤
      thetaFirstModeFirst (133785307673187732441/327721993105999567360:ℝ)*(thetaPowerMass 3 (209/512:ℝ) (105/256:ℝ)-(133785307673187732441/327721993105999567360:ℝ)*thetaPowerMass 2 (209/512:ℝ) (105/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0318.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (209/512:ℝ) (105/256:ℝ)
    (133785307673187732441/327721993105999567360:ℝ) (200825070001/100000000000000:ℝ) (-344302932232714622490896993499/12500000000000000000000000000000:ℝ) (78759207614849840720043/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_209
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0629).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_209 :
    (∫ x in (209/512:ℝ)..(105/256:ℝ), x^2*thetaFirstMode x) ≤ (81024392308292637/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (209/512:ℝ) (105/256:ℝ)
    (200894167167/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (78759207614849840720043/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_209 (thetaFirstMode_refined_node_0625).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_210 :
    (637030323417505151/1000000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(211/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-131607490515433995560369/5000000000000000000000000:ℝ)*(thetaPowerMass 3 (105/256:ℝ) (211/512:ℝ)-(211/512:ℝ)*thetaPowerMass 2 (105/256:ℝ) (211/512:ℝ)) ≤
      thetaFirstModeFirst (211/512:ℝ)*(thetaPowerMass 3 (105/256:ℝ) (211/512:ℝ)-(211/512:ℝ)*thetaPowerMass 2 (105/256:ℝ) (211/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0320.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (105/256:ℝ) (211/512:ℝ)
    (211/512:ℝ) (38074591613/20000000000000:ℝ) (-131607490515433995560369/5000000000000000000000000:ℝ) (38672709412707373928059/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_210
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0631).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_210 :
    (∫ x in (105/256:ℝ)..(211/512:ℝ), x^2*thetaFirstMode x) ≤ (127406473359570953/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (105/256:ℝ) (211/512:ℝ)
    (97786844973/50000000000000:ℝ) (23796674017/12500000000000:ℝ) (38672709412707373928059/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_210 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0631).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_211 :
    (625962697824976417/1000000000000000000000000:ℝ) ≤ ∫ x in (211/512:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-657848293661949787266058245451/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (211/512:ℝ) (53/128:ℝ)-(145757762788870993959/353665902141891765760:ℝ)*thetaPowerMass 2 (211/512:ℝ) (53/128:ℝ)) ≤
      thetaFirstModeFirst (145757762788870993959/353665902141891765760:ℝ)*(thetaPowerMass 3 (211/512:ℝ) (53/128:ℝ)-(145757762788870993959/353665902141891765760:ℝ)*thetaPowerMass 2 (211/512:ℝ) (53/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0321.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (211/512:ℝ) (53/128:ℝ)
    (145757762788870993959/353665902141891765760:ℝ) (95154001427/50000000000000:ℝ) (-657848293661949787266058245451/25000000000000000000000000000000:ℝ) (151896656769668924807039/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_211
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0635).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_211 :
    (∫ x in (211/512:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x) ≤ (625965287184933791/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (211/512:ℝ) (53/128:ℝ)
    (23796674017/12500000000000:ℝ) (92645558231/50000000000000:ℝ) (151896656769668924807039/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_211 (thetaFirstMode_refined_node_0631).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_212 :
    (614993619004012983/1000000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(213/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-125673807826113142827569/5000000000000000000000000:ℝ)*(thetaPowerMass 3 (53/128:ℝ) (213/512:ℝ)-(213/512:ℝ)*thetaPowerMass 2 (53/128:ℝ) (213/512:ℝ)) ≤
      thetaFirstModeFirst (213/512:ℝ)*(thetaPowerMass 3 (53/128:ℝ) (213/512:ℝ)-(213/512:ℝ)*thetaPowerMass 2 (53/128:ℝ) (213/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0323.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (53/128:ℝ) (213/512:ℝ)
    (213/512:ℝ) (90162158371/50000000000000:ℝ) (-125673807826113142827569/5000000000000000000000000:ℝ) (59654337099177772698799/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_212
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0637).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_212 :
    (∫ x in (53/128:ℝ)..(213/512:ℝ), x^2*thetaFirstMode x) ≤ (614995620170850103/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (53/128:ℝ) (213/512:ℝ)
    (92645558231/50000000000000:ℝ) (90162365563/50000000000000:ℝ) (59654337099177772698799/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_212 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0637).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_213 :
    (604122462808435203/1000000000000000000000000:ℝ) ≤ ∫ x in (213/512:ℝ)..(107/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-628188395966882458476796945611/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (213/512:ℝ) (107/256:ℝ)-(158673294672040530657/381389448748703772160:ℝ)*thetaPowerMass 2 (213/512:ℝ) (107/256:ℝ)) ≤
      thetaFirstModeFirst (158673294672040530657/381389448748703772160:ℝ)*(thetaPowerMass 3 (213/512:ℝ) (107/256:ℝ)-(158673294672040530657/381389448748703772160:ℝ)*thetaPowerMass 2 (213/512:ℝ) (107/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0324.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (213/512:ℝ) (107/256:ℝ)
    (158673294672040530657/381389448748703772160:ℝ) (90131436197/50000000000000:ℝ) (-628188395966882458476796945611/25000000000000000000000000000000:ℝ) (292816715856159756349177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_213
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0641).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_213 :
    (∫ x in (213/512:ℝ)..(107/256:ℝ), x^2*thetaFirstMode x) ≤ (302062503506743813/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (213/512:ℝ) (107/256:ℝ)
    (90162365563/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (292816715856159756349177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_213 (thetaFirstMode_refined_node_0637).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_214 :
    (37084565730822917/62500000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(215/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-149943140548005677139231/6250000000000000000000000:ℝ)*(thetaPowerMass 3 (107/256:ℝ) (215/512:ℝ)-(215/512:ℝ)*thetaPowerMass 2 (107/256:ℝ) (215/512:ℝ)) ≤
      thetaFirstModeFirst (215/512:ℝ)*(thetaPowerMass 3 (107/256:ℝ) (215/512:ℝ)-(215/512:ℝ)*thetaPowerMass 2 (107/256:ℝ) (215/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0326.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (107/256:ℝ) (215/512:ℝ)
    (215/512:ℝ) (42682709031/25000000000000:ℝ) (-149943140548005677139231/6250000000000000000000000:ℝ) (3592853923256872964007/12500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_214
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0643).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_214 :
    (∫ x in (107/256:ℝ)..(215/512:ℝ), x^2*thetaFirstMode x) ≤ (593355010459659563/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (107/256:ℝ) (215/512:ℝ)
    (17547212979/10000000000000:ℝ) (8536561577/5000000000000:ℝ) (3592853923256872964007/12500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_214 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0643).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_215 :
    (116536923408797501/200000000000000000000000:ℝ) ≤ ∫ x in (215/512:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (215/512:ℝ) (27/64:ℝ)-(34519255196979847635/82199252318350141952:ℝ)*thetaPowerMass 2 (215/512:ℝ) (27/64:ℝ)) ≤
      thetaFirstModeFirst (34519255196979847635/82199252318350141952:ℝ)*(thetaPowerMass 3 (215/512:ℝ) (27/64:ℝ)-(34519255196979847635/82199252318350141952:ℝ)*thetaPowerMass 2 (215/512:ℝ) (27/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0327.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (215/512:ℝ) (27/64:ℝ)
    (34519255196979847635/82199252318350141952:ℝ) (170672733493/100000000000000:ℝ) (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ) (282106373519129414186399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_215
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0647).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_215 :
    (∫ x in (215/512:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x) ≤ (145671778887207743/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (215/512:ℝ) (27/64:ℝ)
    (8536561577/5000000000000:ℝ) (20762497607/12500000000000:ℝ) (282106373519129414186399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_215 (thetaFirstMode_refined_node_0643).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_216 :
    (71515101779585713/125000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(217/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-114444404248090926647781/5000000000000000000000000:ℝ)*(thetaPowerMass 3 (27/64:ℝ) (217/512:ℝ)-(217/512:ℝ)*thetaPowerMass 2 (27/64:ℝ) (217/512:ℝ)) ≤
      thetaFirstModeFirst (217/512:ℝ)*(thetaPowerMass 3 (27/64:ℝ) (217/512:ℝ)-(217/512:ℝ)*thetaPowerMass 2 (27/64:ℝ) (217/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0329.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (27/64:ℝ) (217/512:ℝ)
    (217/512:ℝ) (80787985213/50000000000000:ℝ) (-114444404248090926647781/5000000000000000000000000:ℝ) (55370154762726230771913/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_216
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0649).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_216 :
    (∫ x in (27/64:ℝ)..(217/512:ℝ), x^2*thetaFirstMode x) ≤ (572122730462058579/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (27/64:ℝ) (217/512:ℝ)
    (20762497607/12500000000000:ℝ) (161576347573/100000000000000:ℝ) (55370154762726230771913/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_216 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0649).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_217 :
    (70207591883645077/125000000000000000000000:ℝ) ≤ ∫ x in (217/512:ℝ)..(109/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-22882298452005075002291703247/1000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (217/512:ℝ) (109/256:ℝ)-(187594809587397482193/442594949984965788160:ℝ)*thetaPowerMass 2 (217/512:ℝ) (109/256:ℝ)) ≤
      thetaFirstModeFirst (187594809587397482193/442594949984965788160:ℝ)*(thetaPowerMass 3 (217/512:ℝ) (109/256:ℝ)-(187594809587397482193/442594949984965788160:ℝ)*thetaPowerMass 2 (217/512:ℝ) (109/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0330.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (217/512:ℝ) (109/256:ℝ)
    (187594809587397482193/442594949984965788160:ℝ) (161521047537/100000000000000:ℝ) (-22882298452005075002291703247/1000000000000000000000000000000:ℝ) (135830689454414892203241/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_217
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0653).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_217 :
    (∫ x in (217/512:ℝ)..(109/256:ℝ), x^2*thetaFirstMode x) ≤ (22466527495431097/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (217/512:ℝ) (109/256:ℝ)
    (161576347573/100000000000000:ℝ) (157158326831/100000000000000:ℝ) (135830689454414892203241/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_217 (thetaFirstMode_refined_node_0649).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_218 :
    (137826967449684563/250000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(219/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-54569150436434823947043/2500000000000000000000000:ℝ)*(thetaPowerMass 3 (109/256:ℝ) (219/512:ℝ)-(219/512:ℝ)*thetaPowerMass 2 (109/256:ℝ) (219/512:ℝ)) ≤
      thetaFirstModeFirst (219/512:ℝ)*(thetaPowerMass 3 (109/256:ℝ) (219/512:ℝ)-(219/512:ℝ)*thetaPowerMass 2 (109/256:ℝ) (219/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0332.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (109/256:ℝ) (219/512:ℝ)
    (219/512:ℝ) (7642178973/5000000000000:ℝ) (-54569150436434823947043/2500000000000000000000000:ℝ) (33317254796652589707933/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_218
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0655).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_218 :
    (∫ x in (109/256:ℝ)..(219/512:ℝ), x^2*thetaFirstMode x) ≤ (275654871700265923/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (109/256:ℝ) (219/512:ℝ)
    (157158326831/100000000000000:ℝ) (152843939023/100000000000000:ℝ) (33317254796652589707933/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_218 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0655).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_219 :
    (67632646964633487/125000000000000000000000:ℝ) ≤ ∫ x in (219/512:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-681918162937633043325755199/31250000000000000000000000000:ℝ)*(thetaPowerMass 3 (219/512:ℝ) (55/128:ℝ)-(203740906957094489391/476299293587687964160:ℝ)*thetaPowerMass 2 (219/512:ℝ) (55/128:ℝ)) ≤
      thetaFirstModeFirst (203740906957094489391/476299293587687964160:ℝ)*(thetaPowerMass 3 (219/512:ℝ) (55/128:ℝ)-(203740906957094489391/476299293587687964160:ℝ)*thetaPowerMass 2 (219/512:ℝ) (55/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0333.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (219/512:ℝ) (55/128:ℝ)
    (203740906957094489391/476299293587687964160:ℝ) (152791681241/100000000000000:ℝ) (-681918162937633043325755199/31250000000000000000000000000:ℝ) (3268507342467591650561/12500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_219
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0659).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_219 :
    (∫ x in (219/512:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x) ≤ (541063581409157919/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (219/512:ℝ) (55/128:ℝ)
    (152843939023/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (3268507342467591650561/12500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_219 (thetaFirstMode_refined_node_0655).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_220 :
    (530923980152779251/1000000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(221/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-65019401425270190145807/3125000000000000000000000:ℝ)*(thetaPowerMass 3 (55/128:ℝ) (221/512:ℝ)-(221/512:ℝ)*thetaPowerMass 2 (55/128:ℝ) (221/512:ℝ)) ≤
      thetaFirstModeFirst (221/512:ℝ)*(thetaPowerMass 3 (55/128:ℝ) (221/512:ℝ)-(221/512:ℝ)*thetaPowerMass 2 (55/128:ℝ) (221/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0335.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (55/128:ℝ) (221/512:ℝ)
    (221/512:ℝ) (36129481767/25000000000000:ℝ) (-65019401425270190145807/3125000000000000000000000:ℝ) (128244423508421206272841/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_220
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0661).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_220 :
    (∫ x in (55/128:ℝ)..(221/512:ℝ), x^2*thetaFirstMode x) ≤ (265462905544643079/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (55/128:ℝ) (221/512:ℝ)
    (148631229741/100000000000000:ℝ) (9032391857/6250000000000:ℝ) (128244423508421206272841/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_220 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0661).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_221 :
    (260447555585386483/500000000000000000000000:ℝ) ≤ ∫ x in (221/512:ℝ)..(111/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (221/512:ℝ) (111/256:ℝ)-(221110673372114090409/512228437469441512960:ℝ)*thetaPowerMass 2 (221/512:ℝ) (111/256:ℝ)) ≤
      thetaFirstModeFirst (221110673372114090409/512228437469441512960:ℝ)*(thetaPowerMass 3 (221/512:ℝ) (111/256:ℝ)-(221110673372114090409/512228437469441512960:ℝ)*thetaPowerMass 2 (221/512:ℝ) (111/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0336.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (221/512:ℝ) (111/256:ℝ)
    (221110673372114090409/512228437469441512960:ℝ) (72234452543/50000000000000:ℝ) (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ) (251562624344124832607773/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_221
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0665).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_221 :
    (∫ x in (221/512:ℝ)..(111/256:ℝ), x^2*thetaFirstMode x) ≤ (52089746986133627/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (221/512:ℝ) (111/256:ℝ)
    (9032391857/6250000000000:ℝ) (17562894341/12500000000000:ℝ) (251562624344124832607773/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_221 (thetaFirstMode_refined_node_0661).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_222 :
    (20439109424453817/40000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(223/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-247793738206430294024529/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (111/256:ℝ) (223/512:ℝ)-(223/512:ℝ)*thetaPowerMass 2 (111/256:ℝ) (223/512:ℝ)) ≤
      thetaFirstModeFirst (223/512:ℝ)*(thetaPowerMass 3 (111/256:ℝ) (223/512:ℝ)-(223/512:ℝ)*thetaPowerMass 2 (111/256:ℝ) (223/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0338.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (111/256:ℝ) (223/512:ℝ)
    (223/512:ℝ) (68291839601/50000000000000:ℝ) (-247793738206430294024529/12500000000000000000000000:ℝ) (61675428197927839744517/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_222
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0667).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_222 :
    (∫ x in (111/256:ℝ)..(223/512:ℝ), x^2*thetaFirstMode x) ≤ (510979523884723391/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (111/256:ℝ) (223/512:ℝ)
    (17562894341/12500000000000:ℝ) (68292002787/50000000000000:ℝ) (61675428197927839744517/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_222 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0667).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_223 :
    (250585278858784701/500000000000000000000000:ℝ) ≤ ∫ x in (223/512:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x := by
  have hd : (-99088961506408080648845019957/5000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (223/512:ℝ) (7/16:ℝ)-(239784500047674155607/550507092643036572160:ℝ)*thetaPowerMass 2 (223/512:ℝ) (7/16:ℝ)) ≤
      thetaFirstModeFirst (239784500047674155607/550507092643036572160:ℝ)*(thetaPowerMass 3 (223/512:ℝ) (7/16:ℝ)-(239784500047674155607/550507092643036572160:ℝ)*thetaPowerMass 2 (223/512:ℝ) (7/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0339.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (223/512:ℝ) (7/16:ℝ)
    (239784500047674155607/550507092643036572160:ℝ) (68268695707/50000000000000:ℝ) (-99088961506408080648845019957/5000000000000000000000000000000:ℝ) (120952946156479495543801/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_223
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0671).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_223 :
    (∫ x in (223/512:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x) ≤ (250586434539623469/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (223/512:ℝ) (7/16:ℝ)
    (68292002787/50000000000000:ℝ) (132758967949/100000000000000:ℝ) (120952946156479495543801/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_223 (thetaFirstMode_refined_node_0667).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

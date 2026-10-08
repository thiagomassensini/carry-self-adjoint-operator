import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature06
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative09
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative10

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_6_192 :
    (67981496039307/4000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(193/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-122199074708781032214327/3125000000000000000000000:ℝ)*(thetaPowerMass 7 (3/8:ℝ) (193/512:ℝ)-(193/512:ℝ)*thetaPowerMass 6 (3/8:ℝ) (193/512:ℝ)) ≤
      thetaFirstModeFirst (193/512:ℝ)*(thetaPowerMass 7 (3/8:ℝ) (193/512:ℝ)-(193/512:ℝ)*thetaPowerMass 6 (3/8:ℝ) (193/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0293.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (3/8:ℝ) (193/512:ℝ)
    (193/512:ℝ) (304224667353/100000000000000:ℝ) (-122199074708781032214327/3125000000000000000000000:ℝ) (421372198150856993365933/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_192
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0577).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_192 :
    (∫ x in (3/8:ℝ)..(193/512:ℝ), x^6*thetaFirstMode x) ≤ (4248855513108729/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/8:ℝ) (193/512:ℝ)
    (311943577261/100000000000000:ℝ) (475352053/156250000000:ℝ) (421372198150856993365933/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_192 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0577).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_193 :
    (34194715342139/2000000000000000000000:ℝ) ≤ ∫ x in (193/512:ℝ)..(97/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-244327697043121646172975414807/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (193/512:ℝ) (97/256:ℝ)-(65332341813084493257/173304480845017500160:ℝ)*thetaPowerMass 6 (193/512:ℝ) (97/256:ℝ)) ≤
      thetaFirstModeFirst (65332341813084493257/173304480845017500160:ℝ)*(thetaPowerMass 7 (193/512:ℝ) (97/256:ℝ)-(65332341813084493257/173304480845017500160:ℝ)*thetaPowerMass 6 (193/512:ℝ) (97/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0294.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (193/512:ℝ) (97/256:ℝ)
    (65332341813084493257/173304480845017500160:ℝ) (12164766849/4000000000000:ℝ) (-244327697043121646172975414807/6250000000000000000000000000000:ℝ) (82917690064399091062251/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_193
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0581).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_193 :
    (∫ x in (193/512:ℝ)..(97/256:ℝ), x^6*thetaFirstMode x) ≤ (17097418175376049/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (193/512:ℝ) (97/256:ℝ)
    (475352053/156250000000:ℝ) (296667793723/100000000000000:ℝ) (82917690064399091062251/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_193 (thetaFirstMode_refined_node_0577).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_194 :
    (17195465778098747/1000000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(195/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-366056393134101133031/9765625000000000000000:ℝ)*(thetaPowerMass 7 (97/256:ℝ) (195/512:ℝ)-(195/512:ℝ)*thetaPowerMass 6 (97/256:ℝ) (195/512:ℝ)) ≤
      thetaFirstModeFirst (195/512:ℝ)*(thetaPowerMass 7 (97/256:ℝ) (195/512:ℝ)-(195/512:ℝ)*thetaPowerMass 6 (97/256:ℝ) (195/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0296.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (97/256:ℝ) (195/512:ℝ)
    (195/512:ℝ) (56497619/19531250000:ℝ) (-366056393134101133031/9765625000000000000000:ℝ) (407869947363270890347949/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_194
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0583).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_194 :
    (∫ x in (97/256:ℝ)..(195/512:ℝ), x^6*thetaFirstMode x) ≤ (17195515054004241/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (97/256:ℝ) (195/512:ℝ)
    (296667793723/100000000000000:ℝ) (289268428881/100000000000000:ℝ) (407869947363270890347949/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_194 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0583).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_195 :
    (17289597974130973/1000000000000000000000000:ℝ) ≤ ∫ x in (195/512:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-29276075031654577887586844773/781250000000000000000000000000:ℝ)*(thetaPowerMass 7 (195/512:ℝ) (49/128:ℝ)-(14336762398671353355/37640552179499351552:ℝ)*thetaPowerMass 6 (195/512:ℝ) (49/128:ℝ)) ≤
      thetaFirstModeFirst (14336762398671353355/37640552179499351552:ℝ)*(thetaPowerMass 7 (195/512:ℝ) (49/128:ℝ)-(14336762398671353355/37640552179499351552:ℝ)*thetaPowerMass 6 (195/512:ℝ) (49/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0297.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (195/512:ℝ) (49/128:ℝ)
    (14336762398671353355/37640552179499351552:ℝ) (72291929829/25000000000000:ℝ) (-29276075031654577887586844773/781250000000000000000000000000:ℝ) (200608460632174198657677/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_195
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0587).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_195 :
    (∫ x in (195/512:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x) ≤ (1080603763600423/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (195/512:ℝ) (49/128:ℝ)
    (289268428881/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (200608460632174198657677/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_195 (thetaFirstMode_refined_node_0583).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_196 :
    (17379753407939869/1000000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(197/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1795843883699179309941067/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (49/128:ℝ) (197/512:ℝ)-(197/512:ℝ)*thetaPowerMass 6 (49/128:ℝ) (197/512:ℝ)) ≤
      thetaFirstModeFirst (197/512:ℝ)*(thetaPowerMass 7 (49/128:ℝ) (197/512:ℝ)-(197/512:ℝ)*thetaPowerMass 6 (49/128:ℝ) (197/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0299.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (49/128:ℝ) (197/512:ℝ)
    (197/512:ℝ) (274933345111/100000000000000:ℝ) (-1795843883699179309941067/50000000000000000000000000:ℝ) (394629585759214226027709/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_196
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0589).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_196 :
    (∫ x in (49/128:ℝ)..(197/512:ℝ), x^6*thetaFirstMode x) ≤ (3475960779967541/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (49/128:ℝ) (197/512:ℝ)
    (282024656491/100000000000000:ℝ) (274933938627/100000000000000:ℝ) (394629585759214226027709/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_196 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0589).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_197 :
    (8732917551811393/500000000000000000000000:ℝ) ≤ ∫ x in (197/512:ℝ)..(99/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (197/512:ℝ) (99/256:ℝ)-(78578341309131839793/204209882504936988160:ℝ)*thetaPowerMass 6 (197/512:ℝ) (99/256:ℝ)) ≤
      thetaFirstModeFirst (78578341309131839793/204209882504936988160:ℝ)*(thetaPowerMass 7 (197/512:ℝ) (99/256:ℝ)-(78578341309131839793/204209882504936988160:ℝ)*thetaPowerMass 6 (197/512:ℝ) (99/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0300.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (197/512:ℝ) (99/256:ℝ)
    (78578341309131839793/204209882504936988160:ℝ) (274838413521/100000000000000:ℝ) (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ) (194054068215068659549999/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_197
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0593).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_197 :
    (∫ x in (197/512:ℝ)..(99/256:ℝ), x^6*thetaFirstMode x) ≤ (8732949537636849/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (197/512:ℝ) (99/256:ℝ)
    (274933938627/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (194054068215068659549999/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_197 (thetaFirstMode_refined_node_0589).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_198 :
    (1096740612785343/62500000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(199/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-430009833253962321035977/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (99/256:ℝ) (199/512:ℝ)-(199/512:ℝ)*thetaPowerMass 6 (99/256:ℝ) (199/512:ℝ)) ≤
      thetaFirstModeFirst (199/512:ℝ)*(thetaPowerMass 7 (99/256:ℝ) (199/512:ℝ)-(199/512:ℝ)*thetaPowerMass 6 (99/256:ℝ) (199/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0302.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (99/256:ℝ) (199/512:ℝ)
    (199/512:ℝ) (65300267963/25000000000000:ℝ) (-430009833253962321035977/12500000000000000000000000:ℝ) (190826375409226913883677/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_198
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0595).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_198 :
    (∫ x in (99/256:ℝ)..(199/512:ℝ), x^6*thetaFirstMode x) ≤ (17547901492759161/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (99/256:ℝ) (199/512:ℝ)
    (33499220303/12500000000000:ℝ) (52240328029/20000000000000:ℝ) (190826375409226913883677/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_198 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0595).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_199 :
    (17625704020368037/1000000000000000000000000:ℝ) ≤ ∫ x in (199/512:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-429886080618259761215196442893/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (199/512:ℝ) (25/64:ℝ)-(86056132492075958991/221395846441879298560:ℝ)*thetaPowerMass 6 (199/512:ℝ) (25/64:ℝ)) ≤
      thetaFirstModeFirst (86056132492075958991/221395846441879298560:ℝ)*(thetaPowerMass 7 (199/512:ℝ) (25/64:ℝ)-(86056132492075958991/221395846441879298560:ℝ)*thetaPowerMass 6 (199/512:ℝ) (25/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0303.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (199/512:ℝ) (25/64:ℝ)
    (86056132492075958991/221395846441879298560:ℝ) (261111060999/100000000000000:ℝ) (-429886080618259761215196442893/12500000000000000000000000000000:ℝ) (375263588556175193661479/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_199
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0599).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_199 :
    (∫ x in (199/512:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x) ≤ (8812884853050527/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (199/512:ℝ) (25/64:ℝ)
    (52240328029/20000000000000:ℝ) (12727755463/5000000000000:ℝ) (375263588556175193661479/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_199 (thetaFirstMode_refined_node_0595).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_200 :
    (8849706119532381/500000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(201/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-32934869486208662412563/1000000000000000000000000:ℝ)*(thetaPowerMass 7 (25/64:ℝ) (201/512:ℝ)-(201/512:ℝ)*thetaPowerMass 6 (25/64:ℝ) (201/512:ℝ)) ≤
      thetaFirstModeFirst (201/512:ℝ)*(thetaPowerMass 7 (25/64:ℝ) (201/512:ℝ)-(201/512:ℝ)*thetaPowerMass 6 (25/64:ℝ) (201/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0305.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (25/64:ℝ) (201/512:ℝ)
    (201/512:ℝ) (248051188579/100000000000000:ℝ) (-32934869486208662412563/1000000000000000000000000:ℝ) (368940791481683951042041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_200
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0601).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_200 :
    (∫ x in (25/64:ℝ)..(201/512:ℝ), x^6*thetaFirstMode x) ≤ (8849732550858923/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (25/64:ℝ) (201/512:ℝ)
    (12727755463/5000000000000:ℝ) (15503233281/6250000000000:ℝ) (368940791481683951042041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_200 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0601).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_201 :
    (2221110567532201/125000000000000000000000:ℝ) ≤ ∫ x in (201/512:ℝ)..(101/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (201/512:ℝ) (101/256:ℝ)-(94159912870084059009/239834298071963906560:ℝ)*thetaPowerMass 6 (201/512:ℝ) (101/256:ℝ)) ≤
      thetaFirstModeFirst (94159912870084059009/239834298071963906560:ℝ)*(thetaPowerMass 7 (201/512:ℝ) (101/256:ℝ)-(94159912870084059009/239834298071963906560:ℝ)*thetaPowerMass 6 (201/512:ℝ) (101/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0306.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (201/512:ℝ) (101/256:ℝ)
    (94159912870084059009/239834298071963906560:ℝ) (247965870591/100000000000000:ℝ) (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ) (181342241891124615302757/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_201
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0605).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_201 :
    (∫ x in (201/512:ℝ)..(101/256:ℝ), x^6*thetaFirstMode x) ≤ (8884475961552419/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (201/512:ℝ) (101/256:ℝ)
    (15503233281/6250000000000:ℝ) (30211137237/12500000000000:ℝ) (181342241891124615302757/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_201 (thetaFirstMode_refined_node_0601).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_202 :
    (4458535819975673/250000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(203/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1575904465507159884915987/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (101/256:ℝ) (203/512:ℝ)-(203/512:ℝ)*thetaPowerMass 6 (101/256:ℝ) (203/512:ℝ)) ≤
      thetaFirstModeFirst (203/512:ℝ)*(thetaPowerMass 7 (101/256:ℝ) (203/512:ℝ)-(203/512:ℝ)*thetaPowerMass 6 (101/256:ℝ) (203/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0308.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (101/256:ℝ) (203/512:ℝ)
    (203/512:ℝ) (235464298503/100000000000000:ℝ) (-1575904465507159884915987/50000000000000000000000000:ℝ) (356494772124939210200983/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_202
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0607).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_202 :
    (∫ x in (101/256:ℝ)..(203/512:ℝ), x^6*thetaFirstMode x) ≤ (17834197292789919/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (101/256:ℝ) (203/512:ℝ)
    (30211137237/12500000000000:ℝ) (235464818869/100000000000000:ℝ) (356494772124939210200983/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_202 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0607).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_203 :
    (2236887771403141/125000000000000000000000:ℝ) ≤ ∫ x in (203/512:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-393862812547991790702588742107/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (203/512:ℝ) (51/128:ℝ)-(102935065125197358207/259602677601152028160:ℝ)*thetaPowerMass 6 (203/512:ℝ) (51/128:ℝ)) ≤
      thetaFirstModeFirst (102935065125197358207/259602677601152028160:ℝ)*(thetaPowerMass 7 (203/512:ℝ) (51/128:ℝ)-(102935065125197358207/259602677601152028160:ℝ)*thetaPowerMass 6 (203/512:ℝ) (51/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0309.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (203/512:ℝ) (51/128:ℝ)
    (102935065125197358207/259602677601152028160:ℝ) (2353834549/1000000000000:ℝ) (-393862812547991790702588742107/12500000000000000000000000000000:ℝ) (875929364510965849653/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_203
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0611).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_203 :
    (∫ x in (203/512:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x) ≤ (3579034246189553/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (203/512:ℝ) (51/128:ℝ)
    (235464818869/100000000000000:ℝ) (9175061369/4000000000000:ℝ) (875929364510965849653/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_203 (thetaFirstMode_refined_node_0607).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_204 :
    (4487947883614427/250000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(205/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1507470284078181177087227/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (51/128:ℝ) (205/512:ℝ)-(205/512:ℝ)*thetaPowerMass 6 (51/128:ℝ) (205/512:ℝ)) ≤
      thetaFirstModeFirst (205/512:ℝ)*(thetaPowerMass 7 (51/128:ℝ) (205/512:ℝ)-(205/512:ℝ)*thetaPowerMass 6 (51/128:ℝ) (205/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0311.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (51/128:ℝ) (205/512:ℝ)
    (205/512:ℝ) (223421410591/100000000000000:ℝ) (-1507470284078181177087227/50000000000000000000000000:ℝ) (172157738447815749517883/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_204
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0613).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_204 :
    (∫ x in (51/128:ℝ)..(205/512:ℝ), x^6*thetaFirstMode x) ≤ (17951846671142743/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (51/128:ℝ) (205/512:ℝ)
    (9175061369/4000000000000:ℝ) (44684381643/20000000000000:ℝ) (172157738447815749517883/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_204 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0613).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_205 :
    (3600825751937207/200000000000000000000000:ℝ) ≤ ∫ x in (205/512:ℝ)..(103/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-5886862690187487516232156083/195312500000000000000000000000:ℝ)*(thetaPowerMass 7 (205/512:ℝ) (103/256:ℝ)-(22485952682885662245/56156474985950039552:ℝ)*thetaPowerMass 6 (205/512:ℝ) (103/256:ℝ)) ≤
      thetaFirstModeFirst (22485952682885662245/56156474985950039552:ℝ)*(thetaPowerMass 7 (205/512:ℝ) (103/256:ℝ)-(22485952682885662245/56156474985950039552:ℝ)*thetaPowerMass 6 (205/512:ℝ) (103/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0312.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (205/512:ℝ) (103/256:ℝ)
    (22485952682885662245/56156474985950039552:ℝ) (223344831929/100000000000000:ℝ) (-5886862690187487516232156083/195312500000000000000000000000:ℝ) (169163010199648404157571/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_205
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0617).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_205 :
    (∫ x in (205/512:ℝ)..(103/256:ℝ), x^6*thetaFirstMode x) ≤ (9002099736504099/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (205/512:ℝ) (103/256:ℝ)
    (44684381643/20000000000000:ℝ) (217598630551/100000000000000:ℝ) (169163010199648404157571/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_205 (thetaFirstMode_refined_node_0613).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_206 :
    (18052152200121531/1000000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(207/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1441388781320946589070937/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (103/256:ℝ) (207/512:ℝ)-(207/512:ℝ)*thetaPowerMass 6 (103/256:ℝ) (207/512:ℝ)) ≤
      thetaFirstModeFirst (207/512:ℝ)*(thetaPowerMass 7 (103/256:ℝ) (207/512:ℝ)-(207/512:ℝ)*thetaPowerMass 6 (103/256:ℝ) (207/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0314.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (103/256:ℝ) (207/512:ℝ)
    (207/512:ℝ) (211903940763/100000000000000:ℝ) (-1441388781320946589070937/50000000000000000000000000:ℝ) (332403414418076337135631/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_206
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0619).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_206 :
    (∫ x in (103/256:ℝ)..(207/512:ℝ), x^6*thetaFirstMode x) ≤ (2256526054008177/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (103/256:ℝ) (207/512:ℝ)
    (217598630551/100000000000000:ℝ) (52976104109/25000000000000:ℝ) (332403414418076337135631/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_206 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0619).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_207 :
    (565493217063243/31250000000000000000000:ℝ) ≤ ∫ x in (207/512:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x := by
  have hd : (-180121801082870474100554348559/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (207/512:ℝ) (13/32:ℝ)-(122695115016799804743/303458889196134300160:ℝ)*thetaPowerMass 6 (207/512:ℝ) (13/32:ℝ)) ≤
      thetaFirstModeFirst (122695115016799804743/303458889196134300160:ℝ)*(thetaPowerMass 7 (207/512:ℝ) (13/32:ℝ)-(122695115016799804743/303458889196134300160:ℝ)*thetaPowerMass 6 (207/512:ℝ) (13/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0315.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (207/512:ℝ) (13/32:ℝ)
    (122695115016799804743/303458889196134300160:ℝ) (211831426291/100000000000000:ℝ) (-180121801082870474100554348559/6250000000000000000000000000000:ℝ) (326547680306461325909969/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_207
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0623).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_207 :
    (∫ x in (207/512:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x) ≤ (361917105731349/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (207/512:ℝ) (13/32:ℝ)
    (52976104109/25000000000000:ℝ) (206337006571/100000000000000:ℝ) (326547680306461325909969/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_207 (thetaFirstMode_refined_node_0619).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_208 :
    (18135067424702581/1000000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(209/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-43050241740776315862587/1562500000000000000000000:ℝ)*(thetaPowerMass 7 (13/32:ℝ) (209/512:ℝ)-(209/512:ℝ)*thetaPowerMass 6 (13/32:ℝ) (209/512:ℝ)) ≤
      thetaFirstModeFirst (209/512:ℝ)*(thetaPowerMass 7 (13/32:ℝ) (209/512:ℝ)-(209/512:ℝ)*thetaPowerMass 6 (13/32:ℝ) (209/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0317.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (13/32:ℝ) (209/512:ℝ)
    (209/512:ℝ) (6277928521/3125000000000:ℝ) (-43050241740776315862587/1562500000000000000000000:ℝ) (160379411427857512154149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_208
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0625).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_208 :
    (∫ x in (13/32:ℝ)..(209/512:ℝ), x^6*thetaFirstMode x) ≤ (18135124721162033/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (13/32:ℝ) (209/512:ℝ)
    (206337006571/100000000000000:ℝ) (200894167167/100000000000000:ℝ) (160379411427857512154149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_208 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0625).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_209 :
    (18169930429497457/1000000000000000000000000:ℝ) ≤ ∫ x in (209/512:ℝ)..(105/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-344302932232714622490896993499/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (209/512:ℝ) (105/256:ℝ)-(133785307673187732441/327721993105999567360:ℝ)*thetaPowerMass 6 (209/512:ℝ) (105/256:ℝ)) ≤
      thetaFirstModeFirst (133785307673187732441/327721993105999567360:ℝ)*(thetaPowerMass 7 (209/512:ℝ) (105/256:ℝ)-(133785307673187732441/327721993105999567360:ℝ)*thetaPowerMass 6 (209/512:ℝ) (105/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0318.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (209/512:ℝ) (105/256:ℝ)
    (133785307673187732441/327721993105999567360:ℝ) (200825070001/100000000000000:ℝ) (-344302932232714622490896993499/12500000000000000000000000000000:ℝ) (78759207614849840720043/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_209
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0629).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_209 :
    (∫ x in (209/512:ℝ)..(105/256:ℝ), x^6*thetaFirstMode x) ≤ (4542501091969253/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (209/512:ℝ) (105/256:ℝ)
    (200894167167/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (78759207614849840720043/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_209 (thetaFirstMode_refined_node_0625).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_210 :
    (9100213237962367/500000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(211/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-131607490515433995560369/5000000000000000000000000:ℝ)*(thetaPowerMass 7 (105/256:ℝ) (211/512:ℝ)-(211/512:ℝ)*thetaPowerMass 6 (105/256:ℝ) (211/512:ℝ)) ≤
      thetaFirstModeFirst (211/512:ℝ)*(thetaPowerMass 7 (105/256:ℝ) (211/512:ℝ)-(211/512:ℝ)*thetaPowerMass 6 (105/256:ℝ) (211/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0320.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (105/256:ℝ) (211/512:ℝ)
    (211/512:ℝ) (38074591613/20000000000000:ℝ) (-131607490515433995560369/5000000000000000000000000:ℝ) (38672709412707373928059/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_210
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0631).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_210 :
    (∫ x in (105/256:ℝ)..(211/512:ℝ), x^6*thetaFirstMode x) ≤ (18200484803984539/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (105/256:ℝ) (211/512:ℝ)
    (97786844973/50000000000000:ℝ) (23796674017/12500000000000:ℝ) (38672709412707373928059/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_210 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0631).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_211 :
    (18226484043383091/1000000000000000000000000:ℝ) ≤ ∫ x in (211/512:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-657848293661949787266058245451/25000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (211/512:ℝ) (53/128:ℝ)-(145757762788870993959/353665902141891765760:ℝ)*thetaPowerMass 6 (211/512:ℝ) (53/128:ℝ)) ≤
      thetaFirstModeFirst (145757762788870993959/353665902141891765760:ℝ)*(thetaPowerMass 7 (211/512:ℝ) (53/128:ℝ)-(145757762788870993959/353665902141891765760:ℝ)*thetaPowerMass 6 (211/512:ℝ) (53/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0321.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (211/512:ℝ) (53/128:ℝ)
    (145757762788870993959/353665902141891765760:ℝ) (95154001427/50000000000000:ℝ) (-657848293661949787266058245451/25000000000000000000000000000000:ℝ) (151896656769668924807039/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_211
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0635).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_211 :
    (∫ x in (211/512:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x) ≤ (9113279773528653/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (211/512:ℝ) (53/128:ℝ)
    (23796674017/12500000000000:ℝ) (92645558231/50000000000000:ℝ) (151896656769668924807039/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_211 (thetaFirstMode_refined_node_0631).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_212 :
    (18248165722203889/1000000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(213/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-125673807826113142827569/5000000000000000000000000:ℝ)*(thetaPowerMass 7 (53/128:ℝ) (213/512:ℝ)-(213/512:ℝ)*thetaPowerMass 6 (53/128:ℝ) (213/512:ℝ)) ≤
      thetaFirstModeFirst (213/512:ℝ)*(thetaPowerMass 7 (53/128:ℝ) (213/512:ℝ)-(213/512:ℝ)*thetaPowerMass 6 (53/128:ℝ) (213/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0323.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (53/128:ℝ) (213/512:ℝ)
    (213/512:ℝ) (90162158371/50000000000000:ℝ) (-125673807826113142827569/5000000000000000000000000:ℝ) (59654337099177772698799/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_212
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0637).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_212 :
    (∫ x in (53/128:ℝ)..(213/512:ℝ), x^6*thetaFirstMode x) ≤ (18248225047005241/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (53/128:ℝ) (213/512:ℝ)
    (92645558231/50000000000000:ℝ) (90162365563/50000000000000:ℝ) (59654337099177772698799/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_212 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0637).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_213 :
    (18265403641979141/1000000000000000000000000:ℝ) ≤ ∫ x in (213/512:ℝ)..(107/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-628188395966882458476796945611/25000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (213/512:ℝ) (107/256:ℝ)-(158673294672040530657/381389448748703772160:ℝ)*thetaPowerMass 6 (213/512:ℝ) (107/256:ℝ)) ≤
      thetaFirstModeFirst (158673294672040530657/381389448748703772160:ℝ)*(thetaPowerMass 7 (213/512:ℝ) (107/256:ℝ)-(158673294672040530657/381389448748703772160:ℝ)*thetaPowerMass 6 (213/512:ℝ) (107/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0324.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (213/512:ℝ) (107/256:ℝ)
    (158673294672040530657/381389448748703772160:ℝ) (90131436197/50000000000000:ℝ) (-628188395966882458476796945611/25000000000000000000000000000000:ℝ) (292816715856159756349177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_213
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0641).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_213 :
    (∫ x in (213/512:ℝ)..(107/256:ℝ), x^6*thetaFirstMode x) ≤ (18265480675450903/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (213/512:ℝ) (107/256:ℝ)
    (90162365563/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (292816715856159756349177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_213 (thetaFirstMode_refined_node_0637).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_214 :
    (3655653685493003/200000000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(215/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-149943140548005677139231/6250000000000000000000000:ℝ)*(thetaPowerMass 7 (107/256:ℝ) (215/512:ℝ)-(215/512:ℝ)*thetaPowerMass 6 (107/256:ℝ) (215/512:ℝ)) ≤
      thetaFirstModeFirst (215/512:ℝ)*(thetaPowerMass 7 (107/256:ℝ) (215/512:ℝ)-(215/512:ℝ)*thetaPowerMass 6 (107/256:ℝ) (215/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0326.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (107/256:ℝ) (215/512:ℝ)
    (215/512:ℝ) (42682709031/25000000000000:ℝ) (-149943140548005677139231/6250000000000000000000000:ℝ) (3592853923256872964007/12500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_214
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0643).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_214 :
    (∫ x in (107/256:ℝ)..(215/512:ℝ), x^6*thetaFirstMode x) ≤ (2284791089009667/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (107/256:ℝ) (215/512:ℝ)
    (17547212979/10000000000000:ℝ) (8536561577/5000000000000:ℝ) (3592853923256872964007/12500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_214 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0643).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_215 :
    (4571673950830469/250000000000000000000000:ℝ) ≤ ∫ x in (215/512:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (215/512:ℝ) (27/64:ℝ)-(34519255196979847635/82199252318350141952:ℝ)*thetaPowerMass 6 (215/512:ℝ) (27/64:ℝ)) ≤
      thetaFirstModeFirst (34519255196979847635/82199252318350141952:ℝ)*(thetaPowerMass 7 (215/512:ℝ) (27/64:ℝ)-(34519255196979847635/82199252318350141952:ℝ)*thetaPowerMass 6 (215/512:ℝ) (27/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0327.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (215/512:ℝ) (27/64:ℝ)
    (34519255196979847635/82199252318350141952:ℝ) (170672733493/100000000000000:ℝ) (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ) (282106373519129414186399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_215
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0647).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_215 :
    (∫ x in (215/512:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x) ≤ (71432712219173/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (215/512:ℝ) (27/64:ℝ)
    (8536561577/5000000000000:ℝ) (20762497607/12500000000000:ℝ) (282106373519129414186399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_215 (thetaFirstMode_refined_node_0643).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_216 :
    (9145382181011031/500000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(217/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-114444404248090926647781/5000000000000000000000000:ℝ)*(thetaPowerMass 7 (27/64:ℝ) (217/512:ℝ)-(217/512:ℝ)*thetaPowerMass 6 (27/64:ℝ) (217/512:ℝ)) ≤
      thetaFirstModeFirst (217/512:ℝ)*(thetaPowerMass 7 (27/64:ℝ) (217/512:ℝ)-(217/512:ℝ)*thetaPowerMass 6 (27/64:ℝ) (217/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0329.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (27/64:ℝ) (217/512:ℝ)
    (217/512:ℝ) (80787985213/50000000000000:ℝ) (-114444404248090926647781/5000000000000000000000000:ℝ) (55370154762726230771913/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_216
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0649).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_216 :
    (∫ x in (27/64:ℝ)..(217/512:ℝ), x^6*thetaFirstMode x) ≤ (3658165113497071/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (27/64:ℝ) (217/512:ℝ)
    (20762497607/12500000000000:ℝ) (161576347573/100000000000000:ℝ) (55370154762726230771913/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_216 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0649).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_217 :
    (18290413350189843/1000000000000000000000000:ℝ) ≤ ∫ x in (217/512:ℝ)..(109/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-22882298452005075002291703247/1000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (217/512:ℝ) (109/256:ℝ)-(187594809587397482193/442594949984965788160:ℝ)*thetaPowerMass 6 (217/512:ℝ) (109/256:ℝ)) ≤
      thetaFirstModeFirst (187594809587397482193/442594949984965788160:ℝ)*(thetaPowerMass 7 (217/512:ℝ) (109/256:ℝ)-(187594809587397482193/442594949984965788160:ℝ)*thetaPowerMass 6 (217/512:ℝ) (109/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0330.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (217/512:ℝ) (109/256:ℝ)
    (187594809587397482193/442594949984965788160:ℝ) (161521047537/100000000000000:ℝ) (-22882298452005075002291703247/1000000000000000000000000000000:ℝ) (135830689454414892203241/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_217
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0653).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_217 :
    (∫ x in (217/512:ℝ)..(109/256:ℝ), x^6*thetaFirstMode x) ≤ (9145246662447049/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (217/512:ℝ) (109/256:ℝ)
    (161576347573/100000000000000:ℝ) (157158326831/100000000000000:ℝ) (135830689454414892203241/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_217 (thetaFirstMode_refined_node_0649).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_218 :
    (18285729235172983/1000000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(219/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-54569150436434823947043/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (109/256:ℝ) (219/512:ℝ)-(219/512:ℝ)*thetaPowerMass 6 (109/256:ℝ) (219/512:ℝ)) ≤
      thetaFirstModeFirst (219/512:ℝ)*(thetaPowerMass 7 (109/256:ℝ) (219/512:ℝ)-(219/512:ℝ)*thetaPowerMass 6 (109/256:ℝ) (219/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0332.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (109/256:ℝ) (219/512:ℝ)
    (219/512:ℝ) (7642178973/5000000000000:ℝ) (-54569150436434823947043/2500000000000000000000000:ℝ) (33317254796652589707933/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_218
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0655).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_218 :
    (∫ x in (109/256:ℝ)..(219/512:ℝ), x^6*thetaFirstMode x) ≤ (146286330567991/8000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (109/256:ℝ) (219/512:ℝ)
    (157158326831/100000000000000:ℝ) (152843939023/100000000000000:ℝ) (33317254796652589707933/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_218 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0655).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_219 :
    (9138327347624699/500000000000000000000000:ℝ) ≤ ∫ x in (219/512:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-681918162937633043325755199/31250000000000000000000000000:ℝ)*(thetaPowerMass 7 (219/512:ℝ) (55/128:ℝ)-(203740906957094489391/476299293587687964160:ℝ)*thetaPowerMass 6 (219/512:ℝ) (55/128:ℝ)) ≤
      thetaFirstModeFirst (203740906957094489391/476299293587687964160:ℝ)*(thetaPowerMass 7 (219/512:ℝ) (55/128:ℝ)-(203740906957094489391/476299293587687964160:ℝ)*thetaPowerMass 6 (219/512:ℝ) (55/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0333.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (219/512:ℝ) (55/128:ℝ)
    (203740906957094489391/476299293587687964160:ℝ) (152791681241/100000000000000:ℝ) (-681918162937633043325755199/31250000000000000000000000000:ℝ) (3268507342467591650561/12500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_219
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0659).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_219 :
    (∫ x in (219/512:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x) ≤ (18276736075446393/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (219/512:ℝ) (55/128:ℝ)
    (152843939023/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (3268507342467591650561/12500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_219 (thetaFirstMode_refined_node_0655).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_220 :
    (9131641976761871/500000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(221/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-65019401425270190145807/3125000000000000000000000:ℝ)*(thetaPowerMass 7 (55/128:ℝ) (221/512:ℝ)-(221/512:ℝ)*thetaPowerMass 6 (55/128:ℝ) (221/512:ℝ)) ≤
      thetaFirstModeFirst (221/512:ℝ)*(thetaPowerMass 7 (55/128:ℝ) (221/512:ℝ)-(221/512:ℝ)*thetaPowerMass 6 (55/128:ℝ) (221/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0335.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (55/128:ℝ) (221/512:ℝ)
    (221/512:ℝ) (36129481767/25000000000000:ℝ) (-65019401425270190145807/3125000000000000000000000:ℝ) (128244423508421206272841/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_220
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0661).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_220 :
    (∫ x in (55/128:ℝ)..(221/512:ℝ), x^6*thetaFirstMode x) ≤ (18263346877257897/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (55/128:ℝ) (221/512:ℝ)
    (148631229741/100000000000000:ℝ) (9032391857/6250000000000:ℝ) (128244423508421206272841/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_220 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0661).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_221 :
    (18245563013823693/1000000000000000000000000:ℝ) ≤ ∫ x in (221/512:ℝ)..(111/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (221/512:ℝ) (111/256:ℝ)-(221110673372114090409/512228437469441512960:ℝ)*thetaPowerMass 6 (221/512:ℝ) (111/256:ℝ)) ≤
      thetaFirstModeFirst (221110673372114090409/512228437469441512960:ℝ)*(thetaPowerMass 7 (221/512:ℝ) (111/256:ℝ)-(221110673372114090409/512228437469441512960:ℝ)*thetaPowerMass 6 (221/512:ℝ) (111/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0336.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (221/512:ℝ) (111/256:ℝ)
    (221110673372114090409/512228437469441512960:ℝ) (72234452543/50000000000000:ℝ) (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ) (251562624344124832607773/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_221
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0665).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_221 :
    (∫ x in (221/512:ℝ)..(111/256:ℝ), x^6*thetaFirstMode x) ≤ (18245645752389603/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (221/512:ℝ) (111/256:ℝ)
    (9032391857/6250000000000:ℝ) (17562894341/12500000000000:ℝ) (251562624344124832607773/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_221 (thetaFirstMode_refined_node_0661).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_222 :
    (4555898427885307/250000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(223/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-247793738206430294024529/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (111/256:ℝ) (223/512:ℝ)-(223/512:ℝ)*thetaPowerMass 6 (111/256:ℝ) (223/512:ℝ)) ≤
      thetaFirstModeFirst (223/512:ℝ)*(thetaPowerMass 7 (111/256:ℝ) (223/512:ℝ)-(223/512:ℝ)*thetaPowerMass 6 (111/256:ℝ) (223/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0338.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (111/256:ℝ) (223/512:ℝ)
    (223/512:ℝ) (68291839601/50000000000000:ℝ) (-247793738206430294024529/12500000000000000000000000:ℝ) (61675428197927839744517/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_222
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0667).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_222 :
    (∫ x in (111/256:ℝ)..(223/512:ℝ), x^6*thetaFirstMode x) ≤ (18223657428970553/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (111/256:ℝ) (223/512:ℝ)
    (17562894341/12500000000000:ℝ) (68292002787/50000000000000:ℝ) (61675428197927839744517/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_222 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0667).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_223 :
    (18197325253349891/1000000000000000000000000:ℝ) ≤ ∫ x in (223/512:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x := by
  have hd : (-99088961506408080648845019957/5000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (223/512:ℝ) (7/16:ℝ)-(239784500047674155607/550507092643036572160:ℝ)*thetaPowerMass 6 (223/512:ℝ) (7/16:ℝ)) ≤
      thetaFirstModeFirst (239784500047674155607/550507092643036572160:ℝ)*(thetaPowerMass 7 (223/512:ℝ) (7/16:ℝ)-(239784500047674155607/550507092643036572160:ℝ)*thetaPowerMass 6 (223/512:ℝ) (7/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0339.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (223/512:ℝ) (7/16:ℝ)
    (239784500047674155607/550507092643036572160:ℝ) (68268695707/50000000000000:ℝ) (-99088961506408080648845019957/5000000000000000000000000000000:ℝ) (120952946156479495543801/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_223
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0671).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_223 :
    (∫ x in (223/512:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x) ≤ (3639481860045033/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (223/512:ℝ) (7/16:ℝ)
    (68292002787/50000000000000:ℝ) (132758967949/100000000000000:ℝ) (120952946156479495543801/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_223 (thetaFirstMode_refined_node_0667).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

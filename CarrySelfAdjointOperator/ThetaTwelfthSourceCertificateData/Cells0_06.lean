import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature06
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative09
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative10

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_192 :
    (752123910769161307/125000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(193/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1996673611171739200025073949849/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/8:ℝ) (193/512:ℝ)-(3/8:ℝ)*thetaPowerMass 0 (3/8:ℝ) (193/512:ℝ)) ≤
      thetaFirstModeFirst (3/8:ℝ)*(thetaPowerMass 1 (3/8:ℝ) (193/512:ℝ)-(3/8:ℝ)*thetaPowerMass 0 (3/8:ℝ) (193/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0292.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/8:ℝ) (193/512:ℝ)
    (3/8:ℝ) (499108667/160000000000:ℝ) (-1996673611171739200025073949849/50000000000000000000000000000000:ℝ) (421372198150856993365933/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_192
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0576).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_192 :
    (∫ x in (3/8:ℝ)..(193/512:ℝ), x^0*thetaFirstMode x) ≤ (188031647051431801/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/8:ℝ) (193/512:ℝ)
    (311943577261/100000000000000:ℝ) (475352053/156250000000:ℝ) (421372198150856993365933/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_192 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0577).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_193 :
    (1466954655503717473/250000000000000000000000:ℝ) ≤ ∫ x in (193/512:ℝ)..(97/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-244327697043121646172975414807/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (193/512:ℝ) (97/256:ℝ)-(65332341813084493257/173304480845017500160:ℝ)*thetaPowerMass 0 (193/512:ℝ) (97/256:ℝ)) ≤
      thetaFirstModeFirst (65332341813084493257/173304480845017500160:ℝ)*(thetaPowerMass 1 (193/512:ℝ) (97/256:ℝ)-(65332341813084493257/173304480845017500160:ℝ)*thetaPowerMass 0 (193/512:ℝ) (97/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0294.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (193/512:ℝ) (97/256:ℝ)
    (65332341813084493257/173304480845017500160:ℝ) (12164766849/4000000000000:ℝ) (-244327697043121646172975414807/6250000000000000000000000000000:ℝ) (82917690064399091062251/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_193
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0581).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_193 :
    (∫ x in (193/512:ℝ)..(97/256:ℝ), x^0*thetaFirstMode x) ≤ (5867839343937532061/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (193/512:ℝ) (97/256:ℝ)
    (475352053/156250000000:ℝ) (296667793723/100000000000000:ℝ) (82917690064399091062251/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_193 (thetaFirstMode_refined_node_0577).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_194 :
    (5721759463685873829/1000000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(195/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-191437203566876054659248635867/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (97/256:ℝ) (195/512:ℝ)-(97/256:ℝ)*thetaPowerMass 0 (97/256:ℝ) (195/512:ℝ)) ≤
      thetaFirstModeFirst (97/256:ℝ)*(thetaPowerMass 1 (97/256:ℝ) (195/512:ℝ)-(97/256:ℝ)*thetaPowerMass 0 (97/256:ℝ) (195/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0295.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (97/256:ℝ) (195/512:ℝ)
    (97/256:ℝ) (1186668643/400000000000:ℝ) (-191437203566876054659248635867/5000000000000000000000000000000:ℝ) (407869947363270890347949/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_194
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0582).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_194 :
    (∫ x in (97/256:ℝ)..(195/512:ℝ), x^0*thetaFirstMode x) ≤ (2860890092437098203/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (97/256:ℝ) (195/512:ℝ)
    (296667793723/100000000000000:ℝ) (289268428881/100000000000000:ℝ) (407869947363270890347949/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_194 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0583).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_195 :
    (43584100676947611/7812500000000000000000:ℝ) ≤ ∫ x in (195/512:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-29276075031654577887586844773/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (195/512:ℝ) (49/128:ℝ)-(14336762398671353355/37640552179499351552:ℝ)*thetaPowerMass 0 (195/512:ℝ) (49/128:ℝ)) ≤
      thetaFirstModeFirst (14336762398671353355/37640552179499351552:ℝ)*(thetaPowerMass 1 (195/512:ℝ) (49/128:ℝ)-(14336762398671353355/37640552179499351552:ℝ)*thetaPowerMass 0 (195/512:ℝ) (49/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0297.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (195/512:ℝ) (49/128:ℝ)
    (14336762398671353355/37640552179499351552:ℝ) (72291929829/25000000000000:ℝ) (-29276075031654577887586844773/781250000000000000000000000000:ℝ) (200608460632174198657677/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_195
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0587).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_195 :
    (∫ x in (195/512:ℝ)..(49/128:ℝ), x^0*thetaFirstMode x) ≤ (1394696232146302507/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (195/512:ℝ) (49/128:ℝ)
    (289268428881/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (200608460632174198657677/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_195 (thetaFirstMode_refined_node_0583).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_196 :
    (2719391861499105567/500000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(197/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1834707607989126777971562390339/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (49/128:ℝ) (197/512:ℝ)-(49/128:ℝ)*thetaPowerMass 0 (49/128:ℝ) (197/512:ℝ)) ≤
      thetaFirstModeFirst (49/128:ℝ)*(thetaPowerMass 1 (49/128:ℝ) (197/512:ℝ)-(49/128:ℝ)*thetaPowerMass 0 (49/128:ℝ) (197/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0298.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (49/128:ℝ) (197/512:ℝ)
    (49/128:ℝ) (282024050041/100000000000000:ℝ) (-1834707607989126777971562390339/50000000000000000000000000000000:ℝ) (394629585759214226027709/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_196
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0588).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_196 :
    (∫ x in (49/128:ℝ)..(197/512:ℝ), x^0*thetaFirstMode x) ≤ (1359700940538666569/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (49/128:ℝ) (197/512:ℝ)
    (282024656491/100000000000000:ℝ) (274933938627/100000000000000:ℝ) (394629585759214226027709/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_196 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0589).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_197 :
    (2650883991680810069/500000000000000000000000:ℝ) ≤ ∫ x in (197/512:ℝ)..(99/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (197/512:ℝ) (99/256:ℝ)-(78578341309131839793/204209882504936988160:ℝ)*thetaPowerMass 0 (197/512:ℝ) (99/256:ℝ)) ≤
      thetaFirstModeFirst (78578341309131839793/204209882504936988160:ℝ)*(thetaPowerMass 1 (197/512:ℝ) (99/256:ℝ)-(78578341309131839793/204209882504936988160:ℝ)*thetaPowerMass 0 (197/512:ℝ) (99/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0300.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (197/512:ℝ) (99/256:ℝ)
    (78578341309131839793/204209882504936988160:ℝ) (274838413521/100000000000000:ℝ) (-1795326814739379979112159424283/50000000000000000000000000000000:ℝ) (194054068215068659549999/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_197
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0593).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_197 :
    (∫ x in (197/512:ℝ)..(99/256:ℝ), x^0*thetaFirstMode x) ≤ (2650893680665136161/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (197/512:ℝ) (99/256:ℝ)
    (274933938627/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (194054068215068659549999/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_197 (thetaFirstMode_refined_node_0589).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_198 :
    (5167667518784852189/1000000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(199/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-109851823764213060394908947733/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (99/256:ℝ) (199/512:ℝ)-(99/256:ℝ)*thetaPowerMass 0 (99/256:ℝ) (199/512:ℝ)) ≤
      thetaFirstModeFirst (99/256:ℝ)*(thetaPowerMass 1 (99/256:ℝ) (199/512:ℝ)-(99/256:ℝ)*thetaPowerMass 0 (99/256:ℝ) (199/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0301.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (99/256:ℝ) (199/512:ℝ)
    (99/256:ℝ) (133996590813/50000000000000:ℝ) (-109851823764213060394908947733/3125000000000000000000000000000:ℝ) (190826375409226913883677/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_198
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0594).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_198 :
    (∫ x in (99/256:ℝ)..(199/512:ℝ), x^0*thetaFirstMode x) ≤ (322980430749868109/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (99/256:ℝ) (199/512:ℝ)
    (33499220303/12500000000000:ℝ) (52240328029/20000000000000:ℝ) (190826375409226913883677/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_198 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0595).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_199 :
    (2518217640887447993/500000000000000000000000:ℝ) ≤ ∫ x in (199/512:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-429886080618259761215196442893/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (199/512:ℝ) (25/64:ℝ)-(86056132492075958991/221395846441879298560:ℝ)*thetaPowerMass 0 (199/512:ℝ) (25/64:ℝ)) ≤
      thetaFirstModeFirst (86056132492075958991/221395846441879298560:ℝ)*(thetaPowerMass 1 (199/512:ℝ) (25/64:ℝ)-(86056132492075958991/221395846441879298560:ℝ)*thetaPowerMass 0 (199/512:ℝ) (25/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0303.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (199/512:ℝ) (25/64:ℝ)
    (86056132492075958991/221395846441879298560:ℝ) (261111060999/100000000000000:ℝ) (-429886080618259761215196442893/12500000000000000000000000000000:ℝ) (375263588556175193661479/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_199
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0599).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_199 :
    (∫ x in (199/512:ℝ)..(25/64:ℝ), x^0*thetaFirstMode x) ≤ (629556751450904259/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (199/512:ℝ) (25/64:ℝ)
    (52240328029/20000000000000:ℝ) (12727755463/5000000000000:ℝ) (375263588556175193661479/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_199 (thetaFirstMode_refined_node_0595).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_200 :
    (4908022147212366947/1000000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(201/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1314910378613676273166924971/39062500000000000000000000000:ℝ)*(thetaPowerMass 1 (25/64:ℝ) (201/512:ℝ)-(25/64:ℝ)*thetaPowerMass 0 (25/64:ℝ) (201/512:ℝ)) ≤
      thetaFirstModeFirst (25/64:ℝ)*(thetaPowerMass 1 (25/64:ℝ) (201/512:ℝ)-(25/64:ℝ)*thetaPowerMass 0 (25/64:ℝ) (201/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0304.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (25/64:ℝ) (201/512:ℝ)
    (25/64:ℝ) (12727727663/5000000000000:ℝ) (-1314910378613676273166924971/39062500000000000000000000000:ℝ) (368940791481683951042041/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_200
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0600).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_200 :
    (∫ x in (25/64:ℝ)..(201/512:ℝ), x^0*thetaFirstMode x) ≤ (4908040870431568571/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/64:ℝ) (201/512:ℝ)
    (12727755463/5000000000000:ℝ) (15503233281/6250000000000:ℝ) (368940791481683951042041/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_200 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0601).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_201 :
    (4782382015226937831/1000000000000000000000000:ℝ) ≤ ∫ x in (201/512:ℝ)..(101/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (201/512:ℝ) (101/256:ℝ)-(94159912870084059009/239834298071963906560:ℝ)*thetaPowerMass 0 (201/512:ℝ) (101/256:ℝ)) ≤
      thetaFirstModeFirst (94159912870084059009/239834298071963906560:ℝ)*(thetaPowerMass 1 (201/512:ℝ) (101/256:ℝ)-(94159912870084059009/239834298071963906560:ℝ)*thetaPowerMass 0 (201/512:ℝ) (101/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0306.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (201/512:ℝ) (101/256:ℝ)
    (94159912870084059009/239834298071963906560:ℝ) (247965870591/100000000000000:ℝ) (-1646269741049782808922279470399/50000000000000000000000000000000:ℝ) (181342241891124615302757/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_201
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0605).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_201 :
    (∫ x in (201/512:ℝ)..(101/256:ℝ), x^0*thetaFirstMode x) ≤ (4782400112632068887/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (201/512:ℝ) (101/256:ℝ)
    (15503233281/6250000000000:ℝ) (30211137237/12500000000000:ℝ) (181342241891124615302757/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_201 (thetaFirstMode_refined_node_0601).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_202 :
    (931893357668914509/200000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(203/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-100689011870884134959010086427/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (101/256:ℝ) (203/512:ℝ)-(101/256:ℝ)*thetaPowerMass 0 (101/256:ℝ) (203/512:ℝ)) ≤
      thetaFirstModeFirst (101/256:ℝ)*(thetaPowerMass 1 (101/256:ℝ) (203/512:ℝ)-(101/256:ℝ)*thetaPowerMass 0 (101/256:ℝ) (203/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0307.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (101/256:ℝ) (203/512:ℝ)
    (101/256:ℝ) (241688565857/100000000000000:ℝ) (-100689011870884134959010086427/3125000000000000000000000000000:ℝ) (356494772124939210200983/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_202
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0606).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_202 :
    (∫ x in (101/256:ℝ)..(203/512:ℝ), x^0*thetaFirstMode x) ≤ (582435609665274361/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (101/256:ℝ) (203/512:ℝ)
    (30211137237/12500000000000:ℝ) (235464818869/100000000000000:ℝ) (356494772124939210200983/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_202 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0607).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_203 :
    (4539231318944877941/1000000000000000000000000:ℝ) ≤ ∫ x in (203/512:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-393862812547991790702588742107/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (203/512:ℝ) (51/128:ℝ)-(102935065125197358207/259602677601152028160:ℝ)*thetaPowerMass 0 (203/512:ℝ) (51/128:ℝ)) ≤
      thetaFirstModeFirst (102935065125197358207/259602677601152028160:ℝ)*(thetaPowerMass 1 (203/512:ℝ) (51/128:ℝ)-(102935065125197358207/259602677601152028160:ℝ)*thetaPowerMass 0 (203/512:ℝ) (51/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0309.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (203/512:ℝ) (51/128:ℝ)
    (102935065125197358207/259602677601152028160:ℝ) (2353834549/1000000000000:ℝ) (-393862812547991790702588742107/12500000000000000000000000000000:ℝ) (875929364510965849653/2500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_203
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0611).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_203 :
    (∫ x in (203/512:ℝ)..(51/128:ℝ), x^0*thetaFirstMode x) ≤ (4539248799397677043/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (203/512:ℝ) (51/128:ℝ)
    (235464818869/100000000000000:ℝ) (9175061369/4000000000000:ℝ) (875929364510965849653/2500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_203 (thetaFirstMode_refined_node_0607).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_204 :
    (2210814269983135869/500000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(205/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1541393956965029146921225289/50000000000000000000000000000:ℝ)*(thetaPowerMass 1 (51/128:ℝ) (205/512:ℝ)-(51/128:ℝ)*thetaPowerMass 0 (51/128:ℝ) (205/512:ℝ)) ≤
      thetaFirstModeFirst (51/128:ℝ)*(thetaPowerMass 1 (51/128:ℝ) (205/512:ℝ)-(51/128:ℝ)*thetaPowerMass 0 (51/128:ℝ) (205/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0310.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (51/128:ℝ) (205/512:ℝ)
    (51/128:ℝ) (22937602533/10000000000000:ℝ) (-1541393956965029146921225289/50000000000000000000000000000:ℝ) (172157738447815749517883/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_204
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0612).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_204 :
    (∫ x in (51/128:ℝ)..(205/512:ℝ), x^0*thetaFirstMode x) ≤ (4421646010268843403/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (51/128:ℝ) (205/512:ℝ)
    (9175061369/4000000000000:ℝ) (44684381643/20000000000000:ℝ) (172157738447815749517883/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_204 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0613).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_205 :
    (4306614259639230641/1000000000000000000000000:ℝ) ≤ ∫ x in (205/512:ℝ)..(103/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5886862690187487516232156083/195312500000000000000000000000:ℝ)*(thetaPowerMass 1 (205/512:ℝ) (103/256:ℝ)-(22485952682885662245/56156474985950039552:ℝ)*thetaPowerMass 0 (205/512:ℝ) (103/256:ℝ)) ≤
      thetaFirstModeFirst (22485952682885662245/56156474985950039552:ℝ)*(thetaPowerMass 1 (205/512:ℝ) (103/256:ℝ)-(22485952682885662245/56156474985950039552:ℝ)*thetaPowerMass 0 (205/512:ℝ) (103/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0312.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (205/512:ℝ) (103/256:ℝ)
    (22485952682885662245/56156474985950039552:ℝ) (223344831929/100000000000000:ℝ) (-5886862690187487516232156083/195312500000000000000000000000:ℝ) (169163010199648404157571/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_205
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0617).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_205 :
    (∫ x in (205/512:ℝ)..(103/256:ℝ), x^0*thetaFirstMode x) ≤ (2153315569223233481/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (205/512:ℝ) (103/256:ℝ)
    (44684381643/20000000000000:ℝ) (217598630551/100000000000000:ℝ) (169163010199648404157571/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_205 (thetaFirstMode_refined_node_0613).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_206 :
    (4194142443019620927/1000000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(207/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1474142493352870903413065561681/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (103/256:ℝ) (207/512:ℝ)-(103/256:ℝ)*thetaPowerMass 0 (103/256:ℝ) (207/512:ℝ)) ≤
      thetaFirstModeFirst (103/256:ℝ)*(thetaPowerMass 1 (103/256:ℝ) (207/512:ℝ)-(103/256:ℝ)*thetaPowerMass 0 (103/256:ℝ) (207/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0313.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (103/256:ℝ) (207/512:ℝ)
    (103/256:ℝ) (3399971/1562500000:ℝ) (-1474142493352870903413065561681/50000000000000000000000000000000:ℝ) (332403414418076337135631/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_206
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0618).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_206 :
    (∫ x in (103/256:ℝ)..(207/512:ℝ), x^0*thetaFirstMode x) ≤ (419415931002993733/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (103/256:ℝ) (207/512:ℝ)
    (217598630551/100000000000000:ℝ) (52976104109/25000000000000:ℝ) (332403414418076337135631/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_206 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0619).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_207 :
    (2042084928394823701/500000000000000000000000:ℝ) ≤ ∫ x in (207/512:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-180121801082870474100554348559/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (207/512:ℝ) (13/32:ℝ)-(122695115016799804743/303458889196134300160:ℝ)*thetaPowerMass 0 (207/512:ℝ) (13/32:ℝ)) ≤
      thetaFirstModeFirst (122695115016799804743/303458889196134300160:ℝ)*(thetaPowerMass 1 (207/512:ℝ) (13/32:ℝ)-(122695115016799804743/303458889196134300160:ℝ)*thetaPowerMass 0 (207/512:ℝ) (13/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0315.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (207/512:ℝ) (13/32:ℝ)
    (122695115016799804743/303458889196134300160:ℝ) (211831426291/100000000000000:ℝ) (-180121801082870474100554348559/6250000000000000000000000000000:ℝ) (326547680306461325909969/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_207
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0623).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_207 :
    (∫ x in (207/512:ℝ)..(13/32:ℝ), x^0*thetaFirstMode x) ≤ (1021046537267123973/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (207/512:ℝ) (13/32:ℝ)
    (52976104109/25000000000000:ℝ) (206337006571/100000000000000:ℝ) (326547680306461325909969/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_207 (thetaFirstMode_refined_node_0619).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_208 :
    (3976651498816543763/1000000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(209/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-704608803669548152540724394021/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (13/32:ℝ) (209/512:ℝ)-(13/32:ℝ)*thetaPowerMass 0 (13/32:ℝ) (209/512:ℝ)) ≤
      thetaFirstModeFirst (13/32:ℝ)*(thetaPowerMass 1 (13/32:ℝ) (209/512:ℝ)-(13/32:ℝ)*thetaPowerMass 0 (13/32:ℝ) (209/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0316.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (13/32:ℝ) (209/512:ℝ)
    (13/32:ℝ) (103168270791/50000000000000:ℝ) (-704608803669548152540724394021/25000000000000000000000000000000:ℝ) (160379411427857512154149/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_208
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0624).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_208 :
    (∫ x in (13/32:ℝ)..(209/512:ℝ), x^0*thetaFirstMode x) ≤ (3976667777746667841/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/32:ℝ) (209/512:ℝ)
    (206337006571/100000000000000:ℝ) (200894167167/100000000000000:ℝ) (160379411427857512154149/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_208 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0625).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_209 :
    (387154509581739801/100000000000000000000000:ℝ) ≤ ∫ x in (209/512:ℝ)..(105/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-344302932232714622490896993499/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (209/512:ℝ) (105/256:ℝ)-(133785307673187732441/327721993105999567360:ℝ)*thetaPowerMass 0 (209/512:ℝ) (105/256:ℝ)) ≤
      thetaFirstModeFirst (133785307673187732441/327721993105999567360:ℝ)*(thetaPowerMass 1 (209/512:ℝ) (105/256:ℝ)-(133785307673187732441/327721993105999567360:ℝ)*thetaPowerMass 0 (209/512:ℝ) (105/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0318.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (209/512:ℝ) (105/256:ℝ)
    (133785307673187732441/327721993105999567360:ℝ) (200825070001/100000000000000:ℝ) (-344302932232714622490896993499/12500000000000000000000000000000:ℝ) (78759207614849840720043/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_209
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0629).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_209 :
    (∫ x in (209/512:ℝ)..(105/256:ℝ), x^0*thetaFirstMode x) ≤ (3871560816511112527/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (209/512:ℝ) (105/256:ℝ)
    (200894167167/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (78759207614849840720043/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_209 (thetaFirstMode_refined_node_0625).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_210 :
    (1884403339091215463/500000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(211/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-84160441287669287987253127539/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (105/256:ℝ) (211/512:ℝ)-(105/256:ℝ)*thetaPowerMass 0 (105/256:ℝ) (211/512:ℝ)) ≤
      thetaFirstModeFirst (105/256:ℝ)*(thetaPowerMass 1 (105/256:ℝ) (211/512:ℝ)-(105/256:ℝ)*thetaPowerMass 0 (105/256:ℝ) (211/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0319.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (105/256:ℝ) (211/512:ℝ)
    (105/256:ℝ) (48893311439/25000000000000:ℝ) (-84160441287669287987253127539/3125000000000000000000000000000:ℝ) (38672709412707373928059/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_210
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0630).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_210 :
    (∫ x in (105/256:ℝ)..(211/512:ℝ), x^0*thetaFirstMode x) ≤ (471102798003930507/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (105/256:ℝ) (211/512:ℝ)
    (97786844973/50000000000000:ℝ) (23796674017/12500000000000:ℝ) (38672709412707373928059/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_210 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0631).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_211 :
    (3668394933225539007/1000000000000000000000000:ℝ) ≤ ∫ x in (211/512:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-657848293661949787266058245451/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (211/512:ℝ) (53/128:ℝ)-(145757762788870993959/353665902141891765760:ℝ)*thetaPowerMass 0 (211/512:ℝ) (53/128:ℝ)) ≤
      thetaFirstModeFirst (145757762788870993959/353665902141891765760:ℝ)*(thetaPowerMass 1 (211/512:ℝ) (53/128:ℝ)-(145757762788870993959/353665902141891765760:ℝ)*thetaPowerMass 0 (211/512:ℝ) (53/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0321.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (211/512:ℝ) (53/128:ℝ)
    (145757762788870993959/353665902141891765760:ℝ) (95154001427/50000000000000:ℝ) (-657848293661949787266058245451/25000000000000000000000000000000:ℝ) (151896656769668924807039/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_211
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0635).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_211 :
    (∫ x in (211/512:ℝ)..(53/128:ℝ), x^0*thetaFirstMode x) ≤ (917102524265849867/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (211/512:ℝ) (53/128:ℝ)
    (23796674017/12500000000000:ℝ) (92645558231/50000000000000:ℝ) (151896656769668924807039/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_211 (thetaFirstMode_refined_node_0631).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_212 :
    (892566730643554073/250000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(213/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-643069310016350191327931928339/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (53/128:ℝ) (213/512:ℝ)-(53/128:ℝ)*thetaPowerMass 0 (53/128:ℝ) (213/512:ℝ)) ≤
      thetaFirstModeFirst (53/128:ℝ)*(thetaPowerMass 1 (53/128:ℝ) (213/512:ℝ)-(53/128:ℝ)*thetaPowerMass 0 (53/128:ℝ) (213/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0322.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (53/128:ℝ) (213/512:ℝ)
    (53/128:ℝ) (7411627693/4000000000000:ℝ) (-643069310016350191327931928339/25000000000000000000000000000000:ℝ) (59654337099177772698799/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_212
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0636).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_212 :
    (∫ x in (53/128:ℝ)..(213/512:ℝ), x^0*thetaFirstMode x) ≤ (1785141035082757607/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (53/128:ℝ) (213/512:ℝ)
    (92645558231/50000000000000:ℝ) (90162365563/50000000000000:ℝ) (59654337099177772698799/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_212 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0637).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_213 :
    (1737191146902962073/500000000000000000000000:ℝ) ≤ ∫ x in (213/512:ℝ)..(107/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-628188395966882458476796945611/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (213/512:ℝ) (107/256:ℝ)-(158673294672040530657/381389448748703772160:ℝ)*thetaPowerMass 0 (213/512:ℝ) (107/256:ℝ)) ≤
      thetaFirstModeFirst (158673294672040530657/381389448748703772160:ℝ)*(thetaPowerMass 1 (213/512:ℝ) (107/256:ℝ)-(158673294672040530657/381389448748703772160:ℝ)*thetaPowerMass 0 (213/512:ℝ) (107/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0324.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (213/512:ℝ) (107/256:ℝ)
    (158673294672040530657/381389448748703772160:ℝ) (90131436197/50000000000000:ℝ) (-628188395966882458476796945611/25000000000000000000000000000000:ℝ) (292816715856159756349177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_213
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0641).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_213 :
    (∫ x in (213/512:ℝ)..(107/256:ℝ), x^0*thetaFirstMode x) ≤ (694879383067535619/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (213/512:ℝ) (107/256:ℝ)
    (90162365563/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (292816715856159756349177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_213 (thetaFirstMode_refined_node_0637).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_214 :
    (3380699137546558207/1000000000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(215/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15348501354658158059784474213/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (107/256:ℝ) (215/512:ℝ)-(107/256:ℝ)*thetaPowerMass 0 (107/256:ℝ) (215/512:ℝ)) ≤
      thetaFirstModeFirst (107/256:ℝ)*(thetaPowerMass 1 (107/256:ℝ) (215/512:ℝ)-(107/256:ℝ)*thetaPowerMass 0 (107/256:ℝ) (215/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0325.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (107/256:ℝ) (215/512:ℝ)
    (107/256:ℝ) (175471724979/100000000000000:ℝ) (-15348501354658158059784474213/625000000000000000000000000000:ℝ) (3592853923256872964007/12500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_214
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0642).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_214 :
    (∫ x in (107/256:ℝ)..(215/512:ℝ), x^0*thetaFirstMode x) ≤ (845178435375856647/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (107/256:ℝ) (215/512:ℝ)
    (17547212979/10000000000000:ℝ) (8536561577/5000000000000:ℝ) (3592853923256872964007/12500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_214 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0643).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_215 :
    (822294515071824443/250000000000000000000000:ℝ) ≤ ∫ x in (215/512:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (215/512:ℝ) (27/64:ℝ)-(34519255196979847635/82199252318350141952:ℝ)*thetaPowerMass 0 (215/512:ℝ) (27/64:ℝ)) ≤
      thetaFirstModeFirst (34519255196979847635/82199252318350141952:ℝ)*(thetaPowerMass 1 (215/512:ℝ) (27/64:ℝ)-(34519255196979847635/82199252318350141952:ℝ)*thetaPowerMass 0 (215/512:ℝ) (27/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0327.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (215/512:ℝ) (27/64:ℝ)
    (34519255196979847635/82199252318350141952:ℝ) (170672733493/100000000000000:ℝ) (-1199200231155814902137354659227/50000000000000000000000000000000:ℝ) (282106373519129414186399/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_215
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0647).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_215 :
    (∫ x in (215/512:ℝ)..(27/64:ℝ), x^0*thetaFirstMode x) ≤ (3289192153865286653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (215/512:ℝ) (27/64:ℝ)
    (8536561577/5000000000000:ℝ) (20762497607/12500000000000:ℝ) (282106373519129414186399/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_215 (thetaFirstMode_refined_node_0643).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_216 :
    (3199778178489337589/1000000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(217/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-73233715856324238905342175189/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (27/64:ℝ) (217/512:ℝ)-(27/64:ℝ)*thetaPowerMass 0 (27/64:ℝ) (217/512:ℝ)) ≤
      thetaFirstModeFirst (27/64:ℝ)*(thetaPowerMass 1 (27/64:ℝ) (217/512:ℝ)-(27/64:ℝ)*thetaPowerMass 0 (27/64:ℝ) (217/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0328.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (27/64:ℝ) (217/512:ℝ)
    (27/64:ℝ) (166099594661/100000000000000:ℝ) (-73233715856324238905342175189/3125000000000000000000000000000:ℝ) (55370154762726230771913/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_216
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0648).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_216 :
    (∫ x in (27/64:ℝ)..(217/512:ℝ), x^0*thetaFirstMode x) ≤ (3199792253230818193/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/64:ℝ) (217/512:ℝ)
    (20762497607/12500000000000:ℝ) (161576347573/100000000000000:ℝ) (55370154762726230771913/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_216 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0649).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_217 :
    (778115263840680507/250000000000000000000000:ℝ) ≤ ∫ x in (217/512:ℝ)..(109/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-22882298452005075002291703247/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (217/512:ℝ) (109/256:ℝ)-(187594809587397482193/442594949984965788160:ℝ)*thetaPowerMass 0 (217/512:ℝ) (109/256:ℝ)) ≤
      thetaFirstModeFirst (187594809587397482193/442594949984965788160:ℝ)*(thetaPowerMass 1 (217/512:ℝ) (109/256:ℝ)-(187594809587397482193/442594949984965788160:ℝ)*thetaPowerMass 0 (217/512:ℝ) (109/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0330.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (217/512:ℝ) (109/256:ℝ)
    (187594809587397482193/442594949984965788160:ℝ) (161521047537/100000000000000:ℝ) (-22882298452005075002291703247/1000000000000000000000000000000:ℝ) (135830689454414892203241/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_217
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0653).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_217 :
    (∫ x in (217/512:ℝ)..(109/256:ℝ), x^0*thetaFirstMode x) ≤ (389059329392917899/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (217/512:ℝ) (109/256:ℝ)
    (161576347573/100000000000000:ℝ) (157158326831/100000000000000:ℝ) (135830689454414892203241/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_217 (thetaFirstMode_refined_node_0649).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_218 :
    (1513593414563604797/500000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(219/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-223532947536861015202605822641/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (109/256:ℝ) (219/512:ℝ)-(109/256:ℝ)*thetaPowerMass 0 (109/256:ℝ) (219/512:ℝ)) ≤
      thetaFirstModeFirst (109/256:ℝ)*(thetaPowerMass 1 (109/256:ℝ) (219/512:ℝ)-(109/256:ℝ)*thetaPowerMass 0 (109/256:ℝ) (219/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0331.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (109/256:ℝ) (219/512:ℝ)
    (109/256:ℝ) (982237241/625000000000:ℝ) (-223532947536861015202605822641/10000000000000000000000000000000:ℝ) (33317254796652589707933/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_218
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0654).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_218 :
    (∫ x in (109/256:ℝ)..(219/512:ℝ), x^0*thetaFirstMode x) ≤ (1513600194442857473/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (109/256:ℝ) (219/512:ℝ)
    (157158326831/100000000000000:ℝ) (152843939023/100000000000000:ℝ) (33317254796652589707933/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_218 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0655).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_219 :
    (588783603306310793/200000000000000000000000:ℝ) ≤ ∫ x in (219/512:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-681918162937633043325755199/31250000000000000000000000000:ℝ)*(thetaPowerMass 1 (219/512:ℝ) (55/128:ℝ)-(203740906957094489391/476299293587687964160:ℝ)*thetaPowerMass 0 (219/512:ℝ) (55/128:ℝ)) ≤
      thetaFirstModeFirst (203740906957094489391/476299293587687964160:ℝ)*(thetaPowerMass 1 (219/512:ℝ) (55/128:ℝ)-(203740906957094489391/476299293587687964160:ℝ)*thetaPowerMass 0 (219/512:ℝ) (55/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0333.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (219/512:ℝ) (55/128:ℝ)
    (203740906957094489391/476299293587687964160:ℝ) (152791681241/100000000000000:ℝ) (-681918162937633043325755199/31250000000000000000000000000:ℝ) (3268507342467591650561/12500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_219
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0659).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_219 :
    (∫ x in (219/512:ℝ)..(55/128:ℝ), x^0*thetaFirstMode x) ≤ (147196554822251311/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (219/512:ℝ) (55/128:ℝ)
    (152843939023/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (3268507342467591650561/12500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_219 (thetaFirstMode_refined_node_0655).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_220 :
    (2862615772570588721/1000000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(221/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1065604242487721865710918355903/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (55/128:ℝ) (221/512:ℝ)-(55/128:ℝ)*thetaPowerMass 0 (55/128:ℝ) (221/512:ℝ)) ≤
      thetaFirstModeFirst (55/128:ℝ)*(thetaPowerMass 1 (55/128:ℝ) (221/512:ℝ)-(55/128:ℝ)*thetaPowerMass 0 (55/128:ℝ) (221/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0334.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (55/128:ℝ) (221/512:ℝ)
    (55/128:ℝ) (58058937/39062500000:ℝ) (-1065604242487721865710918355903/50000000000000000000000000000000:ℝ) (128244423508421206272841/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_220
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0660).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_220 :
    (∫ x in (55/128:ℝ)..(221/512:ℝ), x^0*thetaFirstMode x) ≤ (572525766272025441/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (55/128:ℝ) (221/512:ℝ)
    (148631229741/100000000000000:ℝ) (9032391857/6250000000000:ℝ) (128244423508421206272841/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_220 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0661).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_221 :
    (2783243563619730483/1000000000000000000000000:ℝ) ≤ ∫ x in (221/512:ℝ)..(111/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (221/512:ℝ) (111/256:ℝ)-(221110673372114090409/512228437469441512960:ℝ)*thetaPowerMass 0 (221/512:ℝ) (111/256:ℝ)) ≤
      thetaFirstModeFirst (221110673372114090409/512228437469441512960:ℝ)*(thetaPowerMass 1 (221/512:ℝ) (111/256:ℝ)-(221110673372114090409/512228437469441512960:ℝ)*thetaPowerMass 0 (221/512:ℝ) (111/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0336.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (221/512:ℝ) (111/256:ℝ)
    (221110673372114090409/512228437469441512960:ℝ) (72234452543/50000000000000:ℝ) (-1040011062986749091978182181949/50000000000000000000000000000000:ℝ) (251562624344124832607773/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_221
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0665).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_221 :
    (∫ x in (221/512:ℝ)..(111/256:ℝ), x^0*thetaFirstMode x) ≤ (173953509838305471/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (221/512:ℝ) (111/256:ℝ)
    (9032391857/6250000000000:ℝ) (17562894341/12500000000000:ℝ) (251562624344124832607773/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_221 (thetaFirstMode_refined_node_0661).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_222 :
    (2705763555598418801/1000000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(223/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-31734578013565063304325910753/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (111/256:ℝ) (223/512:ℝ)-(111/256:ℝ)*thetaPowerMass 0 (111/256:ℝ) (223/512:ℝ)) ≤
      thetaFirstModeFirst (111/256:ℝ)*(thetaPowerMass 1 (111/256:ℝ) (223/512:ℝ)-(111/256:ℝ)*thetaPowerMass 0 (111/256:ℝ) (223/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0337.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (111/256:ℝ) (223/512:ℝ)
    (111/256:ℝ) (1405028203/1000000000000:ℝ) (-31734578013565063304325910753/1562500000000000000000000000000:ℝ) (61675428197927839744517/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_222
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0666).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_222 :
    (∫ x in (111/256:ℝ)..(223/512:ℝ), x^0*thetaFirstMode x) ≤ (2705776127241339267/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (111/256:ℝ) (223/512:ℝ)
    (17562894341/12500000000000:ℝ) (68292002787/50000000000000:ℝ) (61675428197927839744517/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_222 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0667).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_223 :
    (2630140159679558857/1000000000000000000000000:ℝ) ≤ ∫ x in (223/512:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-99088961506408080648845019957/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (223/512:ℝ) (7/16:ℝ)-(239784500047674155607/550507092643036572160:ℝ)*thetaPowerMass 0 (223/512:ℝ) (7/16:ℝ)) ≤
      thetaFirstModeFirst (239784500047674155607/550507092643036572160:ℝ)*(thetaPowerMass 1 (223/512:ℝ) (7/16:ℝ)-(239784500047674155607/550507092643036572160:ℝ)*thetaPowerMass 0 (223/512:ℝ) (7/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0339.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (223/512:ℝ) (7/16:ℝ)
    (239784500047674155607/550507092643036572160:ℝ) (68268695707/50000000000000:ℝ) (-99088961506408080648845019957/5000000000000000000000000000000:ℝ) (120952946156479495543801/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_223
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0671).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_223 :
    (∫ x in (223/512:ℝ)..(7/16:ℝ), x^0*thetaFirstMode x) ≤ (657538070216229459/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (223/512:ℝ) (7/16:ℝ)
    (68292002787/50000000000000:ℝ) (132758967949/100000000000000:ℝ) (120952946156479495543801/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_223 (thetaFirstMode_refined_node_0667).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature7

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_224 :
    (158983550002741/1000000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (7/8:ℝ) (225/256:ℝ)
    (449/512:ℝ) (254193/6250000000000:ℝ) (45469611906907/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_224
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1345).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^0*thetaFirstMode x) ≤ (79506078903509/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/8:ℝ) (225/256:ℝ)
    (136283/3125000000000:ℝ) (379193/10000000000000:ℝ) (45469611906907/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_224 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_225 :
    (4317522152517/31250000000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (225/256:ℝ) (113/128:ℝ)
    (451/512:ℝ) (1767181/50000000000000:ℝ) (20070903384091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_225
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1351).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x) ≤ (69093089947581/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (225/256:ℝ) (113/128:ℝ)
    (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ) (20070903384091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_225 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_226 :
    (14991404139491/125000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (113/128:ℝ) (227/256:ℝ)
    (453/512:ℝ) (3067989/100000000000000:ℝ) (35398370214817/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_226
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1357).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^0*thetaFirstMode x) ≤ (59976921180947/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (113/128:ℝ) (227/256:ℝ)
    (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ) (35398370214817/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_226 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_227 :
    (2079798728777/20000000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (227/256:ℝ) (57/64:ℝ)
    (455/512:ℝ) (8313/312500000000:ℝ) (15590014330449/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_227
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1363).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x) ≤ (104010009934799/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (227/256:ℝ) (57/64:ℝ)
    (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ) (15590014330449/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_227 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_228 :
    (90065396104387/1000000000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (57/64:ℝ) (229/256:ℝ)
    (457/512:ℝ) (230393/10000000000000:ℝ) (27432954452633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_228
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1369).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^0*thetaFirstMode x) ≤ (2815099144843/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/64:ℝ) (229/256:ℝ)
    (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ) (27432954452633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_228 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_229 :
    (3895815956047/50000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (229/256:ℝ) (115/128:ℝ)
    (459/512:ℝ) (3189/160000000000:ℝ) (12054189803443/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_229
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1375).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x) ≤ (77932049258119/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (229/256:ℝ) (115/128:ℝ)
    (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_229 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_230 :
    (67328455088293/1000000000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (115/128:ℝ) (231/256:ℝ)
    (461/512:ℝ) (1722263/100000000000000:ℝ) (10581051391233/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_230
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1381).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^0*thetaFirstMode x) ≤ (67342367167163/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (115/128:ℝ) (231/256:ℝ)
    (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ) (10581051391233/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_230 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_231 :
    (5811186097847/100000000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (231/256:ℝ) (29/32:ℝ)
    (463/512:ℝ) (371621/25000000000000:ℝ) (9277074693267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_231
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1387).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x) ≤ (58124129605559/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (231/256:ℝ) (29/32:ℝ)
    (40007/2500000000000:ℝ) (690197/50000000000000:ℝ) (9277074693267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_231 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_232 :
    (50098283028799/1000000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (29/32:ℝ) (233/256:ℝ)
    (465/512:ℝ) (1281483/100000000000000:ℝ) (16248401359171/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_232
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1393).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^0*thetaFirstMode x) ≤ (25054549002451/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/32:ℝ) (233/256:ℝ)
    (690197/50000000000000:ℝ) (297331/25000000000000:ℝ) (16248401359171/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_232 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_233 :
    (43138851265113/1000000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (233/256:ℝ) (117/128:ℝ)
    (467/512:ℝ) (1103451/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_233
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1399).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x) ≤ (43148410751023/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (233/256:ℝ) (117/128:ℝ)
    (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_233 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_234 :
    (37102125564699/1000000000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (117/128:ℝ) (235/256:ℝ)
    (469/512:ℝ) (37961/4000000000000:ℝ) (1552051974267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_234
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1405).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^0*thetaFirstMode x) ≤ (37110514495601/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (117/128:ℝ) (235/256:ℝ)
    (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ) (1552051974267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_234 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_235 :
    (15935973265177/500000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (235/256:ℝ) (59/64:ℝ)
    (471/512:ℝ) (815233/100000000000000:ℝ) (5417188802421/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_235
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1411).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x) ≤ (15939664797771/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (235/256:ℝ) (59/64:ℝ)
    (879727/100000000000000:ℝ) (3021/400000000000:ℝ) (5417188802421/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_235 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_236 :
    (27346028623759/1000000000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (59/64:ℝ) (237/256:ℝ)
    (473/512:ℝ) (349729/50000000000000:ℝ) (2360604497989/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_236
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1417).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^0*thetaFirstMode x) ≤ (27352513064981/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/64:ℝ) (237/256:ℝ)
    (3021/400000000000:ℝ) (1619/250000000000:ℝ) (2360604497989/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_236 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_237 :
    (1171713989987/50000000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (237/256:ℝ) (119/128:ℝ)
    (475/512:ℝ) (119879/20000000000000:ℝ) (8219203312331/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_237
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1423).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x) ≤ (292999450319/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (237/256:ℝ) (119/128:ℝ)
    (1619/250000000000:ℝ) (69327/12500000000000:ℝ) (8219203312331/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_237 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_238 :
    (626796026993/31250000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (119/128:ℝ) (239/256:ℝ)
    (477/512:ℝ) (513017/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_238
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1429).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^0*thetaFirstMode x) ≤ (10031228308099/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (119/128:ℝ) (239/256:ℝ)
    (69327/12500000000000:ℝ) (474399/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_238 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_239 :
    (17146073149859/1000000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (239/256:ℝ) (15/16:ℝ)
    (479/512:ℝ) (87709/20000000000000:ℝ) (155112952199/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_239
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1435).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x) ≤ (17150431825281/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (239/256:ℝ) (15/16:ℝ)
    (474399/100000000000000:ℝ) (405281/100000000000000:ℝ) (155112952199/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_239 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_240 :
    (146390269479/10000000000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (15/16:ℝ) (241/256:ℝ)
    (481/512:ℝ) (374417/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_240
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1441).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^0*thetaFirstMode x) ≤ (14642844541699/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/16:ℝ) (241/256:ℝ)
    (405281/100000000000000:ℝ) (345801/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_240 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_241 :
    (3120715693789/250000000000000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (241/256:ℝ) (121/128:ℝ)
    (483/512:ℝ) (63853/20000000000000:ℝ) (582524031463/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_241
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1447).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x) ≤ (6243104021719/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (241/256:ℝ) (121/128:ℝ)
    (345801/100000000000000:ℝ) (147339/50000000000000:ℝ) (582524031463/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_241 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_242 :
    (106308316591/10000000000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (121/128:ℝ) (243/256:ℝ)
    (485/512:ℝ) (271893/100000000000000:ℝ) (2015550292363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_242
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1453).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^0*thetaFirstMode x) ≤ (212674936761/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (121/128:ℝ) (243/256:ℝ)
    (147339/50000000000000:ℝ) (50159/20000000000000:ℝ) (2015550292363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_242 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_243 :
    (2260511800907/250000000000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (243/256:ℝ) (61/64:ℝ)
    (487/512:ℝ) (46251/20000000000000:ℝ) (3482453219147/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_243
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1459).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x) ≤ (4522298499497/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (243/256:ℝ) (61/64:ℝ)
    (50159/20000000000000:ℝ) (106587/50000000000000:ℝ) (3482453219147/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_243 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_244 :
    (3840410673787/500000000000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (61/64:ℝ) (245/256:ℝ)
    (489/512:ℝ) (98219/50000000000000:ℝ) (3004587016079/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_244
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1465).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^0*thetaFirstMode x) ≤ (7683044804851/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/64:ℝ) (245/256:ℝ)
    (106587/50000000000000:ℝ) (90481/50000000000000:ℝ) (3004587016079/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_244 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_245 :
    (6516078088701/1000000000000000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (245/256:ℝ) (123/128:ℝ)
    (491/512:ℝ) (166647/100000000000000:ℝ) (647229882051/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_245
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1471).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x) ≤ (814752450481/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (245/256:ℝ) (123/128:ℝ)
    (90481/50000000000000:ℝ) (153419/100000000000000:ℝ) (647229882051/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_245 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_246 :
    (8626198753/1562500000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (123/128:ℝ) (247/256:ℝ)
    (493/512:ℝ) (14119/10000000000000:ℝ) (445562075193/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_246
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1477).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^0*thetaFirstMode x) ≤ (138061249279/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (123/128:ℝ) (247/256:ℝ)
    (153419/100000000000000:ℝ) (129897/100000000000000:ℝ) (445562075193/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_246 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_247 :
    (2335658659571/500000000000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (247/256:ℝ) (31/32:ℝ)
    (495/512:ℝ) (14933/12500000000000:ℝ) (1914543067207/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_247
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1483).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x) ≤ (934555103593/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (247/256:ℝ) (31/32:ℝ)
    (129897/100000000000000:ℝ) (27459/25000000000000:ℝ) (1914543067207/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_247 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_248 :
    (3947361990473/1000000000000000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (31/32:ℝ) (249/256:ℝ)
    (497/512:ℝ) (25237/25000000000000:ℝ) (1643123144931/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_248
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1489).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^0*thetaFirstMode x) ≤ (3948596331553/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/32:ℝ) (249/256:ℝ)
    (27459/25000000000000:ℝ) (371/400000000000:ℝ) (1643123144931/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_248 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_249 :
    (832778675947/250000000000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (249/256:ℝ) (125/128:ℝ)
    (499/512:ℝ) (85187/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_249
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1495).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x) ≤ (3332204186173/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (249/256:ℝ) (125/128:ℝ)
    (371/400000000000:ℝ) (78217/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_249 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_250 :
    (1403664758289/500000000000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (125/128:ℝ) (251/256:ℝ)
    (501/512:ℝ) (71791/100000000000000:ℝ) (301343536891/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_250
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1501).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^0*thetaFirstMode x) ≤ (2808251123093/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (125/128:ℝ) (251/256:ℝ)
    (78217/100000000000000:ℝ) (4117/6250000000000:ℝ) (301343536891/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_250 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_251 :
    (1181337971201/500000000000000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (251/256:ℝ) (63/64:ℝ)
    (503/512:ℝ) (60419/100000000000000:ℝ) (2060581617/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_251
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1507).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x) ≤ (590869060049/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (251/256:ℝ) (63/64:ℝ)
    (4117/6250000000000:ℝ) (277/500000000000:ℝ) (2060581617/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_251 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_252 :
    (992849854653/500000000000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (63/64:ℝ) (253/256:ℝ)
    (505/512:ℝ) (25389/50000000000000:ℝ) (439714250091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_252
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1513).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^0*thetaFirstMode x) ≤ (1986432612637/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/64:ℝ) (253/256:ℝ)
    (277/500000000000:ℝ) (46529/100000000000000:ℝ) (439714250091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_252 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_253 :
    (26041051431/15625000000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (253/256:ℝ) (127/128:ℝ)
    (507/512:ℝ) (21309/50000000000000:ℝ) (149921195583/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_253
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1519).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x) ≤ (1667233698081/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (253/256:ℝ) (127/128:ℝ)
    (46529/100000000000000:ℝ) (2439/6250000000000:ℝ) (149921195583/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_253 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_254 :
    (1396858065781/1000000000000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (127/128:ℝ) (255/256:ℝ)
    (509/512:ℝ) (35719/100000000000000:ℝ) (39878476441/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_254
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1525).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^0*thetaFirstMode x) ≤ (1397377618437/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (127/128:ℝ) (255/256:ℝ)
    (2439/6250000000000:ℝ) (8171/25000000000000:ℝ) (39878476441/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_254 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_255 :
    (1169120373083/1000000000000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (255/256:ℝ) (1/1:ℝ)
    (511/512:ℝ) (5979/20000000000000:ℝ) (108469580301/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_255
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1531).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x) ≤ (1169571753833/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (255/256:ℝ) (1/1:ℝ)
    (8171/25000000000000:ℝ) (3417/12500000000000:ℝ) (108469580301/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_255 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator

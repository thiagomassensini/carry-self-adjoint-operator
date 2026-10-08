import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature7

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_224 :
    (72291296006119/1000000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (7/8:ℝ) (225/256:ℝ)
    (1609598370787246343/1835425813694056448:ℝ) (4065821/100000000000000:ℝ) (45469611906907/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_224
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1348).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^6*thetaFirstMode x) ≤ (72304302067953/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/8:ℝ) (225/256:ℝ)
    (136283/3125000000000:ℝ) (379193/10000000000000:ℝ) (45469611906907/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_224 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_225 :
    (4032544222071/62500000000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (225/256:ℝ) (113/128:ℝ)
    (1660461446893028857/1885028606660507648:ℝ) (1766629/50000000000000:ℝ) (20070903384091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_225
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1354).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x) ≤ (64532584329573/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (225/256:ℝ) (113/128:ℝ)
    (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ) (20070903384091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_225 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_226 :
    (28757174966287/500000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (113/128:ℝ) (227/256:ℝ)
    (1712696009065125735/1935743510899152896:ℝ) (3067027/100000000000000:ℝ) (35398370214817/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_226
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1360).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^6*thetaFirstMode x) ≤ (1438129553823/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (113/128:ℝ) (227/256:ℝ)
    (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ) (35398370214817/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_226 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_227 :
    (1600161649243/31250000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (227/256:ℝ) (57/64:ℝ)
    (1766332737496293785/1987590384755320832:ℝ) (2659323/100000000000000:ℝ) (15590014330449/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_227
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1366).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x) ≤ (640188082421/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (227/256:ℝ) (57/64:ℝ)
    (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ) (15590014330449/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_227 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_228 :
    (45531171427607/1000000000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (57/64:ℝ) (229/256:ℝ)
    (1821402858995508775/2040589351345350656:ℝ) (2303203/100000000000000:ℝ) (27432954452633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_228
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1372).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^6*thetaFirstMode x) ≤ (2846258697051/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (57/64:ℝ) (229/256:ℝ)
    (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ) (27432954452633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_228 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_229 :
    (20217499781869/500000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (229/256:ℝ) (115/128:ℝ)
    (1877938154259808473/2094760800899667968:ℝ) (1992493/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_229
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1378).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x) ≤ (808863256367/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (229/256:ℝ) (115/128:ℝ)
    (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_229 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_230 :
    (1434552780031/40000000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (115/128:ℝ) (231/256:ℝ)
    (1935970965210345287/2150125393116182528:ℝ) (344343/20000000000000:ℝ) (10581051391233/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_230
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1384).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^6*thetaFirstMode x) ≤ (7174245717569/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (115/128:ℝ) (231/256:ℝ)
    (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ) (10581051391233/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_230 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_231 :
    (15884457815161/500000000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (231/256:ℝ) (29/32:ℝ)
    (1995534202392930745/2206704059524007936:ℝ) (1486009/100000000000000:ℝ) (9277074693267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_231
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1390).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x) ≤ (31775628205981/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (231/256:ℝ) (29/32:ℝ)
    (40007/2500000000000:ℝ) (690197/50000000000000:ℝ) (9277074693267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_231 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_232 :
    (3513190001547/125000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (29/32:ℝ) (233/256:ℝ)
    (2056661352443354055/2264518005857503232:ℝ) (80067/6250000000000:ℝ) (16248401359171/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_232
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1396).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^6*thetaFirstMode x) ≤ (14055796372501/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (29/32:ℝ) (233/256:ℝ)
    (690197/50000000000000:ℝ) (297331/25000000000000:ℝ) (16248401359171/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_232 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_233 :
    (6208124497163/250000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (233/256:ℝ) (117/128:ℝ)
    (2119386485617756985/2323588714440636416:ℝ) (137887/12500000000000:ℝ) (14212279360473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_233
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1402).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x) ≤ (12419000705839/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (233/256:ℝ) (117/128:ℝ)
    (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_233 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_234 :
    (2739022232241/125000000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (117/128:ℝ) (235/256:ℝ)
    (2183744263388347303/2383937946581669888:ℝ) (474359/50000000000000:ℝ) (1552051974267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_234
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1408).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^6*thetaFirstMode x) ≤ (21917145851001/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (117/128:ℝ) (235/256:ℝ)
    (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ) (1552051974267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_234 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_235 :
    (19310054385513/1000000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (235/256:ℝ) (59/64:ℝ)
    (2249769946104733017/2445587744978167808:ℝ) (814969/100000000000000:ℝ) (5417188802421/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_235
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1414).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x) ≤ (19314523246023/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (235/256:ℝ) (59/64:ℝ)
    (879727/100000000000000:ℝ) (3021/400000000000:ℝ) (5417188802421/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_235 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_236 :
    (106215912679/6250000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (59/64:ℝ) (237/256:ℝ)
    (2317499400721159655/2508560436132325376:ℝ) (69923/10000000000000:ℝ) (2360604497989/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_236
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1420).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^6*thetaFirstMode x) ≤ (16998587998173/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (59/64:ℝ) (237/256:ℝ)
    (3021/400000000000:ℝ) (1619/250000000000:ℝ) (2360604497989/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_236 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_237 :
    (7468462518451/500000000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (237/256:ℝ) (119/128:ℝ)
    (2386969108589932825/2572878632776620032:ℝ) (599199/100000000000000:ℝ) (8219203312331/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_237
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1426).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x) ≤ (1867568883079/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (237/256:ℝ) (119/128:ℝ)
    (1619/250000000000:ℝ) (69327/12500000000000:ℝ) (8219203312331/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_237 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_238 :
    (13110949180469/1000000000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (119/128:ℝ) (239/256:ℝ)
    (2458216173321308295/2638565236309784576:ℝ) (512849/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_238
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1432).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^6*thetaFirstMode x) ≤ (13114204302743/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (119/128:ℝ) (239/256:ℝ)
    (69327/12500000000000:ℝ) (474399/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_238 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_239 :
    (11492775884919/1000000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (239/256:ℝ) (15/16:ℝ)
    (2531278328710131833/2705643439243102208:ℝ) (438401/100000000000000:ℝ) (155112952199/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_239
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1438).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x) ≤ (5747845614457/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (239/256:ℝ) (15/16:ℝ)
    (474399/100000000000000:ℝ) (405281/100000000000000:ℝ) (155112952199/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_239 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_240 :
    (10060708171013/1000000000000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (15/16:ℝ) (241/256:ℝ)
    (2606193946729511047/2774136727657023488:ℝ) (374293/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_240
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1444).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^6*thetaFirstMode x) ≤ (10063342366267/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (15/16:ℝ) (241/256:ℝ)
    (405281/100000000000000:ℝ) (345801/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_240 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_241 :
    (4397566666773/500000000000000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (241/256:ℝ) (121/128:ℝ)
    (2683002045591801465/2844068883668105216:ℝ) (319159/100000000000000:ℝ) (582524031463/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_241
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1450).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^6*thetaFirstMode x) ≤ (2199373961427/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (241/256:ℝ) (121/128:ℝ)
    (345801/100000000000000:ℝ) (147339/50000000000000:ℝ) (582524031463/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_241 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_242 :
    (7678271756717/1000000000000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (121/128:ℝ) (243/256:ℝ)
    (2761742297877189095/2915463987906271232:ℝ) (271803/100000000000000:ℝ) (2015550292363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_242
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1456).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^6*thetaFirstMode x) ≤ (1536072965283/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (121/128:ℝ) (243/256:ℝ)
    (147339/50000000000000:ℝ) (50159/20000000000000:ℝ) (2015550292363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_242 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_243 :
    (1338799118741/200000000000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (243/256:ℝ) (61/64:ℝ)
    (2842455038730151705/2988346422002395136:ℝ) (115589/50000000000000:ℝ) (3482453219147/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_243
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1462).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^6*thetaFirstMode x) ≤ (6695876988199/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (243/256:ℝ) (61/64:ℝ)
    (50159/20000000000000:ℝ) (106587/50000000000000:ℝ) (3482453219147/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_243 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_244 :
    (5827795728967/1000000000000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (61/64:ℝ) (245/256:ℝ)
    (2925181274124081063/3062740871086204928:ℝ) (49093/25000000000000:ℝ) (3004587016079/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_244
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1468).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^6*thetaFirstMode x) ≤ (364342962723/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (61/64:ℝ) (245/256:ℝ)
    (106587/50000000000000:ℝ) (90481/50000000000000:ℝ) (3004587016079/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_244 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_245 :
    (158331986671/31250000000000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (245/256:ℝ) (123/128:ℝ)
    (3009962689194348377/3138672326294509568:ℝ) (166591/100000000000000:ℝ) (647229882051/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_245
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1474).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^6*thetaFirstMode x) ≤ (5068131081347/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (245/256:ℝ) (123/128:ℝ)
    (90481/50000000000000:ℝ) (153419/100000000000000:ℝ) (647229882051/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_245 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_246 :
    (4398682151041/1000000000000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (123/128:ℝ) (247/256:ℝ)
    (3096841656640095175/3216166087289747456:ℝ) (70571/50000000000000:ℝ) (445562075193/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_246
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1480).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^6*thetaFirstMode x) ≤ (4400032559873/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (123/128:ℝ) (247/256:ℝ)
    (153419/100000000000000:ℝ) (129897/100000000000000:ℝ) (445562075193/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_246 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_247 :
    (953354373269/250000000000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (247/256:ℝ) (31/32:ℝ)
    (3185861245195031865/3295247764788856832:ℝ) (933/781250000000:ℝ) (1914543067207/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_247
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1486).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^6*thetaFirstMode x) ≤ (953647918637/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (247/256:ℝ) (31/32:ℝ)
    (129897/100000000000000:ℝ) (27459/25000000000000:ℝ) (1914543067207/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_247 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_248 :
    (412661416821/125000000000000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (31/32:ℝ) (249/256:ℝ)
    (3277065228167526215/3375943283102468096:ℝ) (100913/100000000000000:ℝ) (1643123144931/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_248
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1492).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^6*thetaFirstMode x) ≤ (660468900959/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (31/32:ℝ) (249/256:ℝ)
    (27459/25000000000000:ℝ) (371/400000000000:ℝ) (1643123144931/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_248 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_249 :
    (2853869339699/1000000000000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (249/256:ℝ) (125/128:ℝ)
    (3370498092050263993/3458278882684418048:ℝ) (42579/50000000000000:ℝ) (1408286069707/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_249
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1498).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^6*thetaFirstMode x) ≤ (2854799047303/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (249/256:ℝ) (125/128:ℝ)
    (371/400000000000:ℝ) (78217/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_249 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_250 :
    (2463528080657/1000000000000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (125/128:ℝ) (251/256:ℝ)
    (3466205045199764007/3542281122691586048:ℝ) (35883/50000000000000:ℝ) (301343536891/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_250
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1504).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^6*thetaFirstMode x) ≤ (2464349559199/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (125/128:ℝ) (251/256:ℝ)
    (78217/100000000000000:ℝ) (4117/6250000000000:ℝ) (301343536891/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_250 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_251 :
    (1061744607667/500000000000000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (251/256:ℝ) (63/64:ℝ)
    (3564232026586029785/3627976883554052096:ℝ) (30199/50000000000000:ℝ) (2060581617/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_251
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1510).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^6*thetaFirstMode x) ≤ (2124215215937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (251/256:ℝ) (63/64:ℝ)
    (4117/6250000000000:ℝ) (277/500000000000:ℝ) (2060581617/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_251 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_252 :
    (1827701686903/1000000000000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (63/64:ℝ) (253/256:ℝ)
    (3664625714612620135/3715393369555576832:ℝ) (50761/100000000000000:ℝ) (439714250091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_252
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1516).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^6*thetaFirstMode x) ≤ (1828356233287/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (63/64:ℝ) (253/256:ℝ)
    (277/500000000000:ℝ) (46529/100000000000000:ℝ) (439714250091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_252 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_253 :
    (1570804728161/1000000000000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (253/256:ℝ) (127/128:ℝ)
    (3767433536007420825/3804558111424403456:ℝ) (42603/100000000000000:ℝ) (149921195583/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_253
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1522).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^6*thetaFirstMode x) ≤ (1571383822921/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (253/256:ℝ) (127/128:ℝ)
    (46529/100000000000000:ℝ) (2439/6250000000000:ℝ) (149921195583/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_253 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_254 :
    (1347999286927/1000000000000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (127/128:ℝ) (255/256:ℝ)
    (3872703674784399623/3895498968934381568:ℝ) (17853/50000000000000:ℝ) (39878476441/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_254
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1528).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^6*thetaFirstMode x) ≤ (6742607237/5000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (127/128:ℝ) (255/256:ℝ)
    (2439/6250000000000:ℝ) (8171/25000000000000:ℝ) (39878476441/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_254 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_255 :
    (1155083867369/1000000000000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (255/256:ℝ) (1/1:ℝ)
    (3980485081276626937/3988244133516412928:ℝ) (7471/25000000000000:ℝ) (108469580301/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_255
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1534).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^6*thetaFirstMode x) ≤ (1155550684657/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (255/256:ℝ) (1/1:ℝ)
    (8171/25000000000000:ℝ) (3417/12500000000000:ℝ) (108469580301/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_255 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature7

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_2_224 :
    (122253282131709/1000000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (7/8:ℝ) (225/256:ℝ)
    (135778947/154829824:ℝ) (813333/20000000000000:ℝ) (45469611906907/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_224
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1346).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^2*thetaFirstMode x) ≤ (6113764905559/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (7/8:ℝ) (225/256:ℝ)
    (136283/3125000000000:ℝ) (379193/10000000000000:ℝ) (45469611906907/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_224 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_225 :
    (53594872284079/500000000000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (225/256:ℝ) (113/128:ℝ)
    (137601453/156212224:ℝ) (1766997/50000000000000:ℝ) (20070903384091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_225
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1352).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x) ≤ (107209494646463/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (225/256:ℝ) (113/128:ℝ)
    (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ) (20070903384091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_225 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_226 :
    (46936865171689/500000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (113/128:ℝ) (227/256:ℝ)
    (139440195/157600768:ℝ) (766917/25000000000000:ℝ) (35398370214817/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_226
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1358).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^2*thetaFirstMode x) ≤ (9389143084387/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (113/128:ℝ) (227/256:ℝ)
    (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ) (35398370214817/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_226 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_227 :
    (8211629836773/100000000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (227/256:ℝ) (57/64:ℝ)
    (141295245/158995456:ℝ) (2659881/100000000000000:ℝ) (15590014330449/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_227
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1364).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x) ≤ (10266517879011/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (227/256:ℝ) (57/64:ℝ)
    (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ) (15590014330449/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_227 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_228 :
    (14349459519407/200000000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (57/64:ℝ) (229/256:ℝ)
    (143166675/160396288:ℝ) (287961/12500000000000:ℝ) (27432954452633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_228
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1370).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^2*thetaFirstMode x) ≤ (14352287502941/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (57/64:ℝ) (229/256:ℝ)
    (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ) (27432954452633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_228 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_229 :
    (62613592002517/1000000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (229/256:ℝ) (115/128:ℝ)
    (145054557/161803264:ℝ) (996457/50000000000000:ℝ) (12054189803443/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_229
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1376).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x) ≤ (12525248507991/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (229/256:ℝ) (115/128:ℝ)
    (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_229 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_230 :
    (852776395983/15625000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (115/128:ℝ) (231/256:ℝ)
    (146958963/163216384:ℝ) (10763/625000000000:ℝ) (10581051391233/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_230
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1382).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^2*thetaFirstMode x) ≤ (54588975944511/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (115/128:ℝ) (231/256:ℝ)
    (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ) (10581051391233/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_230 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_231 :
    (1900645357213/40000000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (231/256:ℝ) (29/32:ℝ)
    (148879965/164635648:ℝ) (59453/4000000000000:ℝ) (9277074693267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_231
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1388).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x) ≤ (23763094542683/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (231/256:ℝ) (29/32:ℝ)
    (40007/2500000000000:ℝ) (690197/50000000000000:ℝ) (9277074693267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_231 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_232 :
    (20659181138803/500000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (29/32:ℝ) (233/256:ℝ)
    (150817635/166061056:ℝ) (640673/50000000000000:ℝ) (16248401359171/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_232
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1394).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^2*thetaFirstMode x) ≤ (8265456818209/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (29/32:ℝ) (233/256:ℝ)
    (690197/50000000000000:ℝ) (297331/25000000000000:ℝ) (16248401359171/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_232 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_233 :
    (35885307388321/1000000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (233/256:ℝ) (117/128:ℝ)
    (152772045/167492608:ℝ) (1103333/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_233
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1400).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x) ≤ (1794662427287/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (233/256:ℝ) (117/128:ℝ)
    (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_233 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_234 :
    (486382721373/15625000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (117/128:ℝ) (235/256:ℝ)
    (154743267/168930304:ℝ) (474461/50000000000000:ℝ) (1552051974267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_234
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1406).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^2*thetaFirstMode x) ≤ (31135560362903/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (117/128:ℝ) (235/256:ℝ)
    (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ) (1552051974267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_234 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_235 :
    (13484482776523/500000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (235/256:ℝ) (59/64:ℝ)
    (156731373/170374144:ℝ) (163029/20000000000000:ℝ) (5417188802421/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_235
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1412).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x) ≤ (26975210557257/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (235/256:ℝ) (59/64:ℝ)
    (879727/100000000000000:ℝ) (3021/400000000000:ℝ) (5417188802421/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_235 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_236 :
    (11668099464103/500000000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (59/64:ℝ) (237/256:ℝ)
    (158736435/171824128:ℝ) (349691/50000000000000:ℝ) (2360604497989/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_236
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1418).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^2*thetaFirstMode x) ≤ (2334173781823/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (59/64:ℝ) (237/256:ℝ)
    (3021/400000000000:ℝ) (1619/250000000000:ℝ) (2360604497989/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_236 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_237 :
    (20167519732081/1000000000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (237/256:ℝ) (119/128:ℝ)
    (160758525/173280256:ℝ) (59933/10000000000000:ℝ) (8219203312331/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_237
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1424).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x) ≤ (10086198426563/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (237/256:ℝ) (119/128:ℝ)
    (1619/250000000000:ℝ) (69327/12500000000000:ℝ) (8219203312331/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_237 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_238 :
    (8703547839547/500000000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (119/128:ℝ) (239/256:ℝ)
    (162797715/174742528:ℝ) (512961/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_238
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1430).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^2*thetaFirstMode x) ≤ (1741141952847/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (119/128:ℝ) (239/256:ℝ)
    (69327/12500000000000:ℝ) (474399/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_238 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_239 :
    (750272305679/50000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (239/256:ℝ) (15/16:ℝ)
    (164854077/176210944:ℝ) (438497/100000000000000:ℝ) (155112952199/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_239
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1436).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x) ≤ (15009257743141/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (239/256:ℝ) (15/16:ℝ)
    (474399/100000000000000:ℝ) (405281/100000000000000:ℝ) (155112952199/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_239 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_240 :
    (1614825362911/125000000000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (15/16:ℝ) (241/256:ℝ)
    (166927683/177685504:ℝ) (46797/12500000000000:ℝ) (5380608354027/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_240
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1442).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^2*thetaFirstMode x) ≤ (12921964706591/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (15/16:ℝ) (241/256:ℝ)
    (405281/100000000000000:ℝ) (345801/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_240 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_241 :
    (11107634629447/1000000000000000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (241/256:ℝ) (121/128:ℝ)
    (169018605/179166208:ℝ) (31923/10000000000000:ℝ) (582524031463/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_241
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1448).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^2*thetaFirstMode x) ≤ (11110601950299/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (241/256:ℝ) (121/128:ℝ)
    (345801/100000000000000:ℝ) (147339/50000000000000:ℝ) (582524031463/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_241 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_242 :
    (9538136502289/1000000000000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (121/128:ℝ) (243/256:ℝ)
    (171126915/180653056:ℝ) (271863/100000000000000:ℝ) (2015550292363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_242
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1454).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^2*thetaFirstMode x) ≤ (238518669273/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (121/128:ℝ) (243/256:ℝ)
    (147339/50000000000000:ℝ) (50159/20000000000000:ℝ) (2015550292363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_242 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_243 :
    (8179685298627/1000000000000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (243/256:ℝ) (61/64:ℝ)
    (173252685/182146048:ℝ) (231229/100000000000000:ℝ) (3482453219147/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_243
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1460).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^2*thetaFirstMode x) ≤ (2045500261859/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (243/256:ℝ) (61/64:ℝ)
    (50159/20000000000000:ℝ) (106587/50000000000000:ℝ) (3482453219147/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_243 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_244 :
    (7005473094451/1000000000000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (61/64:ℝ) (245/256:ℝ)
    (175395987/183645184:ℝ) (3069/1562500000000:ℝ) (3004587016079/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_244
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1466).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^2*thetaFirstMode x) ≤ (3503751411327/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (61/64:ℝ) (245/256:ℝ)
    (106587/50000000000000:ℝ) (90481/50000000000000:ℝ) (3004587016079/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_244 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_245 :
    (748984945563/125000000000000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (245/256:ℝ) (123/128:ℝ)
    (177556893/185150464:ℝ) (166629/100000000000000:ℝ) (647229882051/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_245
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1472).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^2*thetaFirstMode x) ≤ (1198728004297/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (245/256:ℝ) (123/128:ℝ)
    (90481/50000000000000:ℝ) (153419/100000000000000:ℝ) (647229882051/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_245 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_246 :
    (639756620493/125000000000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (123/128:ℝ) (247/256:ℝ)
    (179735475/186661888:ℝ) (70587/50000000000000:ℝ) (445562075193/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_246
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1478).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^2*thetaFirstMode x) ≤ (5119616665817/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (123/128:ℝ) (247/256:ℝ)
    (153419/100000000000000:ℝ) (129897/100000000000000:ℝ) (445562075193/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_246 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_247 :
    (873158761009/200000000000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (247/256:ℝ) (31/32:ℝ)
    (181931805/188179456:ℝ) (119451/100000000000000:ℝ) (1914543067207/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_247
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1484).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^2*thetaFirstMode x) ≤ (873427643383/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (247/256:ℝ) (31/32:ℝ)
    (129897/100000000000000:ℝ) (27459/25000000000000:ℝ) (1914543067207/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_247 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_248 :
    (929755653109/250000000000000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (31/32:ℝ) (249/256:ℝ)
    (184145955/189703168:ℝ) (12617/12500000000000:ℝ) (1643123144931/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_248
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1490).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^2*thetaFirstMode x) ≤ (372020560833/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (31/32:ℝ) (249/256:ℝ)
    (27459/25000000000000:ℝ) (371/400000000000:ℝ) (1643123144931/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_248 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_249 :
    (3163737231647/1000000000000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (249/256:ℝ) (125/128:ℝ)
    (186377997/191233024:ℝ) (85177/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_249
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1496).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^2*thetaFirstMode x) ≤ (632956588421/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (249/256:ℝ) (125/128:ℝ)
    (371/400000000000:ℝ) (78217/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_249 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_250 :
    (335958102187/125000000000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (125/128:ℝ) (251/256:ℝ)
    (188628003/192769024:ℝ) (35891/50000000000000:ℝ) (301343536891/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_250
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1502).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^2*thetaFirstMode x) ≤ (84018021249/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (125/128:ℝ) (251/256:ℝ)
    (78217/100000000000000:ℝ) (4117/6250000000000:ℝ) (301343536891/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_250 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_251 :
    (1140041122629/500000000000000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (251/256:ℝ) (63/64:ℝ)
    (190896045/194311168:ℝ) (15103/25000000000000:ℝ) (2060581617/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_251
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1508).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^2*thetaFirstMode x) ≤ (71276779463/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (251/256:ℝ) (63/64:ℝ)
    (4117/6250000000000:ℝ) (277/500000000000:ℝ) (2060581617/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_251 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_252 :
    (96579345379/50000000000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (63/64:ℝ) (253/256:ℝ)
    (193182195/195859456:ℝ) (50773/100000000000000:ℝ) (439714250091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_252
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1514).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^2*thetaFirstMode x) ≤ (241533426437/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (63/64:ℝ) (253/256:ℝ)
    (277/500000000000:ℝ) (46529/100000000000000:ℝ) (439714250091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_252 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_253 :
    (1634045514233/1000000000000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (253/256:ℝ) (127/128:ℝ)
    (195486525/197413888:ℝ) (42613/100000000000000:ℝ) (149921195583/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_253
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1520).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^2*thetaFirstMode x) ≤ (1634642663469/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (253/256:ℝ) (127/128:ℝ)
    (46529/100000000000000:ℝ) (2439/6250000000000:ℝ) (149921195583/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_253 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_254 :
    (1380383937879/1000000000000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (127/128:ℝ) (255/256:ℝ)
    (197809107/198974464:ℝ) (7143/20000000000000:ℝ) (39878476441/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_254
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1526).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^2*thetaFirstMode x) ≤ (138089156329/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (127/128:ℝ) (255/256:ℝ)
    (2439/6250000000000:ℝ) (8171/25000000000000:ℝ) (39878476441/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_254 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_255 :
    (291100949289/250000000000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (255/256:ℝ) (1/1:ℝ)
    (200150013/200541184:ℝ) (29891/100000000000000:ℝ) (108469580301/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_255
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1532).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x) ≤ (582436661627/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (255/256:ℝ) (1/1:ℝ)
    (8171/25000000000000:ℝ) (3417/12500000000000:ℝ) (108469580301/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_255 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

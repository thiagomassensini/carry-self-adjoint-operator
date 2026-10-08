import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature7

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_224 :
    (13897704029137/250000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (7/8:ℝ) (225/256:ℝ)
    (130381348261662627095241/148673423925516220418560:ℝ) (4065399/100000000000000:ℝ) (45469611906907/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_224
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1349).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^8*thetaFirstMode x) ≤ (27800406870303/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/8:ℝ) (225/256:ℝ)
    (136283/3125000000000:ℝ) (379193/10000000000000:ℝ) (45469611906907/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_224 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_225 :
    (12514581533071/250000000000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (225/256:ℝ) (113/128:ℝ)
    (135702249480635062632759/154054636064115110786560:ℝ) (353289/10000000000000:ℝ) (20070903384091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_225
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1355).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^8*thetaFirstMode x) ≤ (25033768597291/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (225/256:ℝ) (113/128:ℝ)
    (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ) (20070903384091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_225 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_226 :
    (9003812277741/200000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (113/128:ℝ) (227/256:ℝ)
    (141215303034674977169457/159605509118049574428160:ℝ) (1533353/50000000000000:ℝ) (35398370214817/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_226
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1361).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^8*thetaFirstMode x) ≤ (45027543510961/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (113/128:ℝ) (227/256:ℝ)
    (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ) (35398370214817/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_226 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_227 :
    (40435261518147/1000000000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (227/256:ℝ) (57/64:ℝ)
    (29385310700934990796995/33066121515527560919552:ℝ) (664761/25000000000000:ℝ) (15590014330449/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_227
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1367).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^8*thetaFirstMode x) ≤ (10110764195719/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (227/256:ℝ) (57/64:ℝ)
    (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ) (15590014330449/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_227 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_228 :
    (3627141644671/100000000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (57/64:ℝ) (229/256:ℝ)
    (152842207727465608740993/171234597812449350300160:ℝ) (28787/1250000000000:ℝ) (27432954452633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_228
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1373).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^8*thetaFirstMode x) ≤ (36278566713211/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (57/64:ℝ) (229/256:ℝ)
    (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ) (27432954452633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_228 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_229 :
    (32494216902107/1000000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (229/256:ℝ) (115/128:ℝ)
    (158968638409273606456191/177322249882403159887360:ℝ) (1992283/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_229
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1379).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^8*thetaFirstMode x) ≤ (507824483413/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (229/256:ℝ) (115/128:ℝ)
    (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_229 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_230 :
    (145362101099/5000000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (115/128:ℝ) (231/256:ℝ)
    (165312387803273059105209/183598439372905969845760:ℝ) (430383/25000000000000:ℝ) (10581051391233/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_230
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1385).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^8*thetaFirstMode x) ≤ (29078432201827/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (115/128:ℝ) (231/256:ℝ)
    (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ) (10581051391233/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_230 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_231 :
    (405888834471/15625000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (231/256:ℝ) (29/32:ℝ)
    (171880171452079192654407/190068149254242844572160:ℝ) (1485851/100000000000000:ℝ) (9277074693267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_231
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1391).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^8*thetaFirstMode x) ≤ (12991185229159/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (231/256:ℝ) (29/32:ℝ)
    (40007/2500000000000:ℝ) (690197/50000000000000:ℝ) (9277074693267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_231 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_232 :
    (23180344904349/1000000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (29/32:ℝ) (233/256:ℝ)
    (35735776399208126994885/39347294353086520381952:ℝ) (256187/20000000000000:ℝ) (16248401359171/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_232
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1397).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^8*thetaFirstMode x) ≤ (23185355516111/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (29/32:ℝ) (233/256:ℝ)
    (690197/50000000000000:ℝ) (297331/25000000000000:ℝ) (16248401359171/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_232 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_233 :
    (20657437430343/1000000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (233/256:ℝ) (117/128:ℝ)
    (185715593048194171355943/203608610322761788188160:ℝ) (551489/50000000000000:ℝ) (14212279360473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_233
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1403).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^8*thetaFirstMode x) ≤ (20662009993453/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (233/256:ℝ) (117/128:ℝ)
    (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_233 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_234 :
    (18384558193249/1000000000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (117/128:ℝ) (235/256:ℝ)
    (192997563136753342300641/210689881453211795484160:ℝ) (118577/12500000000000:ℝ) (1552051974267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_234
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1409).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^8*thetaFirstMode x) ≤ (18388724181121/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (117/128:ℝ) (235/256:ℝ)
    (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ) (1552051974267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_234 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_235 :
    (16339810097109/1000000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (235/256:ℝ) (59/64:ℝ)
    (200532239716009818864159/217985716752994642792960:ℝ) (814881/100000000000000:ℝ) (5417188802421/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_235
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1415).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^8*thetaFirstMode x) ≤ (16343590758681/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (235/256:ℝ) (59/64:ℝ)
    (879727/100000000000000:ℝ) (3021/400000000000:ℝ) (5417188802421/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_235 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_236 :
    (725143215717/50000000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (59/64:ℝ) (237/256:ℝ)
    (208327263246534084091857/225501664871413871772160:ℝ) (139831/20000000000000:ℝ) (2360604497989/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_236
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1421).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^8*thetaFirstMode x) ≤ (7253148370997/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (59/64:ℝ) (237/256:ℝ)
    (3021/400000000000:ℝ) (1619/250000000000:ℝ) (2360604497989/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_236 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_237 :
    (12854931204351/1000000000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (237/256:ℝ) (119/128:ℝ)
    (43278094269113915002275/46648678704053587338752:ℝ) (299567/50000000000000:ℝ) (8219203312331/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_237
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1427).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^8*thetaFirstMode x) ≤ (3214511822047/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (237/256:ℝ) (119/128:ℝ)
    (1619/250000000000:ℝ) (69327/12500000000000:ℝ) (8219203312331/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_237 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_238 :
    (5689339532593/500000000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (119/128:ℝ) (239/256:ℝ)
    (224729903008522098228393/241216691509014397212160:ℝ) (512793/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_238
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1433).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^8*thetaFirstMode x) ≤ (2276300727487/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (119/128:ℝ) (239/256:ℝ)
    (69327/12500000000000:ℝ) (474399/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_238 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_239 :
    (2514529489743/250000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (239/256:ℝ) (15/16:ℝ)
    (233353802902454023413591/249427470805914151528960:ℝ) (438353/100000000000000:ℝ) (155112952199/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_239
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1439).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^8*thetaFirstMode x) ≤ (5030333906977/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (239/256:ℝ) (15/16:ℝ)
    (474399/100000000000000:ℝ) (405281/100000000000000:ℝ) (155112952199/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_239 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_240 :
    (8878495415503/1000000000000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (15/16:ℝ) (241/256:ℝ)
    (242270625732500482869609/257881768625375876508160:ℝ) (93563/25000000000000:ℝ) (5380608354027/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_240
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1445).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^8*thetaFirstMode x) ≤ (8880815495439/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/16:ℝ) (241/256:ℝ)
    (405281/100000000000000:ℝ) (345801/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_240 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_241 :
    (7826313480041/1000000000000000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (241/256:ℝ) (121/128:ℝ)
    (251489040682132561926807/266585749541721770268160:ℝ) (79781/25000000000000:ℝ) (582524031463/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_241
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1451).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^8*thetaFirstMode x) ≤ (1957102354097/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (241/256:ℝ) (121/128:ℝ)
    (345801/100000000000000:ℝ) (147339/50000000000000:ℝ) (582524031463/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_241 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_242 :
    (6889173655959/1000000000000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (121/128:ℝ) (243/256:ℝ)
    (52203587185640050827165/55109141525919324349952:ℝ) (271773/100000000000000:ℝ) (2015550292363/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_242
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1457).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^8*thetaFirstMode x) ≤ (275641922677/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (121/128:ℝ) (243/256:ℝ)
    (147339/50000000000000:ℝ) (50159/20000000000000:ℝ) (2015550292363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_242 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_243 :
    (1513918708547/250000000000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (243/256:ℝ) (61/64:ℝ)
    (270866423231695777103343/284768068631243160732160:ℝ) (14447/6250000000000:ℝ) (3482453219147/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_243
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1463).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^8*thetaFirstMode x) ≤ (3028691907477/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (243/256:ℝ) (61/64:ℝ)
    (50159/20000000000000:ℝ) (106587/50000000000000:ℝ) (3482453219147/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_243 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_244 :
    (2657746656461/500000000000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (61/64:ℝ) (245/256:ℝ)
    (281043842605185699355041/294259392150867570741760:ℝ) (196351/100000000000000:ℝ) (3004587016079/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_244
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1469).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^8*thetaFirstMode x) ≤ (5317010771069/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (61/64:ℝ) (245/256:ℝ)
    (106587/50000000000000:ℝ) (90481/50000000000000:ℝ) (3004587016079/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_244 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_245 :
    (2329553133203/500000000000000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (245/256:ℝ) (123/128:ℝ)
    (291559767057868215806559/304026373876319976271360:ℝ) (166573/100000000000000:ℝ) (647229882051/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_245
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1475).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^8*thetaFirstMode x) ≤ (4660473355457/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (245/256:ℝ) (123/128:ℝ)
    (90481/50000000000000:ℝ) (153419/100000000000000:ℝ) (647229882051/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_245 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_246 :
    (4077885660683/1000000000000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (123/128:ℝ) (247/256:ℝ)
    (302424007419219829279257/314075847828315644700160:ℝ) (70563/50000000000000:ℝ) (445562075193/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_246
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1481).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^8*thetaFirstMode x) ≤ (509892584513/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (123/128:ℝ) (247/256:ℝ)
    (153419/100000000000000:ℝ) (129897/100000000000000:ℝ) (445562075193/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_246 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_247 :
    (1782016173583/500000000000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (247/256:ℝ) (31/32:ℝ)
    (62729323448440729602555/64882957727484714455552:ℝ) (11941/10000000000000:ℝ) (1914543067207/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_247
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1487).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^8*thetaFirstMode x) ≤ (3565144663983/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (247/256:ℝ) (31/32:ℝ)
    (129897/100000000000000:ℝ) (27459/25000000000000:ℝ) (1914543067207/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_247 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_248 :
    (1555202787857/500000000000000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (31/32:ℝ) (249/256:ℝ)
    (325237897787019494300793/335050313849050052508160:ℝ) (50451/50000000000000:ℝ) (1643123144931/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_248
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1493).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^8*thetaFirstMode x) ≤ (777845987147/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/32:ℝ) (249/256:ℝ)
    (27459/25000000000000:ℝ) (371/400000000000:ℝ) (1643123144931/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_248 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_249 :
    (677628810787/250000000000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (249/256:ℝ) (125/128:ℝ)
    (337208403086384037209991/345989686256645754242560:ℝ) (21287/25000000000000:ℝ) (1408286069707/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_249
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1499).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^8*thetaFirstMode x) ≤ (1355703878811/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (249/256:ℝ) (125/128:ℝ)
    (371/400000000000:ℝ) (78217/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_249 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_250 :
    (1179294232411/500000000000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (125/128:ℝ) (251/256:ℝ)
    (349568945093337212835009/357240316263365765762560:ℝ) (35879/50000000000000:ℝ) (301343536891/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_250
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1505).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^8*thetaFirstMode x) ≤ (2359368131801/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (125/128:ℝ) (251/256:ℝ)
    (78217/100000000000000:ℝ) (4117/6250000000000:ℝ) (301343536891/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_250 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_251 :
    (1024644603659/500000000000000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (251/256:ℝ) (63/64:ℝ)
    (362330598912579278694207/368809764272412990108160:ℝ) (60391/100000000000000:ℝ) (2060581617/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_251
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1511).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^8*thetaFirstMode x) ≤ (409998411513/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (251/256:ℝ) (63/64:ℝ)
    (4117/6250000000000:ℝ) (277/500000000000:ℝ) (2060581617/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_251 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_252 :
    (1777887328861/1000000000000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (63/64:ℝ) (253/256:ℝ)
    (75100941623270192936445/76141148621259241175552:ℝ) (10151/20000000000000:ℝ) (439714250091/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_252
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1517).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^8*thetaFirstMode x) ≤ (22231615619/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (63/64:ℝ) (253/256:ℝ)
    (277/500000000000:ℝ) (46529/100000000000000:ℝ) (439714250091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_252 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_253 :
    (1540120106613/1000000000000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (253/256:ℝ) (127/128:ℝ)
    (389102890145877331465743/392936120455235036700160:ℝ) (21299/50000000000000:ℝ) (149921195583/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_253
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1523).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^8*thetaFirstMode x) ≤ (308138080119/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (253/256:ℝ) (127/128:ℝ)
    (46529/100000000000000:ℝ) (2439/6250000000000:ℝ) (149921195583/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_253 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_254 :
    (1332121869019/1000000000000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (127/128:ℝ) (255/256:ℝ)
    (403137041799404128338441/405508921354945001551360:ℝ) (17851/50000000000000:ℝ) (39878476441/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_254
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1529).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^8*thetaFirstMode x) ≤ (1332632335847/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (127/128:ℝ) (255/256:ℝ)
    (2439/6250000000000:ℝ) (8171/25000000000000:ℝ) (39878476441/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_254 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_255 :
    (230095983649/200000000000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (255/256:ℝ) (1/1:ℝ)
    (417619344807863656339959/418432330694036747061760:ℝ) (29881/100000000000000:ℝ) (108469580301/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_255
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1535).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^8*thetaFirstMode x) ≤ (1150926185021/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (255/256:ℝ) (1/1:ℝ)
    (8171/25000000000000:ℝ) (3417/12500000000000:ℝ) (108469580301/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_255 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

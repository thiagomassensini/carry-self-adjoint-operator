import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature7

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^10*thetaFirstMode x) ≤ (42756389786177/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/8:ℝ) (225/256:ℝ)
    (136283/3125000000000:ℝ) (379193/10000000000000:ℝ) (45469611906907/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_224 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^10*thetaFirstMode x) ≤ (38845100177469/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (225/256:ℝ) (113/128:ℝ)
    (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ) (20070903384091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_225 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^10*thetaFirstMode x) ≤ (4405663667517/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (113/128:ℝ) (227/256:ℝ)
    (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ) (35398370214817/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_226 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^10*thetaFirstMode x) ≤ (31936930223537/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (227/256:ℝ) (57/64:ℝ)
    (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ) (15590014330449/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_227 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^10*thetaFirstMode x) ≤ (578014395303/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (57/64:ℝ) (229/256:ℝ)
    (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ) (27432954452633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_228 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^10*thetaFirstMode x) ≤ (26118296851153/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (229/256:ℝ) (115/128:ℝ)
    (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ) (12054189803443/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_229 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^10*thetaFirstMode x) ≤ (736628415273/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (115/128:ℝ) (231/256:ℝ)
    (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ) (10581051391233/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_230 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^10*thetaFirstMode x) ≤ (531136446929/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (231/256:ℝ) (29/32:ℝ)
    (40007/2500000000000:ℝ) (690197/50000000000000:ℝ) (9277074693267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_231 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^10*thetaFirstMode x) ≤ (9561251611101/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (29/32:ℝ) (233/256:ℝ)
    (690197/50000000000000:ℝ) (297331/25000000000000:ℝ) (16248401359171/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_232 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^10*thetaFirstMode x) ≤ (17188229359943/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (233/256:ℝ) (117/128:ℝ)
    (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ) (14212279360473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_233 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^10*thetaFirstMode x) ≤ (3857108351299/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (117/128:ℝ) (235/256:ℝ)
    (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ) (1552051974267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_234 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^10*thetaFirstMode x) ≤ (432178935509/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (235/256:ℝ) (59/64:ℝ)
    (879727/100000000000000:ℝ) (3021/400000000000:ℝ) (5417188802421/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_235 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^10*thetaFirstMode x) ≤ (12379492831629/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (59/64:ℝ) (237/256:ℝ)
    (3021/400000000000:ℝ) (1619/250000000000:ℝ) (2360604497989/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_236 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^10*thetaFirstMode x) ≤ (1106588074151/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (237/256:ℝ) (119/128:ℝ)
    (1619/250000000000:ℝ) (69327/12500000000000:ℝ) (8219203312331/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_237 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^10*thetaFirstMode x) ≤ (4938896044963/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (119/128:ℝ) (239/256:ℝ)
    (69327/12500000000000:ℝ) (474399/100000000000000:ℝ) (1786401178299/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_238 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^10*thetaFirstMode x) ≤ (4402415763719/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (239/256:ℝ) (15/16:ℝ)
    (474399/100000000000000:ℝ) (405281/100000000000000:ℝ) (155112952199/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_239 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^10*thetaFirstMode x) ≤ (7837290546539/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/16:ℝ) (241/256:ℝ)
    (405281/100000000000000:ℝ) (345801/100000000000000:ℝ) (5380608354027/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_240 (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^10*thetaFirstMode x) ≤ (6966112291227/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (241/256:ℝ) (121/128:ℝ)
    (345801/100000000000000:ℝ) (147339/50000000000000:ℝ) (582524031463/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_241 (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^10*thetaFirstMode x) ≤ (3091442494009/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (121/128:ℝ) (243/256:ℝ)
    (147339/50000000000000:ℝ) (50159/20000000000000:ℝ) (2015550292363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_242 (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^10*thetaFirstMode x) ≤ (2739902841221/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (243/256:ℝ) (61/64:ℝ)
    (50159/20000000000000:ℝ) (106587/50000000000000:ℝ) (3482453219147/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_243 (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^10*thetaFirstMode x) ≤ (4849613537251/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (61/64:ℝ) (245/256:ℝ)
    (106587/50000000000000:ℝ) (90481/50000000000000:ℝ) (3004587016079/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_244 (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^10*thetaFirstMode x) ≤ (4285629467443/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (245/256:ℝ) (123/128:ℝ)
    (90481/50000000000000:ℝ) (153419/100000000000000:ℝ) (647229882051/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_245 (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^10*thetaFirstMode x) ≤ (1890835990497/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (123/128:ℝ) (247/256:ℝ)
    (153419/100000000000000:ℝ) (129897/100000000000000:ℝ) (445562075193/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_246 (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^10*thetaFirstMode x) ≤ (666405563399/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (247/256:ℝ) (31/32:ℝ)
    (129897/100000000000000:ℝ) (27459/25000000000000:ℝ) (1914543067207/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_247 (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^10*thetaFirstMode x) ≤ (1465740818909/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (31/32:ℝ) (249/256:ℝ)
    (27459/25000000000000:ℝ) (371/400000000000:ℝ) (1643123144931/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_248 (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^10*thetaFirstMode x) ≤ (2575232523047/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (249/256:ℝ) (125/128:ℝ)
    (371/400000000000:ℝ) (78217/100000000000000:ℝ) (1408286069707/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_249 (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^10*thetaFirstMode x) ≤ (1129435452683/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (125/128:ℝ) (251/256:ℝ)
    (78217/100000000000000:ℝ) (4117/6250000000000:ℝ) (301343536891/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_250 (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^10*thetaFirstMode x) ≤ (1978372778299/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (251/256:ℝ) (63/64:ℝ)
    (4117/6250000000000:ℝ) (277/500000000000:ℝ) (2060581617/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_251 (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^10*thetaFirstMode x) ≤ (865034601339/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (63/64:ℝ) (253/256:ℝ)
    (277/500000000000:ℝ) (46529/100000000000000:ℝ) (439714250091/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_252 (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^10*thetaFirstMode x) ≤ (755302165683/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (253/256:ℝ) (127/128:ℝ)
    (46529/100000000000000:ℝ) (2439/6250000000000:ℝ) (149921195583/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_253 (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^10*thetaFirstMode x) ≤ (658468604577/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (127/128:ℝ) (255/256:ℝ)
    (2439/6250000000000:ℝ) (8171/25000000000000:ℝ) (39878476441/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_254 (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^10*thetaFirstMode x) ≤ (1146326038941/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (255/256:ℝ) (1/1:ℝ)
    (8171/25000000000000:ℝ) (3417/12500000000000:ℝ) (108469580301/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_255 (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes00
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes01
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes02
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes03
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes04
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes05
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes06
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes07
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes08
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes09
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes10
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes11
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes12
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes13
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes14
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes15
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes16
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes17
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes18
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes19
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes20
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes21
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes22
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes23
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes24
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes25
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes26
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes27
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes28
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes29
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes30
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes31
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes32
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes33
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes34
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes35
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes36
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes37
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes38
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes39
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes40
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes41
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes42
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes43
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes44
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes45
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes46
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes47
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes48
import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaFirstMode_refined_cell_lower_2_224 :
    (40992254311/335544320000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/8:ℝ) (225/256:ℝ) (135778947/154829824:ℝ) (813333/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1346).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^2*thetaFirstMode x) ≤ (1232611867399/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/8:ℝ) (225/256:ℝ) (136283/3125000000000:ℝ) (379193/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_225 :
    (89852386449/838860800000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (225/256:ℝ) (113/128:ℝ) (137601453/156212224:ℝ) (1766997/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1352).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x) ≤ (2161526877713/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (225/256:ℝ) (113/128:ℝ) (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_226 :
    (39344631573/419430400000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (113/128:ℝ) (227/256:ℝ) (139440195/157600768:ℝ) (766917/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1358).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^2*thetaFirstMode x) ≤ (631018400749/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (113/128:ℝ) (227/256:ℝ) (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_227 :
    (137665687663/1677721600000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (227/256:ℝ) (57/64:ℝ) (141295245/158995456:ℝ) (2659881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1364).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x) ≤ (276000141971/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (227/256:ℝ) (57/64:ℝ) (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_228 :
    (15035115719/209715200000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (57/64:ℝ) (229/256:ℝ) (143166675/160396288:ℝ) (287961/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1370).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^2*thetaFirstMode x) ≤ (482311379663/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (57/64:ℝ) (229/256:ℝ) (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_229 :
    (157451167027/2516582400000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (229/256:ℝ) (115/128:ℝ) (145054557/161803264:ℝ) (996457/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1376).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x) ≤ (210461725389/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (229/256:ℝ) (115/128:ℝ) (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_230 :
    (1715525333/31457280000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (115/128:ℝ) (231/256:ℝ) (146958963/163216384:ℝ) (10763/625000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1382).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^2*thetaFirstMode x) ≤ (1100736868991/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (115/128:ℝ) (231/256:ℝ) (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_231 :
    (9558674981/201326592000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (231/256:ℝ) (29/32:ℝ) (148879965/164635648:ℝ) (59453/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1388).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x) ≤ (479172920089/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (231/256:ℝ) (29/32:ℝ) (40007/2500000000000:ℝ) (690197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_232 :
    (103897299737/2516582400000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/32:ℝ) (233/256:ℝ) (150817635/166061056:ℝ) (640673/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1394).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^2*thetaFirstMode x) ≤ (416684174567/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/32:ℝ) (233/256:ℝ) (690197/50000000000000:ℝ) (297331/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_233 :
    (180468868811/5033164800000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (233/256:ℝ) (117/128:ℝ) (152772045/167492608:ℝ) (1103333/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1400).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x) ≤ (241269640999/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (233/256:ℝ) (117/128:ℝ) (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_234 :
    (78272305631/2516582400000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (117/128:ℝ) (235/256:ℝ) (154743267/168930304:ℝ) (474461/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1406).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^2*thetaFirstMode x) ≤ (104647244849/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (117/128:ℝ) (235/256:ℝ) (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_235 :
    (9041642683/335544320000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (235/256:ℝ) (59/64:ℝ) (156731373/170374144:ℝ) (163029/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1412).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x) ≤ (543999587807/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (235/256:ℝ) (59/64:ℝ) (879727/100000000000000:ℝ) (3021/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_236 :
    (58677100727/2516582400000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (59/64:ℝ) (237/256:ℝ) (158736435/171824128:ℝ) (349691/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1418).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^2*thetaFirstMode x) ≤ (9414742489/402653184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (59/64:ℝ) (237/256:ℝ) (3021/400000000000:ℝ) (1619/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_237 :
    (10141802327/503316480000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (237/256:ℝ) (119/128:ℝ) (160758525/173280256:ℝ) (59933/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1424).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x) ≤ (50853926401/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (237/256:ℝ) (119/128:ℝ) (1619/250000000000:ℝ) (69327/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_238 :
    (29178418589/1677721600000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (119/128:ℝ) (239/256:ℝ) (162797715/174742528:ℝ) (512961/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1430).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^2*thetaFirstMode x) ≤ (117052793967/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (119/128:ℝ) (239/256:ℝ) (69327/12500000000000:ℝ) (474399/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_239 :
    (75457002257/5033164800000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (239/256:ℝ) (15/16:ℝ) (164854077/176210944:ℝ) (438497/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1436).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x) ≤ (151359660319/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (239/256:ℝ) (15/16:ℝ) (474399/100000000000000:ℝ) (405281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_240 :
    (2706754079/209715200000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/16:ℝ) (241/256:ℝ) (166927683/177685504:ℝ) (46797/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1442).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^2*thetaFirstMode x) ≤ (65157097391/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/16:ℝ) (241/256:ℝ) (405281/100000000000000:ℝ) (345801/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_241 :
    (1861823847/167772160000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (241/256:ℝ) (121/128:ℝ) (169018605/179166208:ℝ) (31923/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1448).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^2*thetaFirstMode x) ≤ (74700228659/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (241/256:ℝ) (121/128:ℝ) (345801/100000000000000:ℝ) (147339/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_242 :
    (15987266199/1677721600000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (121/128:ℝ) (243/256:ℝ) (171126915/180653056:ℝ) (271863/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1454).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^2*thetaFirstMode x) ≤ (192442319119/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (121/128:ℝ) (243/256:ℝ) (147339/50000000000000:ℝ) (50159/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_243 :
    (41130320833/5033164800000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (243/256:ℝ) (61/64:ℝ) (173252685/182146048:ℝ) (231229/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1460).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^2*thetaFirstMode x) ≤ (165040506199/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (243/256:ℝ) (61/64:ℝ) (50159/20000000000000:ℝ) (106587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_244 :
    (183465843/26214400000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (61/64:ℝ) (245/256:ℝ) (175395987/183645184:ℝ) (3069/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1466).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^2*thetaFirstMode x) ≤ (35338434271/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (61/64:ℝ) (245/256:ℝ) (106587/50000000000000:ℝ) (90481/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_245 :
    (10042785373/1677721600000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (245/256:ℝ) (123/128:ℝ) (177556893/185150464:ℝ) (166629/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1472).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^2*thetaFirstMode x) ≤ (120906002369/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (245/256:ℝ) (123/128:ℝ) (90481/50000000000000:ℝ) (153419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_246 :
    (4289030823/838860800000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (123/128:ℝ) (247/256:ℝ) (179735475/186661888:ℝ) (70587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1478).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^2*thetaFirstMode x) ≤ (51639025519/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (123/128:ℝ) (247/256:ℝ) (153419/100000000000000:ℝ) (129897/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_247 :
    (7317130273/1677721600000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (247/256:ℝ) (31/32:ℝ) (181931805/188179456:ℝ) (119451/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1484).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^2*thetaFirstMode x) ≤ (29367019053/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (247/256:ℝ) (31/32:ℝ) (129897/100000000000000:ℝ) (27459/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_248 :
    (2337387569/629145600000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/32:ℝ) (249/256:ℝ) (184145955/189703168:ℝ) (12617/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1490).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^2*thetaFirstMode x) ≤ (37526228731/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/32:ℝ) (249/256:ℝ) (27459/25000000000000:ℝ) (371/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_249 :
    (15906889927/5033164800000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (249/256:ℝ) (125/128:ℝ) (186377997/191233024:ℝ) (85177/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1496).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^2*thetaFirstMode x) ≤ (63849264467/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (249/256:ℝ) (125/128:ℝ) (371/400000000000:ℝ) (78217/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_250 :
    (6756516641/2516582400000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (125/128:ℝ) (251/256:ℝ) (188628003/192769024:ℝ) (35891/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1502).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^2*thetaFirstMode x) ≤ (54243611833/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (125/128:ℝ) (251/256:ℝ) (78217/100000000000000:ℝ) (4117/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_251 :
    (2865899971/1258291200000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (251/256:ℝ) (63/64:ℝ) (190896045/194311168:ℝ) (15103/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1508).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^2*thetaFirstMode x) ≤ (5752394299/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (251/256:ℝ) (63/64:ℝ) (4117/6250000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_252 :
    (9711300937/5033164800000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (63/64:ℝ) (253/256:ℝ) (193182195/195859456:ℝ) (50773/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1514).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^2*thetaFirstMode x) ≤ (38987235947/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (63/64:ℝ) (253/256:ℝ) (277/500000000000:ℝ) (46529/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_253 :
    (8215232431/5033164800000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (253/256:ℝ) (127/128:ℝ) (195486525/197413888:ℝ) (42613/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1520).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^2*thetaFirstMode x) ≤ (32983207387/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (253/256:ℝ) (127/128:ℝ) (46529/100000000000000:ℝ) (2439/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_254 :
    (462654491/335544320000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (127/128:ℝ) (255/256:ℝ) (197809107/198974464:ℝ) (7143/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1526).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^2*thetaFirstMode x) ≤ (6966019829/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (127/128:ℝ) (255/256:ℝ) (2439/6250000000000:ℝ) (8171/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_255 :
    (5853883331/5033164800000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (255/256:ℝ) (1/1:ℝ) (200150013/200541184:ℝ) (29891/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1532).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^2*thetaFirstMode x) ≤ (5876505203/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (255/256:ℝ) (1/1:ℝ) (8171/25000000000000:ℝ) (3417/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

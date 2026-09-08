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

theorem thetaFirstMode_refined_cell_lower_4_224 :
    (51645563791702243/549755813888000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/8:ℝ) (225/256:ℝ) (17108430194245/19508815873536:ℝ) (4066243/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1347).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^4*thetaFirstMode x) ≤ (31059010146855181/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/8:ℝ) (225/256:ℝ) (136283/3125000000000:ℝ) (379193/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_225 :
    (22842889850934563/274877906944000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (225/256:ℝ) (113/128:ℝ) (17492871381755/19858739329536:ℝ) (1766813/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1353).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^4*thetaFirstMode x) ≤ (18317275001332259/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (225/256:ℝ) (113/128:ℝ) (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_226 :
    (10091369814874447/137438953472000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (113/128:ℝ) (227/256:ℝ) (5961397569855/6737783055872:ℝ) (766837/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1359).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^4*thetaFirstMode x) ≤ (80923869322509213/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (113/128:ℝ) (227/256:ℝ) (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_227 :
    (17810924351514261/274877906944000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (227/256:ℝ) (57/64:ℝ) (18282486115075/20572687044096:ℝ) (1329801/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1365).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^4*thetaFirstMode x) ≤ (107125133578718173/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (227/256:ℝ) (57/64:ℝ) (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_228 :
    (6279525429323109/109951162777600000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (57/64:ℝ) (229/256:ℝ) (18687844351085/20936794799616:ℝ) (460689/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1371).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^4*thetaFirstMode x) ≤ (62950290942991581/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (57/64:ℝ) (229/256:ℝ) (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_229 :
    (13496393339023/268435456000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (229/256:ℝ) (115/128:ℝ) (6366786996465/7101904819712:ℝ) (973/48828125000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1377).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^4*thetaFirstMode x) ≤ (13854987664372953/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (229/256:ℝ) (115/128:ℝ) (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_230 :
    (12151649553253299/274877906944000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (115/128:ℝ) (231/256:ℝ) (19520130424405/21679488231936:ℝ) (860949/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1383).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^4*thetaFirstMode x) ≤ (146191732613811311/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (115/128:ℝ) (231/256:ℝ) (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_231 :
    (21342517747872927/549755813888000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (231/256:ℝ) (29/32:ℝ) (19947247876715/22058158511616:ℝ) (1486167/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1389).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^4*thetaFirstMode x) ≤ (64193566372059233/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (231/256:ℝ) (29/32:ℝ) (40007/2500000000000:ℝ) (690197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_232 :
    (18719137355966849/549755813888000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/32:ℝ) (233/256:ℝ) (6793936465575/7480589292032:ℝ) (1281209/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1395).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^4*thetaFirstMode x) ≤ (18768463460139649/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/32:ℝ) (233/256:ℝ) (690197/50000000000000:ℝ) (297331/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_233 :
    (3279530546984933/109951162777600000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (233/256:ℝ) (117/128:ℝ) (20823911868235/22830359087616:ℝ) (220643/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1401).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^4*thetaFirstMode x) ≤ (98649425437530269/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (233/256:ℝ) (117/128:ℝ) (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_234 :
    (717297267170891/27487790694400000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (117/128:ℝ) (235/256:ℝ) (21273653012045/23223975092736:ℝ) (47441/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1407).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^4*thetaFirstMode x) ≤ (2697189287395981/103079215104000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (117/128:ℝ) (235/256:ℝ) (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_235 :
    (12535034892427157/549755813888000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (235/256:ℝ) (59/64:ℝ) (7243710463185/7874219674112:ℝ) (815057/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1413).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^4*thetaFirstMode x) ≤ (25139440210217599/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (235/256:ℝ) (59/64:ℝ) (879727/100000000000000:ℝ) (3021/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_236 :
    (5469350122044993/274877906944000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (59/64:ℝ) (237/256:ℝ) (22196446406365/24026454191616:ℝ) (349653/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1419).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^4*thetaFirstMode x) ≤ (1316336734588273/65970697666560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (59/64:ℝ) (237/256:ℝ) (3021/400000000000:ℝ) (1619/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_237 :
    (297917846733397/17179869184000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (237/256:ℝ) (119/128:ℝ) (22669698315875/24435404100096:ℝ) (18727/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1425).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^4*thetaFirstMode x) ≤ (7170472652851741/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (237/256:ℝ) (119/128:ℝ) (1619/250000000000:ℝ) (69327/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_238 :
    (1659565063794011/109951162777600000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (119/128:ℝ) (239/256:ℝ) (7716996074295/8283184143872:ℝ) (102581/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1431).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^4*thetaFirstMode x) ≤ (16643873895602229/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (119/128:ℝ) (239/256:ℝ) (69327/12500000000000:ℝ) (474399/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_239 :
    (7212983602363649/549755813888000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (239/256:ℝ) (15/16:ℝ) (23640418087195/25268943054336:ℝ) (438449/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1437).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^4*thetaFirstMode x) ≤ (10851426870426599/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (239/256:ℝ) (15/16:ℝ) (474399/100000000000000:ℝ) (405281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_240 :
    (3130857928659567/274877906944000000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/16:ℝ) (241/256:ℝ) (24138090727205/25693620020736:ℝ) (187167/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1443).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^4*thetaFirstMode x) ≤ (18841581256584343/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/16:ℝ) (241/256:ℝ) (405281/100000000000000:ℝ) (345801/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_241 :
    (1085746263209009/109951162777600000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (241/256:ℝ) (121/128:ℝ) (8214703274505/8707875855872:ℝ) (63839/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1449).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^4*thetaFirstMode x) ≤ (10890591244960413/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (241/256:ℝ) (121/128:ℝ) (345801/100000000000000:ℝ) (147339/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_242 :
    (4700270440682763/549755813888000000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (121/128:ℝ) (243/256:ℝ) (25158579922525/26559010116096:ℝ) (271833/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1455).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^4*thetaFirstMode x) ≤ (28289099317468249/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (121/128:ℝ) (243/256:ℝ) (147339/50000000000000:ℝ) (50159/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_243 :
    (1016026138744581/137438953472000000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (243/256:ℝ) (61/64:ℝ) (25681606440035/26999812271616:ℝ) (57801/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1461).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^4*thetaFirstMode x) ≤ (24461513510002093/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (243/256:ℝ) (61/64:ℝ) (50159/20000000000000:ℝ) (106587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_244 :
    (1754637110855497/274877906944000000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (61/64:ℝ) (245/256:ℝ) (8737765221615/9148692941312:ℝ) (98197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1467).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^4*thetaFirstMode x) ≤ (440066614679189/68719476736000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (61/64:ℝ) (245/256:ℝ) (106587/50000000000000:ℝ) (90481/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_245 :
    (302608175743511/54975581388800000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (245/256:ℝ) (123/128:ℝ) (26753754762355/27897854747136:ℝ) (16661/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1473).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^4*thetaFirstMode x) ≤ (6071891913981639/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (245/256:ℝ) (123/128:ℝ) (90481/50000000000000:ℝ) (153419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_246 :
    (1302917067840949/274877906944000000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (123/128:ℝ) (247/256:ℝ) (27303091778165/28355185199616:ℝ) (70579/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1479).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^4*thetaFirstMode x) ≤ (3921715731528359/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (123/128:ℝ) (247/256:ℝ) (153419/100000000000000:ℝ) (129897/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_247 :
    (2240852385319957/549755813888000000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (247/256:ℝ) (31/32:ℝ) (9287138547225/9606038508032:ℝ) (119437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1485).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^4*thetaFirstMode x) ≤ (4496807338324083/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (247/256:ℝ) (31/32:ℝ) (129897/100000000000000:ℝ) (27459/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_248 :
    (76972898806397/21990232555520000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/32:ℝ) (249/256:ℝ) (28428836169685/29286691247616:ℝ) (4037/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1491).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^4*thetaFirstMode x) ≤ (5792706256192297/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/32:ℝ) (249/256:ℝ) (27459/25000000000000:ℝ) (371/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_249 :
    (103136445226573/34359738368000000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (249/256:ℝ) (125/128:ℝ) (29005464069995/29760958081536:ℝ) (5323/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1497).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^4*thetaFirstMode x) ≤ (9935519608278967/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (249/256:ℝ) (125/128:ℝ) (371/400000000000:ℝ) (78217/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_250 :
    (706547786769637/274877906944000000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (125/128:ℝ) (251/256:ℝ) (9863803648335/10080320640512:ℝ) (35887/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1503).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^4*thetaFirstMode x) ≤ (2836195587550859/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (125/128:ℝ) (251/256:ℝ) (78217/100000000000000:ℝ) (4117/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_251 :
    (241673081268261/109951162777600000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (251/256:ℝ) (63/64:ℝ) (30186789295315/30726748847616:ℝ) (12081/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1509).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^4*thetaFirstMode x) ≤ (909531580538663/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (251/256:ℝ) (63/64:ℝ) (4117/6250000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_252 :
    (1031811681155587/549755813888000000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (63/64:ℝ) (253/256:ℝ) (30791712523325/31218365124096:ℝ) (50767/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1515).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^4*thetaFirstMode x) ≤ (2071175490234399/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (63/64:ℝ) (253/256:ℝ) (277/500000000000:ℝ) (46529/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_253 :
    (54986541486053/34359738368000000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (253/256:ℝ) (127/128:ℝ) (10468764978945/10571952399872:ℝ) (2663/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1521).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^4*thetaFirstMode x) ≤ (1766120285192003/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (253/256:ℝ) (127/128:ℝ) (46529/100000000000000:ℝ) (2439/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_254 :
    (749077091102561/549755813888000000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (127/128:ℝ) (255/256:ℝ) (32030651752645/32219271707136:ℝ) (35711/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1527).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^4*thetaFirstMode x) ≤ (1127853735146351/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (127/128:ℝ) (255/256:ℝ) (2439/6250000000000:ℝ) (8171/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_255 :
    (9950704493267/8589934592000000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (255/256:ℝ) (1/1:ℝ) (32664899100155/32728655463936:ℝ) (467/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1533).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^4*thetaFirstMode x) ≤ (958943943689801/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (255/256:ℝ) (1/1:ℝ) (8171/25000000000000:ℝ) (3417/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

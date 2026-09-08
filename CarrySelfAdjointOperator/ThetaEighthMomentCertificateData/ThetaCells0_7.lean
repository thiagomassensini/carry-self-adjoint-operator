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

theorem thetaFirstMode_refined_cell_lower_0_224 :
    (254193/1600000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(225/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (7/8:ℝ) (225/256:ℝ) (449/512:ℝ) (254193/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1345).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_224 :
    (∫ x in (7/8:ℝ)..(225/256:ℝ), x^0*thetaFirstMode x) ≤ (4076493/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (7/8:ℝ) (225/256:ℝ) (136283/3125000000000:ℝ) (379193/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_225 :
    (1767181/12800000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (225/256:ℝ) (113/128:ℝ) (451/512:ℝ) (1767181/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1351).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_225 :
    (∫ x in (225/256:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x) ≤ (7085341/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (225/256:ℝ) (113/128:ℝ) (379193/10000000000000:ℝ) (3293411/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_226 :
    (3067989/25600000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(227/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (113/128:ℝ) (227/256:ℝ) (453/512:ℝ) (3067989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1357).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_226 :
    (∫ x in (113/128:ℝ)..(227/256:ℝ), x^0*thetaFirstMode x) ≤ (6150639/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (113/128:ℝ) (227/256:ℝ) (3293411/100000000000000:ℝ) (714307/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_227 :
    (8313/80000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (227/256:ℝ) (57/64:ℝ) (455/512:ℝ) (8313/312500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1363).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_227 :
    (∫ x in (227/256:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x) ≤ (2666621/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (227/256:ℝ) (57/64:ℝ) (714307/25000000000000:ℝ) (1238007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_228 :
    (230393/2560000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(229/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (57/64:ℝ) (229/256:ℝ) (457/512:ℝ) (230393/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1369).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_228 :
    (∫ x in (57/64:ℝ)..(229/256:ℝ), x^0*thetaFirstMode x) ≤ (923847/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (57/64:ℝ) (229/256:ℝ) (1238007/50000000000000:ℝ) (2143221/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_229 :
    (3189/40960000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (229/256:ℝ) (115/128:ℝ) (459/512:ℝ) (3189/160000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1375).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_229 :
    (∫ x in (229/256:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x) ≤ (999063/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (229/256:ℝ) (115/128:ℝ) (2143221/100000000000000:ℝ) (1853031/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_230 :
    (1722263/25600000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(231/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (115/128:ℝ) (231/256:ℝ) (461/512:ℝ) (1722263/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1381).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_230 :
    (∫ x in (115/128:ℝ)..(231/256:ℝ), x^0*thetaFirstMode x) ≤ (3453311/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (115/128:ℝ) (231/256:ℝ) (1853031/100000000000000:ℝ) (40007/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_231 :
    (371621/6400000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (231/256:ℝ) (29/32:ℝ) (463/512:ℝ) (371621/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1387).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_231 :
    (∫ x in (231/256:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x) ≤ (1490337/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (231/256:ℝ) (29/32:ℝ) (40007/2500000000000:ℝ) (690197/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_232 :
    (1281483/25600000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(233/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (29/32:ℝ) (233/256:ℝ) (465/512:ℝ) (1281483/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1393).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_232 :
    (∫ x in (29/32:ℝ)..(233/256:ℝ), x^0*thetaFirstMode x) ≤ (1284859/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (29/32:ℝ) (233/256:ℝ) (690197/50000000000000:ℝ) (297331/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_233 :
    (1103451/25600000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (233/256:ℝ) (117/128:ℝ) (467/512:ℝ) (1103451/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1399).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_233 :
    (∫ x in (233/256:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x) ≤ (2212813/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (233/256:ℝ) (117/128:ℝ) (297331/25000000000000:ℝ) (1023489/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_234 :
    (37961/1024000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(235/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (117/128:ℝ) (235/256:ℝ) (469/512:ℝ) (37961/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1405).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_234 :
    (∫ x in (117/128:ℝ)..(235/256:ℝ), x^0*thetaFirstMode x) ≤ (118951/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (117/128:ℝ) (235/256:ℝ) (1023489/100000000000000:ℝ) (879727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_235 :
    (815233/25600000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (235/256:ℝ) (59/64:ℝ) (471/512:ℝ) (815233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1411).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_235 :
    (∫ x in (235/256:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x) ≤ (1634977/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (235/256:ℝ) (59/64:ℝ) (879727/100000000000000:ℝ) (3021/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_236 :
    (349729/12800000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(237/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (59/64:ℝ) (237/256:ℝ) (473/512:ℝ) (349729/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1417).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_236 :
    (∫ x in (59/64:ℝ)..(237/256:ℝ), x^0*thetaFirstMode x) ≤ (28057/1024000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (59/64:ℝ) (237/256:ℝ) (3021/400000000000:ℝ) (1619/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_237 :
    (119879/5120000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (237/256:ℝ) (119/128:ℝ) (475/512:ℝ) (119879/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1423).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_237 :
    (∫ x in (237/256:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x) ≤ (150277/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (237/256:ℝ) (119/128:ℝ) (1619/250000000000:ℝ) (69327/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_238 :
    (513017/25600000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(239/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (119/128:ℝ) (239/256:ℝ) (477/512:ℝ) (513017/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1429).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_238 :
    (∫ x in (119/128:ℝ)..(239/256:ℝ), x^0*thetaFirstMode x) ≤ (205803/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (119/128:ℝ) (239/256:ℝ) (69327/12500000000000:ℝ) (474399/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_239 :
    (87709/5120000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (239/256:ℝ) (15/16:ℝ) (479/512:ℝ) (87709/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1435).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_239 :
    (∫ x in (239/256:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x) ≤ (2749/160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (239/256:ℝ) (15/16:ℝ) (474399/100000000000000:ℝ) (405281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_240 :
    (374417/25600000000000000:ℝ) ≤ ∫ x in (15/16:ℝ)..(241/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (15/16:ℝ) (241/256:ℝ) (481/512:ℝ) (374417/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1441).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_240 :
    (∫ x in (15/16:ℝ)..(241/256:ℝ), x^0*thetaFirstMode x) ≤ (375541/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (15/16:ℝ) (241/256:ℝ) (405281/100000000000000:ℝ) (345801/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1440).2 (thetaFirstMode_refined_node_1446).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_241 :
    (63853/5120000000000000:ℝ) ≤ ∫ x in (241/256:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (241/256:ℝ) (121/128:ℝ) (483/512:ℝ) (63853/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1447).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_241 :
    (∫ x in (241/256:ℝ)..(121/128:ℝ), x^0*thetaFirstMode x) ≤ (640479/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (241/256:ℝ) (121/128:ℝ) (345801/100000000000000:ℝ) (147339/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1446).2 (thetaFirstMode_refined_node_1452).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_242 :
    (271893/25600000000000000:ℝ) ≤ ∫ x in (121/128:ℝ)..(243/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (121/128:ℝ) (243/256:ℝ) (485/512:ℝ) (271893/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1453).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_242 :
    (∫ x in (121/128:ℝ)..(243/256:ℝ), x^0*thetaFirstMode x) ≤ (545473/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (121/128:ℝ) (243/256:ℝ) (147339/50000000000000:ℝ) (50159/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1452).2 (thetaFirstMode_refined_node_1458).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_243 :
    (46251/5120000000000000:ℝ) ≤ ∫ x in (243/256:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (243/256:ℝ) (61/64:ℝ) (487/512:ℝ) (46251/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1459).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_243 :
    (∫ x in (243/256:ℝ)..(61/64:ℝ), x^0*thetaFirstMode x) ≤ (463969/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (243/256:ℝ) (61/64:ℝ) (50159/20000000000000:ℝ) (106587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1458).2 (thetaFirstMode_refined_node_1464).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_244 :
    (98219/12800000000000000:ℝ) ≤ ∫ x in (61/64:ℝ)..(245/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (61/64:ℝ) (245/256:ℝ) (489/512:ℝ) (98219/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1465).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_244 :
    (∫ x in (61/64:ℝ)..(245/256:ℝ), x^0*thetaFirstMode x) ≤ (49267/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (61/64:ℝ) (245/256:ℝ) (106587/50000000000000:ℝ) (90481/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1464).2 (thetaFirstMode_refined_node_1470).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_245 :
    (166647/25600000000000000:ℝ) ≤ ∫ x in (245/256:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (245/256:ℝ) (123/128:ℝ) (491/512:ℝ) (166647/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1471).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_245 :
    (∫ x in (245/256:ℝ)..(123/128:ℝ), x^0*thetaFirstMode x) ≤ (334381/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (245/256:ℝ) (123/128:ℝ) (90481/50000000000000:ℝ) (153419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1470).2 (thetaFirstMode_refined_node_1476).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_246 :
    (14119/2560000000000000:ℝ) ≤ ∫ x in (123/128:ℝ)..(247/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (123/128:ℝ) (247/256:ℝ) (493/512:ℝ) (14119/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1477).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_246 :
    (∫ x in (123/128:ℝ)..(247/256:ℝ), x^0*thetaFirstMode x) ≤ (70829/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (123/128:ℝ) (247/256:ℝ) (153419/100000000000000:ℝ) (129897/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1476).2 (thetaFirstMode_refined_node_1482).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_247 :
    (14933/3200000000000000:ℝ) ≤ ∫ x in (247/256:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (247/256:ℝ) (31/32:ℝ) (495/512:ℝ) (14933/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1483).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_247 :
    (∫ x in (247/256:ℝ)..(31/32:ℝ), x^0*thetaFirstMode x) ≤ (239733/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (247/256:ℝ) (31/32:ℝ) (129897/100000000000000:ℝ) (27459/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1482).2 (thetaFirstMode_refined_node_1488).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_248 :
    (25237/6400000000000000:ℝ) ≤ ∫ x in (31/32:ℝ)..(249/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (31/32:ℝ) (249/256:ℝ) (497/512:ℝ) (25237/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1489).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_248 :
    (∫ x in (31/32:ℝ)..(249/256:ℝ), x^0*thetaFirstMode x) ≤ (101293/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (31/32:ℝ) (249/256:ℝ) (27459/25000000000000:ℝ) (371/400000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1488).2 (thetaFirstMode_refined_node_1494).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_249 :
    (85187/25600000000000000:ℝ) ≤ ∫ x in (249/256:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (249/256:ℝ) (125/128:ℝ) (499/512:ℝ) (85187/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1495).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_249 :
    (∫ x in (249/256:ℝ)..(125/128:ℝ), x^0*thetaFirstMode x) ≤ (170967/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (249/256:ℝ) (125/128:ℝ) (371/400000000000:ℝ) (78217/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1494).2 (thetaFirstMode_refined_node_1500).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_250 :
    (71791/25600000000000000:ℝ) ≤ ∫ x in (125/128:ℝ)..(251/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (125/128:ℝ) (251/256:ℝ) (501/512:ℝ) (71791/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1501).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_250 :
    (∫ x in (125/128:ℝ)..(251/256:ℝ), x^0*thetaFirstMode x) ≤ (144089/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (125/128:ℝ) (251/256:ℝ) (78217/100000000000000:ℝ) (4117/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1500).2 (thetaFirstMode_refined_node_1506).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_251 :
    (60419/25600000000000000:ℝ) ≤ ∫ x in (251/256:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (251/256:ℝ) (63/64:ℝ) (503/512:ℝ) (60419/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1507).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_251 :
    (∫ x in (251/256:ℝ)..(63/64:ℝ), x^0*thetaFirstMode x) ≤ (15159/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (251/256:ℝ) (63/64:ℝ) (4117/6250000000000:ℝ) (277/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1506).2 (thetaFirstMode_refined_node_1512).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_252 :
    (25389/12800000000000000:ℝ) ≤ ∫ x in (63/64:ℝ)..(253/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (63/64:ℝ) (253/256:ℝ) (505/512:ℝ) (25389/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1513).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_252 :
    (∫ x in (63/64:ℝ)..(253/256:ℝ), x^0*thetaFirstMode x) ≤ (101929/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (63/64:ℝ) (253/256:ℝ) (277/500000000000:ℝ) (46529/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1512).2 (thetaFirstMode_refined_node_1518).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_253 :
    (21309/12800000000000000:ℝ) ≤ ∫ x in (253/256:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (253/256:ℝ) (127/128:ℝ) (507/512:ℝ) (21309/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1519).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_253 :
    (∫ x in (253/256:ℝ)..(127/128:ℝ), x^0*thetaFirstMode x) ≤ (85553/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (253/256:ℝ) (127/128:ℝ) (46529/100000000000000:ℝ) (2439/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1518).2 (thetaFirstMode_refined_node_1524).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_254 :
    (35719/25600000000000000:ℝ) ≤ ∫ x in (127/128:ℝ)..(255/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (127/128:ℝ) (255/256:ℝ) (509/512:ℝ) (35719/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1525).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_254 :
    (∫ x in (127/128:ℝ)..(255/256:ℝ), x^0*thetaFirstMode x) ≤ (17927/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (127/128:ℝ) (255/256:ℝ) (2439/6250000000000:ℝ) (8171/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1524).2 (thetaFirstMode_refined_node_1530).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_255 :
    (5979/5120000000000000:ℝ) ≤ ∫ x in (255/256:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (255/256:ℝ) (1/1:ℝ) (511/512:ℝ) (5979/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1531).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_255 :
    (∫ x in (255/256:ℝ)..(1/1:ℝ), x^0*thetaFirstMode x) ≤ (3001/2560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (255/256:ℝ) (1/1:ℝ) (8171/25000000000000:ℝ) (3417/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1530).2 (thetaFirstMode_refined_node_1536).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

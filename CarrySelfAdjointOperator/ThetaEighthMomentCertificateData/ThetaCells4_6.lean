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

theorem thetaFirstMode_refined_cell_lower_4_192 :
    (1453075547289965847/549755813888000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/4:ℝ) (193/256:ℝ) (7930210043525/10546054596096:ℝ) (211635927/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1155).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^4*thetaFirstMode x) ≤ (2910126412530577647/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/4:ℝ) (193/256:ℝ) (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_193 :
    (332606790195741787/137438953472000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (193/256:ℝ) (97/128:ℝ) (2712779610345/3588968463872:ℝ) (47449477/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1161).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^4*thetaFirstMode x) ≤ (532910944215074907/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (193/256:ℝ) (97/128:ℝ) (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_194 :
    (304235583388156387/137438953472000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (97/128:ℝ) (195/256:ℝ) (8350814750845/10991206887936:ℝ) (42516337/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1167).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^4*thetaFirstMode x) ≤ (146239546164268589/65970697666560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (97/128:ℝ) (195/256:ℝ) (179715241/100000000000000:ℝ) (257537/160000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_195 :
    (1112045094670690729/549755813888000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (195/256:ℝ) (49/64:ℝ) (8567705548355/11218994843136:ℝ) (152250829/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1173).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^4*thetaFirstMode x) ≤ (445457399307363413/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (195/256:ℝ) (49/64:ℝ) (257537/160000000000:ℝ) (72018211/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_196 :
    (1015186377386572451/549755813888000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (49/64:ℝ) (197/256:ℝ) (2929693223055/3816768399872:ℝ) (136182071/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1179).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^4*thetaFirstMode x) ≤ (40666793228407243/21990232555520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (49/64:ℝ) (197/256:ℝ) (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_197 :
    (115730443403605077/68719476736000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (197/256:ℝ) (99/128:ℝ) (9015006262675/11685174084096:ℝ) (15212607/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1185).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^4*thetaFirstMode x) ≤ (1112662723018787243/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (197/256:ℝ) (99/128:ℝ) (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_198 :
    (105439976142600281/68719476736000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (99/128:ℝ) (199/256:ℝ) (9245555185685/11923637807616:ℝ) (13582751/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1191).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^4*thetaFirstMode x) ≤ (1689587459623553589/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (99/128:ℝ) (199/256:ℝ) (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_199 :
    (191935908155522111/137438953472000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (199/256:ℝ) (25/32:ℝ) (3160265668665/4055244288512:ℝ) (24233111/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1197).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^4*thetaFirstMode x) ≤ (1537844742881123187/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (199/256:ℝ) (25/32:ℝ) (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_200 :
    (174517018166766569/137438953472000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/32:ℝ) (201/256:ℝ) (9720803006005/12411495937536:ℝ) (21597569/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1203).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^4*thetaFirstMode x) ≤ (4194945777895950721/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/32:ℝ) (201/256:ℝ) (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_201 :
    (25362803894970729/21990232555520000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (201/256:ℝ) (101/128:ℝ) (9965645186315/12660963887616:ℝ) (3076959/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1209).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^4*thetaFirstMode x) ≤ (3810457131337655321/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (201/256:ℝ) (101/128:ℝ) (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_202 :
    (287674932472877323/274877906944000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (101/128:ℝ) (203/256:ℝ) (3405132089775/4304724588032:ℝ) (34215793/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1215).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^4*thetaFirstMode x) ≤ (576277924457709197/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (101/128:ℝ) (203/256:ℝ) (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_203 :
    (521529966975589533/549755813888000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (203/256:ℝ) (51/64:ℝ) (10470129702835/13171162799616:ℝ) (60819993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1221).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^4*thetaFirstMode x) ≤ (3134310994011561857/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (203/256:ℝ) (51/64:ℝ) (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_204 :
    (118063670576095959/137438953472000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (51/64:ℝ) (205/256:ℝ) (10729919663645/13431968411136:ℝ) (13501059/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1227).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^4*thetaFirstMode x) ≤ (2838251500964506201/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (51/64:ℝ) (205/256:ℝ) (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_205 :
    (427189175075546719/549755813888000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (205/256:ℝ) (103/128:ℝ) (3664947020385/4565542733312:ℝ) (47906869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1233).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^4*thetaFirstMode x) ≤ (855826171697154587/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (205/256:ℝ) (103/128:ℝ) (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_206 :
    (386018694378960253/549755813888000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (103/128:ℝ) (207/256:ℝ) (11264969540965/13965179951616:ℝ) (42457363/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1239).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^4*thetaFirstMode x) ≤ (773367349657748793/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (103/128:ℝ) (207/256:ℝ) (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_207 :
    (348447794263912433/549755813888000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (207/256:ℝ) (13/16:ℝ) (11540381488475/14237661636096:ℝ) (37591553/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1245).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^4*thetaFirstMode x) ≤ (349057985520065687/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (207/256:ℝ) (13/16:ℝ) (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_208 :
    (157099749700451079/274877906944000000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/16:ℝ) (209/256:ℝ) (3940384677495/4838037135872:ℝ) (16625559/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1251).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^4*thetaFirstMode x) ≤ (629517640460378903/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/16:ℝ) (209/256:ℝ) (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_209 :
    (4422102036183561/8589934592000000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (209/256:ℝ) (105/128:ℝ) (12107365048795/14794567604736:ℝ) (459111/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1257).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^4*thetaFirstMode x) ≤ (42529000413010651/82463372083200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (209/256:ℝ) (105/128:ℝ) (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_210 :
    (63662620760366319/137438953472000000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (105/128:ℝ) (211/256:ℝ) (12399093163805/15079068750336:ℝ) (6484869/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1263).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^4*thetaFirstMode x) ≤ (9566959225321531/20615843020800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (105/128:ℝ) (211/256:ℝ) (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_211 :
    (45776207922203321/109951162777600000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (211/256:ℝ) (53/64:ℝ) (4232139252705/5122551183872:ℝ) (4575341/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1269).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^4*thetaFirstMode x) ≤ (114654513986186749/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (211/256:ℝ) (53/64:ℝ) (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_212 :
    (41099036872445497/109951162777600000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (53/64:ℝ) (213/256:ℝ) (12999418970125/15660360900096:ℝ) (4031077/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1275).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^4*thetaFirstMode x) ≤ (411771602272882351/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (53/64:ℝ) (213/256:ℝ) (10740033/50000000000000:ℝ) (151323/800000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_213 :
    (184296457690177811/549755813888000000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (213/256:ℝ) (107/128:ℝ) (13308177699635/15957229871616:ℝ) (17739881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1281).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^4*thetaFirstMode x) ≤ (553957684758565087/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (213/256:ℝ) (107/128:ℝ) (151323/800000000000:ℝ) (16640047/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_214 :
    (165102155180006347/549755813888000000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (107/128:ℝ) (215/256:ℝ) (4540925203815/5419433242112:ℝ) (15597997/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1287).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^4*thetaFirstMode x) ≤ (165426435080943537/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (107/128:ℝ) (215/256:ℝ) (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_215 :
    (36935653116858969/137438953472000000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (215/256:ℝ) (27/32:ℝ) (13943295138955/16563609908736:ℝ) (3425169/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1293).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^4*thetaFirstMode x) ≤ (74018795672502581/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (215/256:ℝ) (27/32:ℝ) (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_216 :
    (33015129226762111/137438953472000000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/32:ℝ) (217/256:ℝ) (14269819487765/16873200047616:ℝ) (3005431/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1299).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^4*thetaFirstMode x) ≤ (79397118211940471/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/32:ℝ) (217/256:ℝ) (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_217 :
    (29477538434837157/137438953472000000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (217/256:ℝ) (109/128:ℝ) (4867477546425/5729036652032:ℝ) (2634387/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1305).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^4*thetaFirstMode x) ≤ (29538347415235391/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (217/256:ℝ) (109/128:ℝ) (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_218 :
    (52578376445738791/274877906944000000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (109/128:ℝ) (219/256:ℝ) (14941219354285/17505379631616:ℝ) (4613461/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1311).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^4*thetaFirstMode x) ≤ (105377262304222999/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (109/128:ℝ) (219/256:ℝ) (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_219 :
    (93675871469712473/549755813888000000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (219/256:ℝ) (55/64:ℝ) (15286265176595/17828049255936:ℝ) (8070773/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1317).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^4*thetaFirstMode x) ≤ (46937767647880007/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (219/256:ℝ) (55/64:ℝ) (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_220 :
    (41676338089179687/274877906944000000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (55/64:ℝ) (221/256:ℝ) (5212552145535/6051719731712:ℝ) (3525987/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1323).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^4*thetaFirstMode x) ≤ (167066541601103183/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (55/64:ℝ) (221/256:ℝ) (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_221 :
    (74081426112230739/549755813888000000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (221/256:ℝ) (111/128:ℝ) (15995480254915/18486749999616:ℝ) (6155169/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1329).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^4*thetaFirstMode x) ≤ (222733745504313391/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (221/256:ℝ) (111/128:ℝ) (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_222 :
    (65764838672320311/549755813888000000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (111/128:ℝ) (223/256:ℝ) (16359824545925/18822862404096:ℝ) (5366601/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1335).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^4*thetaFirstMode x) ≤ (79094475702100793/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (111/128:ℝ) (223/256:ℝ) (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_223 :
    (1457838654423569/13743895347200000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (223/256:ℝ) (7/8:ℝ) (5576926007145/6387845775872:ℝ) (116849/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1341).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^4*thetaFirstMode x) ≤ (116892476156053617/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (223/256:ℝ) (7/8:ℝ) (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

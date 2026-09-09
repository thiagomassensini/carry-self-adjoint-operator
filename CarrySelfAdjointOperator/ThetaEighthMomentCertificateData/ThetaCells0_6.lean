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

theorem thetaFirstMode_refined_cell_lower_0_192 :
    (211675683/25600000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (3/4:ℝ) (193/256:ℝ) (385/512:ℝ) (211675683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1153).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^0*thetaFirstMode x) ≤ (423930397/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (3/4:ℝ) (193/256:ℝ) (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_193 :
    (189833661/25600000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (193/256:ℝ) (97/128:ℝ) (387/512:ℝ) (189833661/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1159).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^0*thetaFirstMode x) ≤ (380195253/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (193/256:ℝ) (97/128:ℝ) (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_194 :
    (85048737/12800000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (97/128:ℝ) (195/256:ℝ) (389/512:ℝ) (85048737/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1165).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^0*thetaFirstMode x) ≤ (170337933/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (97/128:ℝ) (195/256:ℝ) (179715241/100000000000000:ℝ) (257537/160000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_195 :
    (15227967/2560000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (195/256:ℝ) (49/64:ℝ) (391/512:ℝ) (15227967/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1171).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^0*thetaFirstMode x) ≤ (304997047/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (195/256:ℝ) (49/64:ℝ) (257537/160000000000:ℝ) (72018211/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_196 :
    (68103971/12800000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (49/64:ℝ) (197/256:ℝ) (393/512:ℝ) (68103971/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1177).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^0*thetaFirstMode x) ≤ (136406953/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (49/64:ℝ) (197/256:ℝ) (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_197 :
    (121724043/25600000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (197/256:ℝ) (99/128:ℝ) (395/512:ℝ) (121724043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1183).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^0*thetaFirstMode x) ≤ (48761939/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (197/256:ℝ) (99/128:ℝ) (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_198 :
    (108682771/25600000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (99/128:ℝ) (199/256:ℝ) (397/512:ℝ) (108682771/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1189).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^0*thetaFirstMode x) ≤ (8707751/2048000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (99/128:ℝ) (199/256:ℝ) (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_199 :
    (4847551/1280000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (199/256:ℝ) (25/32:ℝ) (399/512:ℝ) (4847551/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1195).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^0*thetaFirstMode x) ≤ (38839941/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (199/256:ℝ) (25/32:ℝ) (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_200 :
    (540043/160000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (25/32:ℝ) (201/256:ℝ) (401/512:ℝ) (540043/625000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1201).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^0*thetaFirstMode x) ≤ (173083457/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (25/32:ℝ) (201/256:ℝ) (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_201 :
    (19234701/6400000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (201/256:ℝ) (101/128:ℝ) (403/512:ℝ) (19234701/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1207).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^0*thetaFirstMode x) ≤ (154121737/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (201/256:ℝ) (101/128:ℝ) (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_202 :
    (68444817/25600000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (101/128:ℝ) (203/256:ℝ) (405/512:ℝ) (68444817/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1213).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^0*thetaFirstMode x) ≤ (68555207/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (101/128:ℝ) (203/256:ℝ) (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_203 :
    (15207947/6400000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (203/256:ℝ) (51/64:ℝ) (407/512:ℝ) (15207947/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1219).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^0*thetaFirstMode x) ≤ (121863053/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (203/256:ℝ) (51/64:ℝ) (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_204 :
    (54014741/25600000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (51/64:ℝ) (205/256:ℝ) (409/512:ℝ) (54014741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1225).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^0*thetaFirstMode x) ≤ (108209541/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (51/64:ℝ) (205/256:ℝ) (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_205 :
    (5989527/3200000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (205/256:ℝ) (103/128:ℝ) (411/512:ℝ) (5989527/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1231).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^0*thetaFirstMode x) ≤ (95994809/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (205/256:ℝ) (103/128:ℝ) (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_206 :
    (42465673/25600000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (103/128:ℝ) (207/256:ℝ) (413/512:ℝ) (42465673/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1237).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^0*thetaFirstMode x) ≤ (17015527/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (103/128:ℝ) (207/256:ℝ) (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_207 :
    (37598933/25600000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (207/256:ℝ) (13/16:ℝ) (415/512:ℝ) (37598933/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1243).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^0*thetaFirstMode x) ≤ (37664767/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (207/256:ℝ) (13/16:ℝ) (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_208 :
    (16628833/12800000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (13/16:ℝ) (209/256:ℝ) (417/512:ℝ) (16628833/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1249).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^0*thetaFirstMode x) ≤ (2665349/2048000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (13/16:ℝ) (209/256:ℝ) (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_209 :
    (29388909/25600000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (209/256:ℝ) (105/128:ℝ) (419/512:ℝ) (29388909/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1255).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^0*thetaFirstMode x) ≤ (7360521/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (209/256:ℝ) (105/128:ℝ) (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_210 :
    (25944617/25600000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (105/128:ℝ) (211/256:ℝ) (421/512:ℝ) (25944617/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1261).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^0*thetaFirstMode x) ≤ (1624521/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (105/128:ℝ) (211/256:ℝ) (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_211 :
    (22881253/25600000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (211/256:ℝ) (53/64:ℝ) (423/512:ℝ) (22881253/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1267).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^0*thetaFirstMode x) ≤ (11462017/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (211/256:ℝ) (53/64:ℝ) (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_212 :
    (10079703/12800000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (53/64:ℝ) (213/256:ℝ) (425/512:ℝ) (10079703/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1273).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^0*thetaFirstMode x) ≤ (40395441/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (53/64:ℝ) (213/256:ℝ) (10740033/50000000000000:ℝ) (151323/800000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_213 :
    (17743431/25600000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (213/256:ℝ) (107/128:ℝ) (427/512:ℝ) (17743431/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1279).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^0*thetaFirstMode x) ≤ (17777711/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (213/256:ℝ) (107/128:ℝ) (151323/800000000000:ℝ) (16640047/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_214 :
    (1950141/3200000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (107/128:ℝ) (215/256:ℝ) (429/512:ℝ) (1950141/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1285).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^0*thetaFirstMode x) ≤ (15631767/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (107/128:ℝ) (215/256:ℝ) (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_215 :
    (3425859/6400000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (215/256:ℝ) (27/32:ℝ) (431/512:ℝ) (3425859/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1291).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^0*thetaFirstMode x) ≤ (1716349/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (215/256:ℝ) (27/32:ℝ) (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_216 :
    (6012077/12800000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (27/32:ℝ) (217/256:ℝ) (433/512:ℝ) (6012077/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1297).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^0*thetaFirstMode x) ≤ (12048553/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (27/32:ℝ) (217/256:ℝ) (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_217 :
    (2634921/6400000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (217/256:ℝ) (109/128:ℝ) (435/512:ℝ) (2634921/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1303).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^0*thetaFirstMode x) ≤ (660089/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (217/256:ℝ) (109/128:ℝ) (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_218 :
    (9228799/25600000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (109/128:ℝ) (219/256:ℝ) (437/512:ℝ) (9228799/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1309).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^0*thetaFirstMode x) ≤ (9248149/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (109/128:ℝ) (219/256:ℝ) (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_219 :
    (403621/1280000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (219/256:ℝ) (55/64:ℝ) (439/512:ℝ) (403621/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1315).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^0*thetaFirstMode x) ≤ (1011203/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (219/256:ℝ) (55/64:ℝ) (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_220 :
    (3526709/12800000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (55/64:ℝ) (221/256:ℝ) (441/512:ℝ) (3526709/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1321).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^0*thetaFirstMode x) ≤ (14137397/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (55/64:ℝ) (221/256:ℝ) (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_221 :
    (3078217/12800000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (221/256:ℝ) (111/128:ℝ) (443/512:ℝ) (3078217/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1327).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^0*thetaFirstMode x) ≤ (6169991/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (221/256:ℝ) (111/128:ℝ) (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_222 :
    (1341927/6400000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (111/128:ℝ) (223/256:ℝ) (445/512:ℝ) (1341927/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1333).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^0*thetaFirstMode x) ≤ (2151889/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (111/128:ℝ) (223/256:ℝ) (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_223 :
    (4674927/25600000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (223/256:ℝ) (7/8:ℝ) (447/512:ℝ) (4674927/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1339).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^0*thetaFirstMode x) ≤ (9371127/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (223/256:ℝ) (7/8:ℝ) (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

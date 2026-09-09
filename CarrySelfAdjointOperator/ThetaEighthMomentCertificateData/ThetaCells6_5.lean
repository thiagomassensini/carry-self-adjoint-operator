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

theorem thetaFirstMode_refined_cell_lower_6_160 :
    (67788551499646929111501/6305039478318694400000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (5/8:ℝ) (161/256:ℝ) (153653616612258567/245075155146180608:ℝ) (566483181/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0964).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^6*thetaFirstMode x) ≤ (868389971470301259767913/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/8:ℝ) (161/256:ℝ) (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_161 :
    (129337044335130709149719/12610078956637388800000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (161/256:ℝ) (81/128:ℝ) (160481454610240505/254380587287115776:ℝ) (1041283337/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0970).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^6*thetaFirstMode x) ≤ (2071081997998566104394417/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (161/256:ℝ) (81/128:ℝ) (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_162 :
    (123272306298335070965447/12610078956637388800000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (81/128:ℝ) (163/256:ℝ) (167567721804348775/263978612695980032:ℝ) (956371733/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0976).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^6*thetaFirstMode x) ≤ (70499794510015099862409/7205759403792793600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (81/128:ℝ) (163/256:ℝ) (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_163 :
    (14673139601604180403951/1576259869579673600000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (163/256:ℝ) (41/64:ℝ) (174920518482869145/273876545640114176:ℝ) (109723123/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0982).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^6*thetaFirstMode x) ≤ (469936852352736649621541/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (163/256:ℝ) (41/64:ℝ) (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_164 :
    (31907759654503812797489/3602879701896396800000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (41/64:ℝ) (165/256:ℝ) (182548146793017383/284081836670609408:ℝ) (1610203763/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0988).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^6*thetaFirstMode x) ≤ (894184249658129787531157/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (41/64:ℝ) (165/256:ℝ) (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_165 :
    (60656908380350936874639/7205759403792793600000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (165/256:ℝ) (83/128:ℝ) (190459114490427097/294602074304780288:ℝ) (2951701683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0994).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^6*thetaFirstMode x) ≤ (849938058806565486409403/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (165/256:ℝ) (83/128:ℝ) (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_166 :
    (7200218728448593978521/900719925474099200000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (83/128:ℝ) (167/256:ℝ) (198662138734783815/305444986718959616:ℝ) (337940841/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1000).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^6*thetaFirstMode x) ≤ (3228561573953231667155603/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (83/128:ℝ) (167/256:ℝ) (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_167 :
    (19127549231630047172141/2522015791327477760000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (167/256:ℝ) (21/32:ℝ) (207166149931887545/316618443451615232:ℝ) (123723749/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1006).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^6*thetaFirstMode x) ≤ (1531585299942715408253/201761263306198220800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (167/256:ℝ) (21/32:ℝ) (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_168 :
    (72522680813396146141127/10088063165309911040000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (21/32:ℝ) (169/256:ℝ) (215980295622426055/328130457116788736:ℝ) (452644511/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1012).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^6*thetaFirstMode x) ≤ (2903570161048823559913399/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/32:ℝ) (169/256:ℝ) (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_169 :
    (343396597413741855789011/50440315826549555200000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (169/256:ℝ) (85/128:ℝ) (225113944417741113/339989185127856128:ℝ) (2068525301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1018).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^6*thetaFirstMode x) ≤ (687434279145556115946861/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (169/256:ℝ) (85/128:ℝ) (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_170 :
    (32489600357333432386317/5044031582654955520000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (85/128:ℝ) (171/256:ℝ) (234576689982869927/352202931431610368:ℝ) (188921487/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1024).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^6*thetaFirstMode x) ≤ (2601635105637279200490333/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (85/128:ℝ) (171/256:ℝ) (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_171 :
    (153552753370247326383623/25220157913274777600000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (171/256:ℝ) (43/64:ℝ) (244378355067144025/364780148252665856:ℝ) (862097459/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1030).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^6*thetaFirstMode x) ≤ (1229607662553119775598403/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (171/256:ℝ) (43/64:ℝ) (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_172 :
    (72504384130296889655167/12610078956637388800000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (43/64:ℝ) (173/256:ℝ) (254528995582627815/377729437848184832:ℝ) (393109363/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1036).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^6*thetaFirstMode x) ≤ (20735868955576566738443/3602879701896396800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (43/64:ℝ) (173/256:ℝ) (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_173 :
    (273623167349310853065927/50440315826549555200000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (173/256:ℝ) (87/128:ℝ) (265038904730679065/391059554272925696:ℝ) (1432979301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1042).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^6*thetaFirstMode x) ≤ (1095584899988462984268507/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (173/256:ℝ) (87/128:ℝ) (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_174 :
    (257912217794131399517267/50440315826549555200000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (87/128:ℝ) (175/256:ℝ) (275918617176913543/404779405154613248:ℝ) (1304918717/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1048).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^6*thetaFirstMode x) ≤ (516347851179406287748807/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (87/128:ℝ) (175/256:ℝ) (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_175 :
    (242873351801478360157317/50440315826549555200000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (175/256:ℝ) (11/16:ℝ) (287178913274856057/418898053479630848:ℝ) (1187412117/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1054).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^6*thetaFirstMode x) ≤ (486247883532426480916187/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (175/256:ℝ) (11/16:ℝ) (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_176 :
    (228494176644809756152203/50440315826549555200000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (11/16:ℝ) (177/256:ℝ) (298830823338560135/433424719389034496:ℝ) (1079670939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1060).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^6*thetaFirstMode x) ≤ (182987112745637572107297/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/16:ℝ) (177/256:ℝ) (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_177 :
    (214761341531138464499847/50440315826549555200000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (177/256:ℝ) (89/128:ℝ) (310885631964478585/448368781984888832:ℝ) (980958633/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1066).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x) ≤ (171992345075156690340113/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (177/256:ℝ) (89/128:ℝ) (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_178 :
    (50415158505787059359621/12610078956637388800000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (89/128:ℝ) (179/256:ℝ) (323354882402867175/463739781146925056:ℝ) (222646943/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1072).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^6*thetaFirstMode x) ≤ (50469839743922444908137/12610078956637388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (89/128:ℝ) (179/256:ℝ) (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_179 :
    (189177075681586980088749/50440315826549555200000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (179/256:ℝ) (45/64:ℝ) (336250380979003673/479547419359520768:ℝ) (807917289/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1078).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x) ≤ (216440802227568239973531/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (179/256:ℝ) (45/64:ℝ) (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_180 :
    (177295013334098958656003/50440315826549555200000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (45/64:ℝ) (181/256:ℝ) (349584201564504487/495801563549001728:ℝ) (732349823/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1084).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^6*thetaFirstMode x) ≤ (141995050784025048710131/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (45/64:ℝ) (181/256:ℝ) (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_181 :
    (20749776284608206026143/6305039478318694400000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (181/256:ℝ) (91/128:ℝ) (363368690099021145/512512246931265536:ℝ) (82916149/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1090).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x) ≤ (1329499694811270149664313/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (181/256:ℝ) (91/128:ℝ) (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_182 :
    (155269933266098239024307/50440315826549555200000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (91/128:ℝ) (183/256:ℝ) (377616469162598855/529689670869727232:ℝ) (600337973/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1096).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^6*thetaFirstMode x) ≤ (621799671950877919898629/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (91/128:ℝ) (183/256:ℝ) (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_183 :
    (145093036502681379875281/50440315826549555200000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (183/256:ℝ) (23/32:ℝ) (392340442598979385/547344206743586816:ℝ) (542895193/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1102).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x) ≤ (1162112316732653764151/403522526612396441600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (183/256:ℝ) (23/32:ℝ) (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_184 :
    (135450043754410109368573/50440315826549555200000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (23/32:ℝ) (185/256:ℝ) (407553800190130503/565486397826418688:ℝ) (490554133/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1108).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^6*thetaFirstMode x) ≤ (1084898817725658868581039/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/32:ℝ) (185/256:ℝ) (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_185 :
    (18046174923358290386931/7205759403792793600000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (185/256:ℝ) (93/128:ℝ) (423270022382284217/584126961175083008:ℝ) (442900227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1114).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x) ≤ (1011817018883992321152163/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (185/256:ℝ) (93/128:ℝ) (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_186 :
    (16813524136349865061093/7205759403792793600000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (93/128:ℝ) (187/256:ℝ) (439502885063766055/603276789528958976:ℝ) (399549073/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1120).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^6*thetaFirstMode x) ≤ (471361823234022450041349/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (93/128:ℝ) (187/256:ℝ) (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_187 :
    (13693294764395174876503/6305039478318694400000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (187/256:ℝ) (47/64:ℝ) (456266464394897625/622946953219500032:ℝ) (45018067/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1126).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x) ≤ (2742107959589159794967/1261007895663738880000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (187/256:ℝ) (47/64:ℝ) (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_188 :
    (2037204603578193567743/1008806316530991104000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (47/64:ℝ) (189/256:ℝ) (473575141690254695/643148702090110976:ℝ) (6487139/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1132).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^6*thetaFirstMode x) ≤ (6374415767606544719963/3152519739159347200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (47/64:ℝ) (189/256:ℝ) (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_189 :
    (94618242528465707235339/50440315826549555200000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (189/256:ℝ) (95/128:ℝ) (491443608353563033/663893467426347008:ℝ) (291881409/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1138).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x) ≤ (189482826946932276081201/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (189/256:ℝ) (95/128:ℝ) (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_190 :
    (87802430612132413155081/50440315826549555200000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (95/128:ℝ) (191/256:ℝ) (509886870865514247/685192863896434688:ℝ) (262436151/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1144).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^6*thetaFirstMode x) ≤ (8791863547003711797687/5044031582654955520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (95/128:ℝ) (191/256:ℝ) (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_191 :
    (20348740718368341454369/12610078956637388800000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (191/256:ℝ) (3/4:ℝ) (528920255824783865/707058691502114816:ℝ) (58940257/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1150).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x) ≤ (652035867006724066991671/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (191/256:ℝ) (3/4:ℝ) (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

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

theorem thetaFirstMode_refined_cell_lower_4_160 :
    (7519059035760345689/274877906944000000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/8:ℝ) (161/256:ℝ) (1065097174935/1698824602112:ℝ) (2266130489/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0963).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^4*thetaFirstMode x) ≤ (30100377832754287293/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/8:ℝ) (161/256:ℝ) (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_161 :
    (177110916193126289/6871947673600000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (161/256:ℝ) (81/128:ℝ) (3296080149115/5224679471616:ℝ) (52068719/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0969).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^4*thetaFirstMode x) ≤ (10635329362823756023/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (161/256:ℝ) (81/128:ℝ) (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_162 :
    (208418601237260959/8589934592000000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (81/128:ℝ) (163/256:ℝ) (3399396216125/5355288900096:ℝ) (59778469/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0975).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^4*thetaFirstMode x) ≤ (40049589475212913981/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (81/128:ℝ) (163/256:ℝ) (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_163 :
    (12546870161245456517/549755813888000000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (163/256:ℝ) (41/64:ℝ) (1168428988545/1829443983872:ℝ) (3511448057/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0981).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^4*thetaFirstMode x) ≤ (12557461746985302353/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (163/256:ℝ) (41/64:ℝ) (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_164 :
    (11792086412443048369/549755813888000000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (41/64:ℝ) (165/256:ℝ) (3613800222445/5623838670336:ℝ) (3220690669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0987).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^4*thetaFirstMode x) ≤ (11802209222924588623/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (41/64:ℝ) (165/256:ℝ) (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_165 :
    (11073391215743219053/549755813888000000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (165/256:ℝ) (83/128:ℝ) (3724984399955/5761839284736:ℝ) (2951961703/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0993).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^4*thetaFirstMode x) ≤ (33249173291673927379/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (165/256:ℝ) (83/128:ℝ) (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_166 :
    (10389718649309530943/549755813888000000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (83/128:ℝ) (167/256:ℝ) (1279629501255/1967454735872:ℝ) (2703765353/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0999).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^4*thetaFirstMode x) ≤ (20797883236115290301/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (83/128:ℝ) (167/256:ℝ) (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_167 :
    (152187327265059451/8589934592000000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (167/256:ℝ) (21/32:ℝ) (3955562135275/6045444036096:ℝ) (38667091/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1005).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^4*thetaFirstMode x) ≤ (974878113833096457/54975581388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (167/256:ℝ) (21/32:ℝ) (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_168 :
    (9123112315204307563/549755813888000000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/32:ℝ) (169/256:ℝ) (4075055495285/6191109551616:ℝ) (2263423123/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1011).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^4*thetaFirstMode x) ≤ (18262973259479634923/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/32:ℝ) (169/256:ℝ) (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_169 :
    (1707598525242203649/109951162777600000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (169/256:ℝ) (85/128:ℝ) (1399139795865/2113130573312:ℝ) (413741799/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1017).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^4*thetaFirstMode x) ≤ (8545962017144541471/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (169/256:ℝ) (85/128:ℝ) (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_170 :
    (498970679355510887/34359738368000000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (85/128:ℝ) (171/256:ℝ) (4322705222605/6490321691136:ℝ) (118086437/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1023).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^4*thetaFirstMode x) ≤ (47946649978402506601/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (85/128:ℝ) (171/256:ℝ) (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_171 :
    (3729314230995135321/274877906944000000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (171/256:ℝ) (43/64:ℝ) (4450965020915/6643930799616:ℝ) (862174341/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1029).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^4*thetaFirstMode x) ≤ (7465826975695355011/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (171/256:ℝ) (43/64:ℝ) (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_172 :
    (6962190327592254007/549755813888000000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (43/64:ℝ) (173/256:ℝ) (1527417138975/2266750188032:ℝ) (1572577987/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1035).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^4*thetaFirstMode x) ≤ (871127854959832841/68719476736000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (43/64:ℝ) (173/256:ℝ) (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_173 :
    (6493127781407869743/549755813888000000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (173/256:ℝ) (87/128:ℝ) (4716617662435/6959312687616:ℝ) (1433107653/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1041).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^4*thetaFirstMode x) ≤ (6499607190058145489/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (173/256:ℝ) (87/128:ℝ) (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_174 :
    (302518062646148543/27487790694400000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (87/128:ℝ) (175/256:ℝ) (4854117630245/7121149057536:ℝ) (65251793/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1047).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^4*thetaFirstMode x) ≤ (2271187637425327049/206158430208000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (87/128:ℝ) (175/256:ℝ) (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_175 :
    (5632822776975880953/549755813888000000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (175/256:ℝ) (11/16:ℝ) (1664935272585/2428597248512:ℝ) (1187518953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1053).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^4*thetaFirstMode x) ≤ (1409658572593468741/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (175/256:ℝ) (11/16:ℝ) (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_176 :
    (327466143989359839/34359738368000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/16:ℝ) (177/256:ℝ) (5138737350565/7453273007616:ℝ) (67485519/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1059).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^4*thetaFirstMode x) ≤ (3146972868252270373/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/16:ℝ) (177/256:ℝ) (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_177 :
    (4869229823436028011/549755813888000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (177/256:ℝ) (89/128:ℝ) (5285967986075/7623625284096:ℝ) (981047301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1065).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^4*thetaFirstMode x) ≤ (2924654203691110733/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (177/256:ℝ) (89/128:ℝ) (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_178 :
    (2260558654446190661/274877906944000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (89/128:ℝ) (179/256:ℝ) (1812184705695/2598960399872:ℝ) (445334231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1071).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^4*thetaFirstMode x) ≤ (2263010379960079797/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (89/128:ℝ) (179/256:ℝ) (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_179 :
    (4194120439079445963/549755813888000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (179/256:ℝ) (45/64:ℝ) (5590552775395/7973073563136:ℝ) (807990663/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1077).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^4*thetaFirstMode x) ≤ (8397491061205716659/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (179/256:ℝ) (45/64:ℝ) (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_180 :
    (1943630093244298547/274877906944000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (45/64:ℝ) (181/256:ℝ) (5748021635405/8152235367936:ℝ) (366208247/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1083).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^4*thetaFirstMode x) ≤ (5837428119285987443/824633720832000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (45/64:ℝ) (181/256:ℝ) (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_181 :
    (112486881730212299/17179869184000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (181/256:ℝ) (91/128:ℝ) (1969673005905/2778133263872:ℝ) (20730929/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1089).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^4*thetaFirstMode x) ≤ (7207367660226563041/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (181/256:ℝ) (91/128:ℝ) (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_182 :
    (666029612757375669/109951162777600000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (91/128:ℝ) (183/256:ℝ) (6073603892725/8519600196096:ℝ) (120078579/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1095).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^4*thetaFirstMode x) ≤ (10002024287284336777/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (91/128:ℝ) (183/256:ℝ) (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_183 :
    (615611252059950157/109951162777600000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (183/256:ℝ) (23/32:ℝ) (6241835884235/8707870127616:ℝ) (108588997/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1101).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^4*thetaFirstMode x) ≤ (46225257018826619/8246337208320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (183/256:ℝ) (23/32:ℝ) (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_184 :
    (1421211585275805419/274877906944000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/32:ℝ) (185/256:ℝ) (2137925091015/2966414438912:ℝ) (245299619/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1107).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^4*thetaFirstMode x) ≤ (5691658100609509047/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/32:ℝ) (185/256:ℝ) (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_185 :
    (524478756275036261/109951162777600000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (185/256:ℝ) (93/128:ℝ) (6589483000555/9093753678336:ℝ) (88588211/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1113).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^4*thetaFirstMode x) ≤ (15753531309474532621/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (185/256:ℝ) (93/128:ℝ) (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_186 :
    (1208570140113083/274877906944000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (93/128:ℝ) (187/256:ℝ) (6769020672365/9291435311616:ℝ) (199793/50000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1119).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^4*thetaFirstMode x) ≤ (7260402627534938299/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (93/128:ℝ) (187/256:ℝ) (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_187 :
    (556465634789372897/137438953472000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (187/256:ℝ) (47/64:ℝ) (2317483520625/3164107500032:ℝ) (90044477/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1125).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^4*thetaFirstMode x) ≤ (222866560035930647/54975581388800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (187/256:ℝ) (47/64:ℝ) (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_188 :
    (409557689687526677/109951162777600000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (47/64:ℝ) (189/256:ℝ) (7139835613885/9696449711616:ℝ) (64877417/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1131).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^4*thetaFirstMode x) ≤ (1025205155520511307/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (47/64:ℝ) (189/256:ℝ) (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_189 :
    (1882174117691518549/549755813888000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (189/256:ℝ) (95/128:ℝ) (7331239448195/9903851598336:ℝ) (291908599/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1137).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^4*thetaFirstMode x) ≤ (353367027888852857/103079215104000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (189/256:ℝ) (95/128:ℝ) (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_190 :
    (345660798217151483/109951162777600000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (95/128:ℝ) (191/256:ℝ) (2508908787735/3371520998912:ℝ) (52492133/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1143).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^4*thetaFirstMode x) ≤ (865295623754261547/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (95/128:ℝ) (191/256:ℝ) (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_191 :
    (158549081559776391/54975581388800000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (191/256:ℝ) (3/4:ℝ) (7726361339515/10328618927616:ℝ) (23578311/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1149).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^4*thetaFirstMode x) ≤ (3175248102678228257/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (191/256:ℝ) (3/4:ℝ) (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

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

theorem thetaFirstMode_refined_cell_lower_2_160 :
    (70057646245391/1006632960000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/8:ℝ) (161/256:ℝ) (49614723/79135744:ℝ) (906531311/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0962).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^2*thetaFirstMode x) ≤ (467425849803211/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/8:ℝ) (161/256:ℝ) (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_161 :
    (54327697183383/838860800000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (161/256:ℝ) (81/128:ℝ) (50547885/80124928:ℝ) (2082930867/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0968).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^2*thetaFirstMode x) ≤ (652464502331591/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (161/256:ℝ) (81/128:ℝ) (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_162 :
    (15155217123683/251658240000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (81/128:ℝ) (163/256:ℝ) (51492675/81120256:ℝ) (191307857/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0974).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^2*thetaFirstMode x) ≤ (303355939795183/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (81/128:ℝ) (163/256:ℝ) (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_163 :
    (140816156547079/2516582400000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (163/256:ℝ) (41/64:ℝ) (52449165/82121728:ℝ) (1755878107/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0980).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^2*thetaFirstMode x) ≤ (281870044004081/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (163/256:ℝ) (41/64:ℝ) (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_164 :
    (52296375542189/1006632960000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (41/64:ℝ) (165/256:ℝ) (53417427/83129344:ℝ) (644194769/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0986).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^2*thetaFirstMode x) ≤ (16356645802457/314572800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (41/64:ℝ) (165/256:ℝ) (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_165 :
    (80862337833807/1677721600000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (165/256:ℝ) (83/128:ℝ) (54397533/84143104:ℝ) (2952221751/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0992).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^2*thetaFirstMode x) ≤ (30349846196917/629145600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (165/256:ℝ) (83/128:ℝ) (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_166 :
    (44976780216767/1006632960000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (83/128:ℝ) (167/256:ℝ) (55389555/85163008:ℝ) (540800801/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0998).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^2*thetaFirstMode x) ≤ (900334081794379/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (83/128:ℝ) (167/256:ℝ) (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_167 :
    (34718487756881/838860800000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (167/256:ℝ) (21/32:ℝ) (56393565/86189056:ℝ) (1237456347/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1004).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^2*thetaFirstMode x) ≤ (20849895688481/503316480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (167/256:ℝ) (21/32:ℝ) (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_168 :
    (32134779514563/838860800000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/32:ℝ) (169/256:ℝ) (57409635/87221248:ℝ) (1131811857/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1010).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^2*thetaFirstMode x) ≤ (771942605172107/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/32:ℝ) (169/256:ℝ) (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_169 :
    (59439977160473/1677721600000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (169/256:ℝ) (85/128:ℝ) (58437837/88259584:ℝ) (2068892709/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1016).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^2*thetaFirstMode x) ≤ (7436931962483/209715200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (169/256:ℝ) (85/128:ℝ) (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_170 :
    (164789643860063/5033164800000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (85/128:ℝ) (171/256:ℝ) (59478243/89304064:ℝ) (1889551133/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1022).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^2*thetaFirstMode x) ≤ (659784173721029/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (85/128:ℝ) (171/256:ℝ) (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_171 :
    (2377576936187/78643200000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (171/256:ℝ) (43/64:ℝ) (60530925/90354688:ℝ) (26945351/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1028).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^2*thetaFirstMode x) ≤ (304623548689519/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (171/256:ℝ) (43/64:ℝ) (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_172 :
    (140395011079453/5033164800000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (43/64:ℝ) (173/256:ℝ) (61595955/91411456:ℝ) (1572718537/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1034).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^2*thetaFirstMode x) ≤ (35133195936073/1258291200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (43/64:ℝ) (173/256:ℝ) (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_173 :
    (2157187420969/83886080000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (173/256:ℝ) (87/128:ℝ) (62673405/92474368:ℝ) (71661801/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1040).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^2*thetaFirstMode x) ≤ (86373597381097/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (173/256:ℝ) (87/128:ℝ) (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_174 :
    (14903379145577/629145600000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (87/128:ℝ) (175/256:ℝ) (63763347/93543424:ℝ) (163144127/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1046).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^2*thetaFirstMode x) ≤ (7956533506159/335544320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (87/128:ℝ) (175/256:ℝ) (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_175 :
    (548689057729/25165824000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (175/256:ℝ) (11/16:ℝ) (64865853/94618624:ℝ) (5938129/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1052).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^2*thetaFirstMode x) ≤ (21970204895981/1006632960000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (175/256:ℝ) (11/16:ℝ) (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_176 :
    (100921006762303/5033164800000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/16:ℝ) (177/256:ℝ) (65980995/95699968:ℝ) (1079865679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1058).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^2*thetaFirstMode x) ≤ (40410749061929/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/16:ℝ) (177/256:ℝ) (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_177 :
    (92735991599101/5033164800000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (177/256:ℝ) (89/128:ℝ) (67108845/96787456:ℝ) (981135979/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1064).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^2*thetaFirstMode x) ≤ (37133961873497/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (177/256:ℝ) (89/128:ℝ) (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_178 :
    (2128600998923/125829120000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (89/128:ℝ) (179/256:ℝ) (68249475/97881088:ℝ) (22268729/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1070).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^2*thetaFirstMode x) ≤ (14206063211993/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (89/128:ℝ) (179/256:ℝ) (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_179 :
    (15621655730749/1006632960000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (179/256:ℝ) (45/64:ℝ) (69402957/98980864:ℝ) (161612809/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1076).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^2*thetaFirstMode x) ≤ (104259211047079/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (179/256:ℝ) (45/64:ℝ) (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_180 :
    (11932272984989/838860800000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (45/64:ℝ) (181/256:ℝ) (70569363/100086784:ℝ) (366241587/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1082).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^2*thetaFirstMode x) ≤ (47782604782399/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (45/64:ℝ) (181/256:ℝ) (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_181 :
    (2185559994443/167772160000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (181/256:ℝ) (91/128:ℝ) (71748765/101198848:ℝ) (66345027/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1088).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^2*thetaFirstMode x) ≤ (262566174332189/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (181/256:ℝ) (91/128:ℝ) (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_182 :
    (3749759132891/314572800000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (91/128:ℝ) (183/256:ℝ) (72941235/102317056:ℝ) (37527989/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1094).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^2*thetaFirstMode x) ≤ (120131369595037/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (91/128:ℝ) (183/256:ℝ) (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_183 :
    (27425851946647/2516582400000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (183/256:ℝ) (23/32:ℝ) (74146845/103441408:ℝ) (271497391/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1100).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^2*thetaFirstMode x) ≤ (5491634396381/503316480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (183/256:ℝ) (23/32:ℝ) (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_184 :
    (50105091564229/5033164800000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/32:ℝ) (185/256:ℝ) (75365667/104571904:ℝ) (490644349/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1106).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^2*thetaFirstMode x) ≤ (66886834122441/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/32:ℝ) (185/256:ℝ) (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_185 :
    (15243154392299/1677721600000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (185/256:ℝ) (93/128:ℝ) (76597773/105708544:ℝ) (442981887/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1112).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^2*thetaFirstMode x) ≤ (183140682682759/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (185/256:ℝ) (93/128:ℝ) (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_186 :
    (41699453981057/5033164800000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (93/128:ℝ) (187/256:ℝ) (77843235/106851328:ℝ) (399622931/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1118).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^2*thetaFirstMode x) ≤ (83502202038977/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (93/128:ℝ) (187/256:ℝ) (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_187 :
    (3165926992683/419430400000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (187/256:ℝ) (47/64:ℝ) (79102125/108000256:ℝ) (90052821/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1124).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^2*thetaFirstMode x) ≤ (3803896395413/503316480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (187/256:ℝ) (47/64:ℝ) (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_188 :
    (4322737853341/629145600000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (47/64:ℝ) (189/256:ℝ) (80374515/109155328:ℝ) (40552153/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1130).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^2*thetaFirstMode x) ≤ (17313088408489/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (47/64:ℝ) (189/256:ℝ) (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_189 :
    (10483511638561/1677721600000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (189/256:ℝ) (95/128:ℝ) (81660477/110316544:ℝ) (291935793/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1136).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^2*thetaFirstMode x) ≤ (31491471768911/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (189/256:ℝ) (95/128:ℝ) (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_190 :
    (28577024140651/5033164800000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (95/128:ℝ) (191/256:ℝ) (82960083/111483904:ℝ) (262485181/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1142).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^2*thetaFirstMode x) ≤ (4769140188897/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (95/128:ℝ) (191/256:ℝ) (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_191 :
    (12971290014149/2516582400000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (191/256:ℝ) (3/4:ℝ) (84273405/112657408:ℝ) (117902597/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1148).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^2*thetaFirstMode x) ≤ (103909932364943/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (191/256:ℝ) (3/4:ℝ) (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

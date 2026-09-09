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

theorem thetaFirstMode_refined_cell_lower_0_160 :
    (4533052171/25600000000000000:ℝ) ≤ ∫ x in (5/8:ℝ)..(161/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (5/8:ℝ) (161/256:ℝ) (321/512:ℝ) (4533052171/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0961).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^0*thetaFirstMode x) ≤ (9073380747/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (5/8:ℝ) (161/256:ℝ) (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_161 :
    (65097281/400000000000000:ℝ) ≤ ∫ x in (161/256:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (161/256:ℝ) (81/128:ℝ) (323/512:ℝ) (65097281/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0967).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^0*thetaFirstMode x) ≤ (104240661/640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (161/256:ℝ) (81/128:ℝ) (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_162 :
    (478311537/3200000000000000:ℝ) ≤ ∫ x in (81/128:ℝ)..(163/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (81/128:ℝ) (163/256:ℝ) (325/512:ℝ) (478311537/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0973).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^0*thetaFirstMode x) ≤ (3829668357/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (81/128:ℝ) (163/256:ℝ) (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_163 :
    (1756032201/12800000000000000:ℝ) ≤ ∫ x in (163/256:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (163/256:ℝ) (41/64:ℝ) (327/512:ℝ) (1756032201/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0979).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^0*thetaFirstMode x) ≤ (3515028821/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (163/256:ℝ) (41/64:ℝ) (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_164 :
    (3221257049/25600000000000000:ℝ) ≤ ∫ x in (41/64:ℝ)..(165/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (41/64:ℝ) (165/256:ℝ) (329/512:ℝ) (3221257049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0985).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^0*thetaFirstMode x) ≤ (3224021999/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (41/64:ℝ) (165/256:ℝ) (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_165 :
    (1476240913/12800000000000000:ℝ) ≤ ∫ x in (165/256:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (165/256:ℝ) (83/128:ℝ) (331/512:ℝ) (1476240913/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0991).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^0*thetaFirstMode x) ≤ (591011783/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (165/256:ℝ) (83/128:ℝ) (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_166 :
    (2704242681/25600000000000000:ℝ) ≤ ∫ x in (83/128:ℝ)..(167/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (83/128:ℝ) (167/256:ℝ) (333/512:ℝ) (2704242681/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0997).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^0*thetaFirstMode x) ≤ (5413285943/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (83/128:ℝ) (167/256:ℝ) (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_167 :
    (495026317/5120000000000000:ℝ) ≤ ∫ x in (167/256:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (167/256:ℝ) (21/32:ℝ) (335/512:ℝ) (495026317/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1003).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^0*thetaFirstMode x) ≤ (247736561/2560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (167/256:ℝ) (21/32:ℝ) (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_168 :
    (90552973/1024000000000000:ℝ) ≤ ∫ x in (21/32:ℝ)..(169/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (21/32:ℝ) (169/256:ℝ) (337/512:ℝ) (90552973/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1009).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^0*thetaFirstMode x) ≤ (4531804213/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (21/32:ℝ) (169/256:ℝ) (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_169 :
    (2069076441/25600000000000000:ℝ) ≤ ∫ x in (169/256:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (169/256:ℝ) (85/128:ℝ) (339/512:ℝ) (2069076441/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1015).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^0*thetaFirstMode x) ≤ (414201501/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (169/256:ℝ) (85/128:ℝ) (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_170 :
    (1889719291/25600000000000000:ℝ) ≤ ∫ x in (85/128:ℝ)..(171/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (85/128:ℝ) (171/256:ℝ) (341/512:ℝ) (1889719291/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1021).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^0*thetaFirstMode x) ≤ (3783025377/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (85/128:ℝ) (171/256:ℝ) (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_171 :
    (862328131/12800000000000000:ℝ) ≤ ∫ x in (171/256:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (171/256:ℝ) (43/64:ℝ) (343/512:ℝ) (862328131/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1027).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^0*thetaFirstMode x) ≤ (1726320581/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (171/256:ℝ) (43/64:ℝ) (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_172 :
    (786429551/12800000000000000:ℝ) ≤ ∫ x in (43/64:ℝ)..(173/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (43/64:ℝ) (173/256:ℝ) (345/512:ℝ) (786429551/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1033).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^0*thetaFirstMode x) ≤ (196800311/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (43/64:ℝ) (173/256:ℝ) (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_173 :
    (3583411/64000000000000:ℝ) ≤ ∫ x in (173/256:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (173/256:ℝ) (87/128:ℝ) (347/512:ℝ) (3583411/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1039).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^0*thetaFirstMode x) ≤ (1434794571/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (173/256:ℝ) (87/128:ℝ) (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_174 :
    (163158773/3200000000000000:ℝ) ≤ ∫ x in (87/128:ℝ)..(175/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (87/128:ℝ) (175/256:ℝ) (349/512:ℝ) (163158773/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1045).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^0*thetaFirstMode x) ≤ (81662153/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (87/128:ℝ) (175/256:ℝ) (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_175 :
    (593866329/12800000000000000:ℝ) ≤ ∫ x in (175/256:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (175/256:ℝ) (11/16:ℝ) (351/512:ℝ) (593866329/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1051).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^0*thetaFirstMode x) ≤ (148619741/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (175/256:ℝ) (11/16:ℝ) (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_176 :
    (134995383/3200000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(177/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (11/16:ℝ) (177/256:ℝ) (353/512:ℝ) (134995383/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1057).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^0*thetaFirstMode x) ≤ (1081095873/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (11/16:ℝ) (177/256:ℝ) (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_177 :
    (490612333/12800000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (177/256:ℝ) (89/128:ℝ) (355/512:ℝ) (490612333/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1063).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x) ≤ (196454237/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (177/256:ℝ) (89/128:ℝ) (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_178 :
    (890829867/25600000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(179/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (89/128:ℝ) (179/256:ℝ) (357/512:ℝ) (890829867/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1069).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^0*thetaFirstMode x) ≤ (445897959/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (89/128:ℝ) (179/256:ℝ) (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_179 :
    (404068717/12800000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (179/256:ℝ) (45/64:ℝ) (359/512:ℝ) (404068717/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1075).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x) ≤ (1618057017/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (179/256:ℝ) (45/64:ℝ) (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_180 :
    (732549859/25600000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(181/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (45/64:ℝ) (181/256:ℝ) (361/512:ℝ) (732549859/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1081).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^0*thetaFirstMode x) ≤ (91671391/3200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (45/64:ℝ) (181/256:ℝ) (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_181 :
    (663510819/25600000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (181/256:ℝ) (91/128:ℝ) (363/512:ℝ) (663510819/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1087).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x) ≤ (1328534299/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (181/256:ℝ) (91/128:ℝ) (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_182 :
    (600502759/25600000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(183/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (91/128:ℝ) (183/256:ℝ) (365/512:ℝ) (600502759/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1093).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^0*thetaFirstMode x) ≤ (601198729/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (91/128:ℝ) (183/256:ℝ) (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_183 :
    (108608917/5120000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (183/256:ℝ) (23/32:ℝ) (367/512:ℝ) (108608917/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1099).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x) ≤ (33980281/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (183/256:ℝ) (23/32:ℝ) (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_184 :
    (490689463/25600000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(185/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (23/32:ℝ) (185/256:ℝ) (369/512:ℝ) (490689463/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1105).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^0*thetaFirstMode x) ≤ (196510941/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (23/32:ℝ) (185/256:ℝ) (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_185 :
    (110755681/6400000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (185/256:ℝ) (93/128:ℝ) (371/512:ℝ) (110755681/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1111).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x) ≤ (887124757/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (185/256:ℝ) (93/128:ℝ) (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_186 :
    (199829933/12800000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(187/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (93/128:ℝ) (187/256:ℝ) (373/512:ℝ) (199829933/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1117).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^0*thetaFirstMode x) ≤ (80030967/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (93/128:ℝ) (187/256:ℝ) (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_187 :
    (45030583/3200000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (187/256:ℝ) (47/64:ℝ) (375/512:ℝ) (45030583/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1123).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x) ≤ (36069827/2560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (187/256:ℝ) (47/64:ℝ) (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_188 :
    (162223683/12800000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(189/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (47/64:ℝ) (189/256:ℝ) (377/512:ℝ) (162223683/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1129).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^0*thetaFirstMode x) ≤ (162431359/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (47/64:ℝ) (189/256:ℝ) (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_189 :
    (29196299/2560000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (189/256:ℝ) (95/128:ℝ) (379/512:ℝ) (29196299/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1135).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x) ≤ (18271437/1600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (189/256:ℝ) (95/128:ℝ) (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_190 :
    (2625097/256000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(191/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (95/128:ℝ) (191/256:ℝ) (381/512:ℝ) (2625097/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1141).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^0*thetaFirstMode x) ≤ (131428533/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (95/128:ℝ) (191/256:ℝ) (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_191 :
    (2947841/320000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (191/256:ℝ) (3/4:ℝ) (383/512:ℝ) (2947841/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1147).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x) ≤ (472289083/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (191/256:ℝ) (3/4:ℝ) (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

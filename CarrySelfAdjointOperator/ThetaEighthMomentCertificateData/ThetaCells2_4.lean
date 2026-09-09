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

theorem thetaFirstMode_refined_cell_lower_2_128 :
    (2407937840330093/5033164800000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/2:ℝ) (129/256:ℝ) (25462275/50725888:ℝ) (48608874989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0770).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^2*thetaFirstMode x) ≤ (1204529838659803/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/2:ℝ) (129/256:ℝ) (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_129 :
    (190916507933627/419430400000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (129/256:ℝ) (65/128:ℝ) (26061357/51518464:ℝ) (11384180871/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0776).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^2*thetaFirstMode x) ≤ (4584167941793761/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (129/256:ℝ) (65/128:ℝ) (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_130 :
    (726109467309793/1677721600000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (65/128:ℝ) (131/256:ℝ) (26669763/52317184:ℝ) (42636245169/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0782).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^2*thetaFirstMode x) ≤ (726459591437597/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (65/128:ℝ) (131/256:ℝ) (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_131 :
    (1034928026718173/2516582400000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (131/256:ℝ) (33/64:ℝ) (27287565/53122048:ℝ) (19949650649/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0788).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^2*thetaFirstMode x) ≤ (8283485638170653/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (131/256:ℝ) (33/64:ℝ) (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_132 :
    (81896024123459/209715200000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (33/64:ℝ) (133/256:ℝ) (27914835/53933056:ℝ) (4664756733/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0794).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^2*thetaFirstMode x) ≤ (7865941732093991/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (33/64:ℝ) (133/256:ℝ) (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_133 :
    (621731366673083/1677721600000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (133/256:ℝ) (67/128:ℝ) (28551645/54750208:ℝ) (34884958947/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0800).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^2*thetaFirstMode x) ≤ (311023498635887/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (133/256:ℝ) (67/128:ℝ) (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_134 :
    (294806946344757/838860800000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (67/128:ℝ) (135/256:ℝ) (29198067/55573504:ℝ) (16296380001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0806).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^2*thetaFirstMode x) ≤ (2359673561358397/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (67/128:ℝ) (135/256:ℝ) (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_135 :
    (838180826238821/2516582400000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (135/256:ℝ) (17/32:ℝ) (29854173/56402944:ℝ) (15217240541/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0812).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^2*thetaFirstMode x) ≤ (111816155464309/335544320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (135/256:ℝ) (17/32:ℝ) (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_136 :
    (793832984596661/2516582400000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/32:ℝ) (137/256:ℝ) (30520035/57238528:ℝ) (14201710013/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0818).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^2*thetaFirstMode x) ≤ (2118019254241857/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/32:ℝ) (137/256:ℝ) (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_137 :
    (626110207671/2097152000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (137/256:ℝ) (69/128:ℝ) (31195725/58080256:ℝ) (33116427/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0824).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^2*thetaFirstMode x) ≤ (1503481385935421/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (137/256:ℝ) (69/128:ℝ) (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_138 :
    (473755114172417/1677721600000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (69/128:ℝ) (139/256:ℝ) (31881315/58928128:ℝ) (24697470633/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0830).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^2*thetaFirstMode x) ≤ (5688205146892931/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (69/128:ℝ) (139/256:ℝ) (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_139 :
    (1343375132316149/5033164800000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (139/256:ℝ) (35/64:ℝ) (32576877/59782144:ℝ) (23010485129/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0836).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^2*thetaFirstMode x) ≤ (1792174385051833/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (139/256:ℝ) (35/64:ℝ) (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_140 :
    (211483218685237/838860800000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (35/64:ℝ) (141/256:ℝ) (33282483/60642304:ℝ) (10713254691/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0842).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^2*thetaFirstMode x) ≤ (211604224952377/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (35/64:ℝ) (141/256:ℝ) (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_141 :
    (199623735509261/838860800000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (141/256:ℝ) (71/128:ℝ) (33998205/61508608:ℝ) (9970053549/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0848).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^2*thetaFirstMode x) ≤ (798959674906581/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (141/256:ℝ) (71/128:ℝ) (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_142 :
    (564904157633887/2516582400000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (71/128:ℝ) (143/256:ℝ) (34724115/62381056:ℝ) (9273037273/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0854).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^2*thetaFirstMode x) ≤ (2260954333326341/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (71/128:ℝ) (143/256:ℝ) (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_143 :
    (26625012423011/125829120000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (143/256:ℝ) (9/16:ℝ) (35460285/63259648:ℝ) (430985843/2500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0860).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^2*thetaFirstMode x) ≤ (1420855732406019/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (143/256:ℝ) (9/16:ℝ) (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_144 :
    (250805568063349/1258291200000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/16:ℝ) (145/256:ℝ) (36206787/64144384:ℝ) (4003856389/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0866).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^2*thetaFirstMode x) ≤ (1338448975053411/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/16:ℝ) (145/256:ℝ) (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_145 :
    (188875403356507/1006632960000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (145/256:ℝ) (73/128:ℝ) (36963693/65035264:ℝ) (2973900637/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0872).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^2*thetaFirstMode x) ≤ (1889930686779317/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (145/256:ℝ) (73/128:ℝ) (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_146 :
    (888368380292267/5033164800000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (73/128:ℝ) (147/256:ℝ) (37731075/65932288:ℝ) (13797325241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0878).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^2*thetaFirstMode x) ≤ (142229006280479/805306368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (73/128:ℝ) (147/256:ℝ) (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_147 :
    (835100487949753/5033164800000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (147/256:ℝ) (37/64:ℝ) (38509005/66835456:ℝ) (12794749237/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0884).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^2*thetaFirstMode x) ≤ (41781934818157/251658240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (147/256:ℝ) (37/64:ℝ) (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_148 :
    (196119532197407/1258291200000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (37/64:ℝ) (149/256:ℝ) (39297555/67744768:ℝ) (2964456251/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0890).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^2*thetaFirstMode x) ≤ (784992354812471/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (37/64:ℝ) (149/256:ℝ) (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_149 :
    (736406932469863/5033164800000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (149/256:ℝ) (75/128:ℝ) (40096797/68660224:ℝ) (10982788213/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0896).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^2*thetaFirstMode x) ≤ (368448946968329/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (149/256:ℝ) (75/128:ℝ) (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_150 :
    (345396766929539/2516582400000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (75/128:ℝ) (151/256:ℝ) (40906803/69581824:ℝ) (5083026989/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0902).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^2*thetaFirstMode x) ≤ (1382523893814803/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (75/128:ℝ) (151/256:ℝ) (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_151 :
    (323772862782961/2516582400000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (151/256:ℝ) (19/32:ℝ) (41727645/70509568:ℝ) (4702105273/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0908).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^2*thetaFirstMode x) ≤ (2591969214028631/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (151/256:ℝ) (19/32:ℝ) (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_152 :
    (202190866402147/1677721600000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/32:ℝ) (153/256:ℝ) (42559395/71443456:ℝ) (8694013089/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0914).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^2*thetaFirstMode x) ≤ (485598441051163/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/32:ℝ) (153/256:ℝ) (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_153 :
    (70973084355713/629145600000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (153/256:ℝ) (77/128:ℝ) (43402125/72383488:ℝ) (1004047199/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0920).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^2*thetaFirstMode x) ≤ (2272758821334209/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (153/256:ℝ) (77/128:ℝ) (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_154 :
    (531094019454961/5033164800000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (77/128:ℝ) (155/256:ℝ) (44255907/73329664:ℝ) (7416374851/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0926).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^2*thetaFirstMode x) ≤ (354319550846181/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (77/128:ℝ) (155/256:ℝ) (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_155 :
    (496414354185239/5033164800000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (155/256:ℝ) (39/64:ℝ) (45120813/74281984:ℝ) (6843224579/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0932).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^2*thetaFirstMode x) ≤ (993561256052207/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (155/256:ℝ) (39/64:ℝ) (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_156 :
    (38638429249713/419430400000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (39/64:ℝ) (157/256:ℝ) (45996915/75240448:ℝ) (1577572407/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0938).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^2*thetaFirstMode x) ≤ (1856036298058117/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (39/64:ℝ) (157/256:ℝ) (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_157 :
    (108187929759277/1258291200000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (157/256:ℝ) (79/128:ℝ) (46884285/76205056:ℝ) (1453767583/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0944).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^2*thetaFirstMode x) ≤ (288721310561827/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (157/256:ℝ) (79/128:ℝ) (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_158 :
    (40360528077199/503316480000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (79/128:ℝ) (159/256:ℝ) (47782995/77175808:ℝ) (535519897/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0950).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^2*thetaFirstMode x) ≤ (807837029240969/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (79/128:ℝ) (159/256:ℝ) (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_159 :
    (75228607681591/1006632960000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (159/256:ℝ) (5/8:ℝ) (48693117/78152704:ℝ) (985686871/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0956).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^2*thetaFirstMode x) ≤ (376439912529931/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (159/256:ℝ) (5/8:ℝ) (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

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

theorem thetaFirstMode_refined_cell_lower_0_128 :
    (48612974743/25600000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (1/2:ℝ) (129/256:ℝ) (257/512:ℝ) (48612974743/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0769).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^0*thetaFirstMode x) ≤ (9727124363/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (1/2:ℝ) (129/256:ℝ) (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_129 :
    (22770282629/12800000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (129/256:ℝ) (65/128:ℝ) (259/512:ℝ) (22770282629/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0775).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x) ≤ (35595429/20000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (129/256:ℝ) (65/128:ℝ) (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_130 :
    (42639843507/25600000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (65/128:ℝ) (131/256:ℝ) (261/512:ℝ) (42639843507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0781).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^0*thetaFirstMode x) ≤ (42660402927/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (65/128:ℝ) (131/256:ℝ) (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_131 :
    (1596106801/1024000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (131/256:ℝ) (33/64:ℝ) (263/512:ℝ) (1596106801/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0787).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x) ≤ (79844485879/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (131/256:ℝ) (33/64:ℝ) (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_132 :
    (37321206119/25600000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (33/64:ℝ) (133/256:ℝ) (265/512:ℝ) (37321206119/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0793).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^0*thetaFirstMode x) ≤ (74679659237/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (33/64:ℝ) (133/256:ℝ) (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_133 :
    (8721976803/6400000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (133/256:ℝ) (67/128:ℝ) (267/512:ℝ) (8721976803/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0799).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x) ≤ (6981123507/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (133/256:ℝ) (67/128:ℝ) (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_134 :
    (16297758063/12800000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (67/128:ℝ) (135/256:ℝ) (269/512:ℝ) (16297758063/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0805).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^0*thetaFirstMode x) ≤ (65224697307/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (67/128:ℝ) (135/256:ℝ) (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_135 :
    (15218528157/12800000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (135/256:ℝ) (17/32:ℝ) (271/512:ℝ) (15218528157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0811).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x) ≤ (761326139/640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (135/256:ℝ) (17/32:ℝ) (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_136 :
    (14202912517/12800000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (17/32:ℝ) (137/256:ℝ) (273/512:ℝ) (14202912517/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0817).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^0*thetaFirstMode x) ≤ (56842009293/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (17/32:ℝ) (137/256:ℝ) (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_137 :
    (13247693251/12800000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (137/256:ℝ) (69/128:ℝ) (275/512:ℝ) (13247693251/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0823).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x) ≤ (26509789259/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (137/256:ℝ) (69/128:ℝ) (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_138 :
    (1234978251/1280000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (69/128:ℝ) (139/256:ℝ) (277/512:ℝ) (1234978251/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0829).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^0*thetaFirstMode x) ≤ (49426445651/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (69/128:ℝ) (139/256:ℝ) (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_139 :
    (5753109521/6400000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (139/256:ℝ) (35/64:ℝ) (279/512:ℝ) (5753109521/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0835).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x) ≤ (46050763947/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (139/256:ℝ) (35/64:ℝ) (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_140 :
    (5357082377/6400000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (35/64:ℝ) (141/256:ℝ) (281/512:ℝ) (5357082377/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0841).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^0*thetaFirstMode x) ≤ (4288117929/5120000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (35/64:ℝ) (141/256:ℝ) (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_141 :
    (19941802539/25600000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (141/256:ℝ) (71/128:ℝ) (283/512:ℝ) (19941802539/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0847).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x) ≤ (997670411/1280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (141/256:ℝ) (71/128:ℝ) (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_142 :
    (4636913251/6400000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (71/128:ℝ) (143/256:ℝ) (285/512:ℝ) (4636913251/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0853).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^0*thetaFirstMode x) ≤ (9279316331/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (71/128:ℝ) (143/256:ℝ) (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_143 :
    (215511281/320000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (143/256:ℝ) (9/16:ℝ) (287/512:ℝ) (215511281/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0859).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x) ≤ (34502567379/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (143/256:ℝ) (9/16:ℝ) (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_144 :
    (8008395751/12800000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (9/16:ℝ) (145/256:ℝ) (289/512:ℝ) (8008395751/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0865).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^0*thetaFirstMode x) ≤ (32053201971/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (9/16:ℝ) (145/256:ℝ) (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_145 :
    (14870772819/25600000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (145/256:ℝ) (73/128:ℝ) (291/512:ℝ) (14870772819/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0871).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^0*thetaFirstMode x) ≤ (7440018227/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (145/256:ℝ) (73/128:ℝ) (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_146 :
    (6899252351/12800000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (73/128:ℝ) (147/256:ℝ) (293/512:ℝ) (6899252351/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0877).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^0*thetaFirstMode x) ≤ (27614495059/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (73/128:ℝ) (147/256:ℝ) (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_147 :
    (79974027/160000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (147/256:ℝ) (37/64:ℝ) (295/512:ℝ) (79974027/625000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0883).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^0*thetaFirstMode x) ≤ (256081811/512000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (147/256:ℝ) (37/64:ℝ) (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_148 :
    (11858841173/25600000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (37/64:ℝ) (149/256:ℝ) (297/512:ℝ) (11858841173/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0889).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^0*thetaFirstMode x) ≤ (59333071/128000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (37/64:ℝ) (149/256:ℝ) (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_149 :
    (549186531/1280000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (149/256:ℝ) (75/128:ℝ) (299/512:ℝ) (549186531/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0895).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^0*thetaFirstMode x) ≤ (1099105303/2560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (149/256:ℝ) (75/128:ℝ) (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_150 :
    (406677099/1024000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (75/128:ℝ) (151/256:ℝ) (301/512:ℝ) (406677099/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0901).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^0*thetaFirstMode x) ≤ (10173821059/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (75/128:ℝ) (151/256:ℝ) (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_151 :
    (1175627463/3200000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (151/256:ℝ) (19/32:ℝ) (303/512:ℝ) (1175627463/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0907).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^0*thetaFirstMode x) ≤ (3764602187/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (151/256:ℝ) (19/32:ℝ) (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_152 :
    (8694762209/25600000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (19/32:ℝ) (153/256:ℝ) (305/512:ℝ) (8694762209/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0913).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^0*thetaFirstMode x) ≤ (696068831/2048000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (19/32:ℝ) (153/256:ℝ) (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_153 :
    (12551673/40000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (153/256:ℝ) (77/128:ℝ) (307/512:ℝ) (12551673/156250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0919).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^0*thetaFirstMode x) ≤ (3215520317/10240000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (153/256:ℝ) (77/128:ℝ) (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_154 :
    (741701579/2560000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (77/128:ℝ) (155/256:ℝ) (309/512:ℝ) (741701579/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0925).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^0*thetaFirstMode x) ≤ (1855599123/6400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (77/128:ℝ) (155/256:ℝ) (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_155 :
    (6843816903/25600000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (155/256:ℝ) (39/64:ℝ) (311/512:ℝ) (6843816903/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0931).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^0*thetaFirstMode x) ≤ (21402707/80000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (155/256:ℝ) (39/64:ℝ) (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_156 :
    (1577709173/6400000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (39/64:ℝ) (157/256:ℝ) (313/512:ℝ) (1577709173/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0937).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^0*thetaFirstMode x) ≤ (12631143917/51200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (39/64:ℝ) (157/256:ℝ) (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_157 :
    (2907787643/12800000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (157/256:ℝ) (79/128:ℝ) (315/512:ℝ) (2907787643/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0943).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^0*thetaFirstMode x) ≤ (5820013077/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (157/256:ℝ) (79/128:ℝ) (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_158 :
    (5355664767/25600000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (79/128:ℝ) (159/256:ℝ) (317/512:ℝ) (5355664767/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0949).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^0*thetaFirstMode x) ≤ (5359820997/25600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (79/128:ℝ) (159/256:ℝ) (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_0_159 :
    (985772753/5120000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 0 (159/256:ℝ) (5/8:ℝ) (319/512:ℝ) (985772753/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0955).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_0_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^0*thetaFirstMode x) ≤ (2466376841/12800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 0 (159/256:ℝ) (5/8:ℝ) (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

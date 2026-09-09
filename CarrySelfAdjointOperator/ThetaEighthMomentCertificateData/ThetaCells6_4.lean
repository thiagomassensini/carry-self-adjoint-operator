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

theorem thetaFirstMode_refined_cell_lower_6_128 :
    (765882249219808295461771/25220157913274777600000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/2:ℝ) (129/256:ℝ) (32400815883885575/64547530894739456:ℝ) (24300338443/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0772).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^6*thetaFirstMode x) ≤ (3064956372564683341587947/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/2:ℝ) (129/256:ℝ) (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_129 :
    (1503271851704832382351777/50440315826549555200000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (129/256:ℝ) (65/128:ℝ) (34207530550618873/67620592658413568:ℝ) (45529041247/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0778).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^6*thetaFirstMode x) ≤ (6015937670410674137596023/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (129/256:ℝ) (65/128:ℝ) (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_130 :
    (1474003916166848271620487/50440315826549555200000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (65/128:ℝ) (131/256:ℝ) (36099919583043687/70814621492860928:ℝ) (42629049717/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0784).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^6*thetaFirstMode x) ≤ (184339340255934734881161/6305039478318694400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (65/128:ℝ) (131/256:ℝ) (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_131 :
    (180503623283691086294411/6305039478318694400000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (131/256:ℝ) (33/64:ℝ) (38081342152251545/74133397164763136:ℝ) (4986570623/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0790).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^6*thetaFirstMode x) ≤ (11557899199025016561986281/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (131/256:ℝ) (33/64:ℝ) (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_132 :
    (282683102935284232887047/10088063165309911040000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (33/64:ℝ) (133/256:ℝ) (40155261980943655/77580787335391232:ℝ) (7462350083/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0796).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^6*thetaFirstMode x) ≤ (11312967288653683900997867/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (33/64:ℝ) (133/256:ℝ) (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_133 :
    (1382231888422052162758269/50440315826549555200000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (133/256:ℝ) (67/128:ℝ) (42325249765261785/81160748912777216:ℝ) (34879063407/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0802).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^6*thetaFirstMode x) ≤ (2765867303195559298005189/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (133/256:ℝ) (67/128:ℝ) (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_134 :
    (675273105567820839865447/25220157913274777600000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (67/128:ℝ) (135/256:ℝ) (44594985633733703/84877329414207488:ℝ) (16293624337/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0808).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^6*thetaFirstMode x) ≤ (10809949883464445824714479/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (67/128:ℝ) (135/256:ℝ) (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_135 :
    (1318426091987427075488317/50440315826549555200000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (135/256:ℝ) (17/32:ℝ) (46968261643615417/88734668339038208:ℝ) (30429331477/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0814).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^6*thetaFirstMode x) ≤ (527647513414251270686069/20176126330619822080000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (135/256:ℝ) (17/32:ℝ) (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_136 :
    (160742305259738338684087/6305039478318694400000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (17/32:ℝ) (137/256:ℝ) (49448984314912455/92736998551832576:ℝ) (3549826351/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0820).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^6*thetaFirstMode x) ≤ (10293005761676970928272687/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/32:ℝ) (137/256:ℝ) (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_137 :
    (626574639443725120084971/25220157913274777600000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (137/256:ℝ) (69/128:ℝ) (52041177202362425/96888647675820032:ℝ) (13244326269/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0826).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^6*thetaFirstMode x) ≤ (179118653940100539809783/7205759403792793600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (137/256:ℝ) (69/128:ℝ) (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_138 :
    (174303362846575632760691/7205759403792793600000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (69/128:ℝ) (139/256:ℝ) (54748983505661095/101194039496677376:ℝ) (24693282551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0832).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^6*thetaFirstMode x) ≤ (9766386471827732437033667/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (69/128:ℝ) (139/256:ℝ) (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_139 :
    (1186924905572114337863681/50440315826549555200000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (139/256:ℝ) (35/64:ℝ) (57576668718214233/105657695376631808:ℝ) (23006579861/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0838).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^6*thetaFirstMode x) ≤ (1357248699172022819623629/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (139/256:ℝ) (35/64:ℝ) (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_140 :
    (288403907905234994639411/12610078956637388800000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (35/64:ℝ) (141/256:ℝ) (60528623314697447/110284235678885888:ℝ) (5355717431/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0844).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^6*thetaFirstMode x) ≤ (329793074310736673504223/14411518807585587200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (35/64:ℝ) (141/256:ℝ) (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_141 :
    (112025639276446846490159/5044031582654955520000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (141/256:ℝ) (71/128:ℝ) (63609365477706265/115078381202364416:ℝ) (1993671677/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0850).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^6*thetaFirstMode x) ≤ (640519113034656786209263/28823037615171174400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (141/256:ℝ) (71/128:ℝ) (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_142 :
    (77636152588049164053927/3602879701896396800000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (71/128:ℝ) (143/256:ℝ) (66823543863778695/120044954626783232:ℝ) (9271459071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0856).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^6*thetaFirstMode x) ≤ (4350198570381613032060367/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (71/128:ℝ) (143/256:ℝ) (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_143 :
    (1053621947284895301302389/50440315826549555200000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (143/256:ℝ) (9/16:ℝ) (70175940409072505/125188881968039936:ℝ) (17236496677/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0862).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^6*thetaFirstMode x) ≤ (1204864515194150829133347/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (143/256:ℝ) (9/16:ℝ) (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_144 :
    (255114731283161500011047/12610078956637388800000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (9/16:ℝ) (145/256:ℝ) (73671473174979463/130515194043926528:ℝ) (4003173527/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0868).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^6*thetaFirstMode x) ≤ (8168671950441528276253077/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/16:ℝ) (145/256:ℝ) (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_145 :
    (123433758917700358520931/6305039478318694400000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (145/256:ℝ) (73/128:ℝ) (77315199233958777/136029027950163968:ℝ) (1858370541/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0874).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x) ≤ (3952341184050637078628863/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (145/256:ℝ) (73/128:ℝ) (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_146 :
    (954706189386899132768553/50440315826549555200000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (73/128:ℝ) (147/256:ℝ) (81112317595871975/141735628546758656:ℝ) (13794966699/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0880).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^6*thetaFirstMode x) ≤ (305699578992263910995767/16140901064495857664000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (73/128:ℝ) (147/256:ℝ) (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_147 :
    (131745113701713860237101/7205759403792793600000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (147/256:ℝ) (37/64:ℝ) (85068172175101465/147640349954680832:ℝ) (12792559423/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0886).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x) ≤ (184562039937410589824219/10088063165309911040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (147/256:ℝ) (37/64:ℝ) (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_148 :
    (27813907637562941550287/1576259869579673600000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (37/64:ℝ) (149/256:ℝ) (89188254798735015/153748657062864896:ℝ) (370493531/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0892).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^6*thetaFirstMode x) ≤ (1781257040012163509647477/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (37/64:ℝ) (149/256:ℝ) (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_149 :
    (122605379966458351222579/7205759403792793600000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (149/256:ℝ) (75/128:ℝ) (93478208256098393/160066127045531648:ℝ) (10980903703/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0898).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x) ≤ (429404947644585422857661/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (149/256:ℝ) (75/128:ℝ) (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_150 :
    (12919295078664178580851/788129934789836800000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (75/128:ℝ) (151/256:ℝ) (97943829389918407/166598450889832448:ℝ) (158817301/1562500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0904).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^6*thetaFirstMode x) ≤ (3309582375877416883684291/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (75/128:ℝ) (151/256:ℝ) (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_151 :
    (795875439485382770645953/50440315826549555200000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (151/256:ℝ) (19/32:ℝ) (102591072229398585/173351434933815296:ℝ) (9402592489/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0910).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x) ≤ (6371394887050609917173047/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (151/256:ℝ) (19/32:ℝ) (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_152 :
    (47837217996949942790137/3152519739159347200000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (19/32:ℝ) (153/256:ℝ) (107426051165489735/180331002414712832:ℝ) (543282193/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0916).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^6*thetaFirstMode x) ≤ (1225491818515472892956923/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/32:ℝ) (153/256:ℝ) (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_153 :
    (735428621015174096832179/50440315826549555200000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (153/256:ℝ) (77/128:ℝ) (112455044168637625/187543195027552256:ℝ) (8030991557/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0922).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x) ≤ (5887626300033773010938833/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (153/256:ℝ) (77/128:ℝ) (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_154 :
    (706005846116139251113307/50440315826549555200000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (77/128:ℝ) (155/256:ℝ) (117684496049290023/194994174494087168:ℝ) (7415093177/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0928).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^6*thetaFirstMode x) ≤ (565214477420279680751733/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (77/128:ℝ) (155/256:ℝ) (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_155 :
    (677155588529793721256459/50440315826549555200000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (155/256:ℝ) (39/64:ℝ) (123121021761445337/202690224142051328:ℝ) (6842040119/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0934).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x) ≤ (2710621061718601615519381/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (155/256:ℝ) (39/64:ℝ) (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_156 :
    (81112962877270125212463/6305039478318694400000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (39/64:ℝ) (157/256:ℝ) (128771409749525095/210637750494734336:ℝ) (788649459/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0940).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^6*thetaFirstMode x) ≤ (742160769966953858725427/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (39/64:ℝ) (157/256:ℝ) (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_157 :
    (621273494346689056310797/50440315826549555200000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (157/256:ℝ) (79/128:ℝ) (134642625338852505/218843284870879232:ℝ) (5814060583/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0946).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x) ≤ (2486990606371849287334977/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (157/256:ℝ) (79/128:ℝ) (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_158 :
    (594285746969494489671007/50440315826549555200000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (79/128:ℝ) (159/256:ℝ) (140741814170019335/227313484994902016:ℝ) (5354267521/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0952).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^6*thetaFirstMode x) ≤ (2378988033841649262333873/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (79/128:ℝ) (159/256:ℝ) (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_159 :
    (567958763774728768993751/50440315826549555200000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (159/256:ℝ) (5/8:ℝ) (147076305677423353/236055136617433088:ℝ) (4927575671/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0958).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x) ≤ (162402020447936569137593/14411518807585587200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (159/256:ℝ) (5/8:ℝ) (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

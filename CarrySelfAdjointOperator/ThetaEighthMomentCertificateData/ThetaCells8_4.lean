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

theorem thetaFirstMode_refined_cell_lower_8_128 :
    (2032425384130976431151794331/265633114661417543270400000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/2:ℝ) (129/256:ℝ) (859903185597392841993/1713045360379148700160:ℝ) (3037286171/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0773).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^8*thetaFirstMode x) ≤ (162669788657062122171797495563/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/2:ℝ) (129/256:ℝ) (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_129 :
    (4051566431879317113791576951/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (129/256:ℝ) (65/128:ℝ) (922036494355905427191/1822640620152625231360:ℝ) (5690650121/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0779).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^8*thetaFirstMode x) ≤ (81069738957932661980253567137/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (129/256:ℝ) (65/128:ℝ) (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_130 :
    (3586019104470188750168493249/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (65/128:ℝ) (131/256:ℝ) (988128929174544916209/1938322640485932981760:ℝ) (42625452771/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0785).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^8*thetaFirstMode x) ≤ (53816226210407978043261168979/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (65/128:ℝ) (131/256:ℝ) (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_131 :
    (32104242760798553982351779533/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (131/256:ℝ) (33/64:ℝ) (1058399498889348955407/2060378912321919132160:ℝ) (39889197553/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0791).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^8*thetaFirstMode x) ≤ (321199927932213377080067205503/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (131/256:ℝ) (33/64:ℝ) (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_132 :
    (6380668679849570852790724133/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (33/64:ℝ) (133/256:ℝ) (226615503159325427085/437821630895601469952:ℝ) (7461719873/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0797).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^8*thetaFirstMode x) ≤ (63838531553390959796745536857/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (33/64:ℝ) (133/256:ℝ) (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_133 :
    (1319673106966110071215100621/177088743107611695513600000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (133/256:ℝ) (67/128:ℝ) (1212402996478512506943/2324820661745853468160:ℝ) (4359514533/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0803).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^8*thetaFirstMode x) ≤ (52813724884935991267687936007/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (133/256:ℝ) (67/128:ℝ) (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_134 :
    (31411434780730857928226279023/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (67/128:ℝ) (135/256:ℝ) (1296627075007226251641/2467838661023287068160:ℝ) (32584493593/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0809).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^8*thetaFirstMode x) ≤ (104758861180731483282283635361/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (67/128:ℝ) (135/256:ℝ) (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_135 :
    (972563020256588240655499883/132816557330708771635200000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (135/256:ℝ) (17/32:ℝ) (1386012428812593345159/2618496675601163368960:ℝ) (950836163/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0815).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^8*thetaFirstMode x) ≤ (2594864022840666716212933/354177486215223391027200000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (135/256:ℝ) (17/32:ℝ) (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_136 :
    (30804802877308971080365043861/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (17/32:ℝ) (137/256:ℝ) (1480833717501674392857/2777141897728678812160:ℝ) (28396206701/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0821).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^8*thetaFirstMode x) ≤ (34245852288782692327044292509/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (17/32:ℝ) (137/256:ℝ) (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_137 :
    (30460762034929361033272921183/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (137/256:ℝ) (69/128:ℝ) (316275606984747764475/588826913916326538752:ℝ) (26486408473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0827).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^8*thetaFirstMode x) ≤ (30477322981410676607618475389/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (137/256:ℝ) (69/128:ℝ) (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_138 :
    (30090924080197149706743541573/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (69/128:ℝ) (139/256:ℝ) (1687945374778197279393/3119848372759046172160:ℝ) (24691188943/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0833).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^8*thetaFirstMode x) ≤ (301075657442119495487448327803/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (69/128:ℝ) (139/256:ℝ) (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_139 :
    (7424093925316426489555481287/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (139/256:ℝ) (35/64:ℝ) (1800849110067536394591/3304670826434478952960:ℝ) (5751156907/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0839).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^8*thetaFirstMode x) ≤ (792348848726044933376100197/113336795588871485128704000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (139/256:ℝ) (35/64:ℝ) (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_140 :
    (9759418492160165753818244629/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (35/64:ℝ) (141/256:ℝ) (1920416486701757070609/3499003694289312924160:ℝ) (21421050267/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0845).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^8*thetaFirstMode x) ≤ (48825016076959591618348140127/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (35/64:ℝ) (141/256:ℝ) (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_141 :
    (576754977911972691543603829/85002596691653613846528000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (141/256:ℝ) (71/128:ℝ) (2046989131565308077807/3703263400356200988160:ℝ) (398700439/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0851).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^8*thetaFirstMode x) ≤ (24045445475665789387466417977/3541774862152233910272000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (141/256:ℝ) (71/128:ℝ) (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_142 :
    (1418804162795643212901477323/212506491729134034616320000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (71/128:ℝ) (143/256:ℝ) (436184715072406009365/783576290780361661952:ℝ) (927067013/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0857).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^8*thetaFirstMode x) ≤ (7098220957223062014552077533/1062532458645670173081600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (71/128:ℝ) (143/256:ℝ) (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_143 :
    (27894522479658640154462226611/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (143/256:ℝ) (9/16:ℝ) (2322591790558180904343/4143304883478902172160:ℝ) (17235028451/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0863).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^8*thetaFirstMode x) ≤ (31012579241917396133706948371/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (143/256:ℝ) (9/16:ℝ) (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_144 :
    (13697180931424301422979765209/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (9/16:ℝ) (145/256:ℝ) (2472381744748202416041/4379996680278775605760:ℝ) (8005664329/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0869).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^8*thetaFirstMode x) ≤ (30456824838628482108049582451/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (9/16:ℝ) (145/256:ℝ) (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_145 :
    (26876922789535260862889262143/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (145/256:ℝ) (73/128:ℝ) (2630697969772508777559/4628436250915918927360:ℝ) (14865695153/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0875).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^8*thetaFirstMode x) ≤ (33617085494799664266725123549/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (145/256:ℝ) (73/128:ℝ) (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_146 :
    (13171773725726112655013474341/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (73/128:ℝ) (147/256:ℝ) (2797962146921232130257/4889119879777782300160:ℝ) (6896893831/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0881).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^8*thetaFirstMode x) ≤ (263602417447678572129200929091/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (73/128:ℝ) (147/256:ℝ) (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_147 :
    (25795593568548646767109353593/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (147/256:ℝ) (37/64:ℝ) (594922741712509294755/1032512240214680279552:ℝ) (12791464733/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0887).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^8*thetaFirstMode x) ≤ (2581222028517990899005979939/425012983458268069232640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (147/256:ℝ) (37/64:ℝ) (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_148 :
    (12617214589141941333395340773/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (37/64:ℝ) (149/256:ℝ) (3161110456538910701793/5449291680715587228160:ℝ) (5927388593/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0893).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^8*thetaFirstMode x) ≤ (15781857662355019354384481411/2656331146614175432704000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (37/64:ℝ) (149/256:ℝ) (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_149 :
    (770669608850841882983802451/132816557330708771635200000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (149/256:ℝ) (75/128:ℝ) (3357929197679323400991/5749861108172310146560:ℝ) (343123801/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0899).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^8*thetaFirstMode x) ≤ (61694677802058119216835956437/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (149/256:ℝ) (75/128:ℝ) (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_150 :
    (2675329088585447289499312003/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (75/128:ℝ) (151/256:ℝ) (3565566396780466626009/6064838098423837058560:ℝ) (10163434077/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0905).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^8*thetaFirstMode x) ≤ (24094290476101012184825640727/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (75/128:ℝ) (151/256:ℝ) (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_151 :
    (23485400614077577188318370537/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (151/256:ℝ) (19/32:ℝ) (3784538847414433095207/6394810604163109788160:ℝ) (9401783617/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0911).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^8*thetaFirstMode x) ≤ (235015991554630829383028370599/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (151/256:ℝ) (19/32:ℝ) (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_152 :
    (2860637853306774931777867459/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (19/32:ℝ) (153/256:ℝ) (803076872185116228645/1348077287675556311552:ℝ) (1086470779/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0917).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^8*thetaFirstMode x) ≤ (9160462569179383826018441519/1700051933833072276930560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (19/32:ℝ) (153/256:ℝ) (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_153 :
    (22278413088820590317602400503/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (153/256:ℝ) (77/128:ℝ) (4258662473983944316743/7102193807453257500160:ℝ) (8030298673/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0923).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^8*thetaFirstMode x) ≤ (222943073489698453421014118561/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (153/256:ℝ) (77/128:ℝ) (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_154 :
    (3611109562973233789991579087/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (77/128:ℝ) (155/256:ℝ) (4514955175067537709441/7480881854937014095360:ℝ) (3707226231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0929).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^8*thetaFirstMode x) ≤ (6022882877722685710591648847/1180591620717411303424000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (77/128:ℝ) (155/256:ℝ) (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_155 :
    (10525569376061739963693976421/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (155/256:ℝ) (39/64:ℝ) (4784867650250851000959/7877121216105401397760:ℝ) (3420724001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0935).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^8*thetaFirstMode x) ≤ (3291667655437127760109720429/664082786653543858176000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (155/256:ℝ) (39/64:ℝ) (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_156 :
    (10216566658013912804746482739/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (39/64:ℝ) (157/256:ℝ) (5069029048681798692657/8291604583475060892160:ℝ) (3154324399/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0941).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^8*thetaFirstMode x) ≤ (204484678805618746576112320501/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (39/64:ℝ) (157/256:ℝ) (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_157 :
    (4953471608847290119886514821/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (157/256:ℝ) (79/128:ℝ) (1073618653626882244035/1745009456680404157952:ℝ) (1453388951/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0947).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^8*thetaFirstMode x) ≤ (6609669642230334517928847419/1416709944860893564108800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (157/256:ℝ) (79/128:ℝ) (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_158 :
    (3838921834898331984681660647/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (79/128:ℝ) (159/256:ℝ) (5682739761029596469193/9178187863912459548160:ℝ) (1070760377/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0953).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^8*thetaFirstMode x) ≤ (96047538864238951443610161389/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (79/128:ℝ) (159/256:ℝ) (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_159 :
    (1857647500518653439223913201/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (159/256:ℝ) (5/8:ℝ) (6013674361321379726391/9651788693910057372160:ℝ) (492714641/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0959).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^8*thetaFirstMode x) ≤ (46477846227237640918891132561/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (159/256:ℝ) (5/8:ℝ) (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

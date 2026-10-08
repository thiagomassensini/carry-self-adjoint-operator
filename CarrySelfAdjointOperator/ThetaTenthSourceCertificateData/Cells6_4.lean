import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature4

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_128 :
    (30372360258868239/1000000000000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/2:ℝ) (129/256:ℝ)
    (32400815883885575/64547530894739456:ℝ) (24300338443/50000000000000:ℝ) (56635078811378937/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_128
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0772).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^6*thetaFirstMode x) ≤ (1518650536891357/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/2:ℝ) (129/256:ℝ)
    (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ) (56635078811378937/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_128 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_129 :
    (5961494769926529/200000000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (129/256:ℝ) (65/128:ℝ)
    (34207530550618873/67620592658413568:ℝ) (45529041247/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_129
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0778).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^6*thetaFirstMode x) ≤ (1863007876133233/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (129/256:ℝ) (65/128:ℝ)
    (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_129 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_130 :
    (2922721299074853/100000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (65/128:ℝ) (131/256:ℝ)
    (36099919583043687/70814621492860928:ℝ) (42629049717/100000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_130
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0784).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^6*thetaFirstMode x) ≤ (29227866290206111/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (65/128:ℝ) (131/256:ℝ)
    (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_130 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_131 :
    (28632931686634111/1000000000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (131/256:ℝ) (33/64:ℝ)
    (38081342152251545/74133397164763136:ℝ) (4986570623/12500000000000:ℝ) (12229335208502793/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_131
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0790).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^6*thetaFirstMode x) ≤ (28633585556806661/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (131/256:ℝ) (33/64:ℝ)
    (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ) (12229335208502793/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_131 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_132 :
    (28025987088354659/1000000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (33/64:ℝ) (133/256:ℝ)
    (40155261980943655/77580787335391232:ℝ) (7462350083/20000000000000:ℝ) (46534764213673919/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_132
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0796).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^6*thetaFirstMode x) ≤ (14013320483782191/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (33/64:ℝ) (133/256:ℝ)
    (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ) (46534764213673919/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_132 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_133 :
    (3425966881939189/125000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (133/256:ℝ) (67/128:ℝ)
    (42325249765261785/81160748912777216:ℝ) (34879063407/100000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_133
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0802).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^6*thetaFirstMode x) ≤ (27408388383020491/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (133/256:ℝ) (67/128:ℝ)
    (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_133 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_134 :
    (26779525838494509/1000000000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (67/128:ℝ) (135/256:ℝ)
    (44594985633733703/84877329414207488:ℝ) (16293624337/50000000000000:ℝ) (21020821257204279/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_134
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0808).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^6*thetaFirstMode x) ≤ (6695044513866857/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (67/128:ℝ) (135/256:ℝ)
    (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (21020821257204279/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_134 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_135 :
    (13071349946973881/500000000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (135/256:ℝ) (17/32:ℝ)
    (46968261643615417/88734668339038208:ℝ) (30429331477/100000000000000:ℝ) (2495419722748173/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_135
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0814).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^6*thetaFirstMode x) ≤ (13071675221934887/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (135/256:ℝ) (17/32:ℝ)
    (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ) (2495419722748173/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_135 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_136 :
    (25498583847801301/1000000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (17/32:ℝ) (137/256:ℝ)
    (49448984314912455/92736998551832576:ℝ) (3549826351/12500000000000:ℝ) (2368537855823959/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_136
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0820).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^6*thetaFirstMode x) ≤ (25499232178344171/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (17/32:ℝ) (137/256:ℝ)
    (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ) (2368537855823959/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_136 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_137 :
    (155303041362743/6250000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (137/256:ℝ) (69/128:ℝ)
    (52041177202362425/96888647675820032:ℝ) (13244326269/50000000000000:ℝ) (35949100893156969/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_137
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0826).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^6*thetaFirstMode x) ≤ (24849132184318369/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (137/256:ℝ) (69/128:ℝ)
    (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ) (35949100893156969/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_137 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_138 :
    (6048423929961451/250000000000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (69/128:ℝ) (139/256:ℝ)
    (54748983505661095/101194039496677376:ℝ) (24693282551/100000000000000:ℝ) (68163974002885677/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_138
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0832).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^6*thetaFirstMode x) ≤ (604858449588179/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (69/128:ℝ) (139/256:ℝ)
    (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ) (68163974002885677/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_138 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_139 :
    (11767736876452189/500000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (139/256:ℝ) (35/64:ℝ)
    (57576668718214233/105657695376631808:ℝ) (23006579861/100000000000000:ℝ) (6458610204731741/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_139
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0838).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^6*thetaFirstMode x) ≤ (1471007011409397/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (139/256:ℝ) (35/64:ℝ)
    (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ) (6458610204731741/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_139 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_140 :
    (571876377028899/25000000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (35/64:ℝ) (141/256:ℝ)
    (60528623314697447/110284235678885888:ℝ) (5355717431/25000000000000:ℝ) (30580084349091647/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_140
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0844).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^6*thetaFirstMode x) ≤ (11437844578450103/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (35/64:ℝ) (141/256:ℝ)
    (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_140 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_141 :
    (5553410682315953/250000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (141/256:ℝ) (71/128:ℝ)
    (63609365477706265/115078381202364416:ℝ) (1993671677/10000000000000:ℝ) (904402682722187/15625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_141
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0850).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^6*thetaFirstMode x) ≤ (1110713597004767/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (141/256:ℝ) (71/128:ℝ)
    (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (904402682722187/15625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_141 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_142 :
    (21552405480509223/1000000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (71/128:ℝ) (143/256:ℝ)
    (66823543863778695/120044954626783232:ℝ) (9271459071/50000000000000:ℝ) (27373264861214221/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_142
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0856).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^6*thetaFirstMode x) ≤ (4310605865921509/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (71/128:ℝ) (143/256:ℝ)
    (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (27373264861214221/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_142 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_143 :
    (1044623760479787/50000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (143/256:ℝ) (9/16:ℝ)
    (70175940409072505/125188881968039936:ℝ) (17236496677/100000000000000:ℝ) (25875044056449187/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_143
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0862).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^6*thetaFirstMode x) ≤ (10201705669143/488281250000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (143/256:ℝ) (9/16:ℝ)
    (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ) (25875044056449187/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_143 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_144 :
    (20234944422252877/1000000000000000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (9/16:ℝ) (145/256:ℝ)
    (73671473174979463/130515194043926528:ℝ) (4003173527/25000000000000:ℝ) (9777624868232171/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_144
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0868).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^6*thetaFirstMode x) ≤ (2023555610439069/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/16:ℝ) (145/256:ℝ)
    (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ) (9777624868232171/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_144 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_145 :
    (3916172808444611/200000000000000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (145/256:ℝ) (73/128:ℝ)
    (77315199233958777/136029027950163968:ℝ) (1858370541/12500000000000:ℝ) (23078176624776193/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_145
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0874).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^6*thetaFirstMode x) ≤ (1958146894997769/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (145/256:ℝ) (73/128:ℝ)
    (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_145 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_146 :
    (757249656774397/40000000000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (73/128:ℝ) (147/256:ℝ)
    (81112317595871975/141735628546758656:ℝ) (13794966699/100000000000000:ℝ) (21775266004453039/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_146
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0880).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^6*thetaFirstMode x) ≤ (2366479888981849/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (73/128:ℝ) (147/256:ℝ)
    (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_146 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_147 :
    (18287038569745973/1000000000000000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (147/256:ℝ) (37/64:ℝ)
    (85068172175101465/147640349954680832:ℝ) (12792559423/100000000000000:ℝ) (20533232419187341/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_147
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0886).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^6*thetaFirstMode x) ≤ (4571907156324011/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (147/256:ℝ) (37/64:ℝ)
    (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ) (20533232419187341/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_147 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_148 :
    (551536583185173/31250000000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (37/64:ℝ) (149/256:ℝ)
    (89188254798735015/153748657062864896:ℝ) (370493531/3125000000000:ℝ) (19350003728002473/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_148
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0892).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^6*thetaFirstMode x) ≤ (17649752674361447/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (37/64:ℝ) (149/256:ℝ)
    (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_148 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_149 :
    (3403700943878299/200000000000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (149/256:ℝ) (75/128:ℝ)
    (93478208256098393/160066127045531648:ℝ) (10980903703/100000000000000:ℝ) (1822353562406607/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_149
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0898).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^6*thetaFirstMode x) ≤ (4254769575494513/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (149/256:ℝ) (75/128:ℝ)
    (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (1822353562406607/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_149 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_150 :
    (3279171712672097/200000000000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (75/128:ℝ) (151/256:ℝ)
    (97943829389918407/166598450889832448:ℝ) (158817301/1562500000000:ℝ) (17151813610223543/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_150
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0904).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^6*thetaFirstMode x) ≤ (16396423349514751/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (75/128:ℝ) (151/256:ℝ)
    (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ) (17151813610223543/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_150 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_151 :
    (15781999981877839/1000000000000000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (151/256:ℝ) (19/32:ℝ)
    (102591072229398585/173351434933815296:ℝ) (9402592489/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_151
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0910).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^6*thetaFirstMode x) ≤ (3945638906062727/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (151/256:ℝ) (19/32:ℝ)
    (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_151 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_152 :
    (15177646120927301/1000000000000000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (19/32:ℝ) (153/256:ℝ)
    (107426051165489735/180331002414712832:ℝ) (543282193/6250000000000:ℝ) (30329419364521959/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_152
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0916).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^6*thetaFirstMode x) ≤ (1517819229205789/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (19/32:ℝ) (153/256:ℝ)
    (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30329419364521959/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_152 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_153 :
    (14583463091176721/1000000000000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (153/256:ℝ) (77/128:ℝ)
    (112455044168637625/187543195027552256:ℝ) (8030991557/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_153
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0922).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^6*thetaFirstMode x) ≤ (7291999743008109/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (153/256:ℝ) (77/128:ℝ)
    (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_153 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_154 :
    (14000065791105849/1000000000000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (77/128:ℝ) (155/256:ℝ)
    (117684496049290023/194994174494087168:ℝ) (7415093177/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_154
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0928).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^6*thetaFirstMode x) ≤ (7000296061760961/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (77/128:ℝ) (155/256:ℝ)
    (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_154 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_155 :
    (6714008962965833/500000000000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (155/256:ℝ) (39/64:ℝ)
    (123121021761445337/202690224142051328:ℝ) (6842040119/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_155
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0934).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^6*thetaFirstMode x) ≤ (33571334833321/2500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (155/256:ℝ) (39/64:ℝ)
    (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_155 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_156 :
    (3216958059512131/250000000000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (39/64:ℝ) (157/256:ℝ)
    (128771409749525095/210637750494734336:ℝ) (788649459/12500000000000:ℝ) (941002024403311/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_156
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0940).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^6*thetaFirstMode x) ≤ (6434168839941473/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (39/64:ℝ) (157/256:ℝ)
    (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ) (941002024403311/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_156 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_157 :
    (12319970913289337/1000000000000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (157/256:ℝ) (79/128:ℝ)
    (134642625338852505/218843284870879232:ℝ) (5814060583/100000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_157
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0946).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^6*thetaFirstMode x) ≤ (1232046557033847/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (157/256:ℝ) (79/128:ℝ)
    (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_157 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_158 :
    (11784846168966793/1000000000000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (79/128:ℝ) (159/256:ℝ)
    (140741814170019335/227313484994902016:ℝ) (5354267521/100000000000000:ℝ) (10318317444428261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_158
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0952).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^6*thetaFirstMode x) ≤ (94282638767721/8000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (79/128:ℝ) (159/256:ℝ)
    (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ) (10318317444428261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_158 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_159 :
    (1126282102155631/100000000000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (159/256:ℝ) (5/8:ℝ)
    (147076305677423353/236055136617433088:ℝ) (4927575671/100000000000000:ℝ) (9654376044293469/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_159
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0958).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^6*thetaFirstMode x) ≤ (11263293543521163/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (159/256:ℝ) (5/8:ℝ)
    (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ) (9654376044293469/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_159 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

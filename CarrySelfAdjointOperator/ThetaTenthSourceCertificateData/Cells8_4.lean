import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature4

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_128 :
    (7652383658708183/1000000000000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/2:ℝ) (129/256:ℝ)
    (859903185597392841993/1713045360379148700160:ℝ) (3037286171/6250000000000:ℝ) (56635078811378937/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_128
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0773).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^8*thetaFirstMode x) ≤ (956568435083541/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/2:ℝ) (129/256:ℝ)
    (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ) (56635078811378937/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_128 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_129 :
    (476712142838841/62500000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (129/256:ℝ) (65/128:ℝ)
    (922036494355905427191/1822640620152625231360:ℝ) (5690650121/12500000000000:ℝ) (21586144939916833/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_129
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0779).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^8*thetaFirstMode x) ≤ (3813780549541341/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (129/256:ℝ) (65/128:ℝ)
    (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_129 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_130 :
    (7594854799199457/1000000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (65/128:ℝ) (131/256:ℝ)
    (988128929174544916209/1938322640485932981760:ℝ) (42625452771/100000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_130
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0785).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^8*thetaFirstMode x) ≤ (3797512246503043/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (65/128:ℝ) (131/256:ℝ)
    (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_130 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_131 :
    (377744318573377/50000000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (131/256:ℝ) (33/64:ℝ)
    (1058399498889348955407/2060378912321919132160:ℝ) (39889197553/100000000000000:ℝ) (12229335208502793/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_131
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0791).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^8*thetaFirstMode x) ≤ (3777529413159571/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (131/256:ℝ) (33/64:ℝ)
    (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ) (12229335208502793/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_131 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_132 :
    (7507630016381329/1000000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (33/64:ℝ) (133/256:ℝ)
    (226615503159325427085/437821630895601469952:ℝ) (7461719873/20000000000000:ℝ) (46534764213673919/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_132
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0797).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^8*thetaFirstMode x) ≤ (300312204265389/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (33/64:ℝ) (133/256:ℝ)
    (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ) (46534764213673919/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_132 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_133 :
    (1490649172586043/200000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (133/256:ℝ) (67/128:ℝ)
    (1212402996478512506943/2324820661745853468160:ℝ) (4359514533/12500000000000:ℝ) (88487185923985229/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_133
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0803).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^8*thetaFirstMode x) ≤ (7453423456002123/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (133/256:ℝ) (67/128:ℝ)
    (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_133 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_134 :
    (295676493972789/40000000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (67/128:ℝ) (135/256:ℝ)
    (1296627075007226251641/2467838661023287068160:ℝ) (32584493593/100000000000000:ℝ) (21020821257204279/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_134
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0809).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^8*thetaFirstMode x) ≤ (739209230645917/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (67/128:ℝ) (135/256:ℝ)
    (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (21020821257204279/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_134 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_135 :
    (457739084353001/62500000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (135/256:ℝ) (17/32:ℝ)
    (1386012428812593345159/2618496675601163368960:ℝ) (950836163/3125000000000:ℝ) (2495419722748173/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_135
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0815).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^8*thetaFirstMode x) ≤ (3662003762900237/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (135/256:ℝ) (17/32:ℝ)
    (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ) (2495419722748173/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_135 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_136 :
    (7249197234556163/1000000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (17/32:ℝ) (137/256:ℝ)
    (1480833717501674392857/2777141897728678812160:ℝ) (28396206701/100000000000000:ℝ) (2368537855823959/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_136
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0821).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^8*thetaFirstMode x) ≤ (906172684885791/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (17/32:ℝ) (137/256:ℝ)
    (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ) (2368537855823959/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_136 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_137 :
    (1792063968421449/250000000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (137/256:ℝ) (69/128:ℝ)
    (316275606984747764475/588826913916326538752:ℝ) (26486408473/100000000000000:ℝ) (35949100893156969/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_137
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0827).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^8*thetaFirstMode x) ≤ (7168442030507291/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (137/256:ℝ) (69/128:ℝ)
    (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ) (35949100893156969/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_137 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_138 :
    (7081243584743991/1000000000000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (69/128:ℝ) (139/256:ℝ)
    (1687945374778197279393/3119848372759046172160:ℝ) (24691188943/100000000000000:ℝ) (68163974002885677/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_138
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0833).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^8*thetaFirstMode x) ≤ (1770357873188119/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (69/128:ℝ) (139/256:ℝ)
    (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ) (68163974002885677/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_138 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_139 :
    (1397683207278409/200000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (139/256:ℝ) (35/64:ℝ)
    (1800849110067536394591/3304670826434478952960:ℝ) (5751156907/25000000000000:ℝ) (6458610204731741/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_139
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0839).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^8*thetaFirstMode x) ≤ (3494302764909141/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (139/256:ℝ) (35/64:ℝ)
    (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ) (6458610204731741/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_139 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_140 :
    (3445020554896543/500000000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (35/64:ℝ) (141/256:ℝ)
    (1920416486701757070609/3499003694289312924160:ℝ) (21421050267/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_140
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0845).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^8*thetaFirstMode x) ≤ (3445116009457829/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (35/64:ℝ) (141/256:ℝ)
    (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_140 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_141 :
    (6786397727217267/1000000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (141/256:ℝ) (71/128:ℝ)
    (2046989131565308077807/3703263400356200988160:ℝ) (398700439/2000000000000:ℝ) (904402682722187/15625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_141
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0851).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^8*thetaFirstMode x) ≤ (6786589877991959/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (141/256:ℝ) (71/128:ℝ)
    (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (904402682722187/15625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_141 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_142 :
    (6677774651198869/1000000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (71/128:ℝ) (143/256:ℝ)
    (436184715072406009365/783576290780361661952:ℝ) (927067013/5000000000000:ℝ) (27373264861214221/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_142
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0857).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^8*thetaFirstMode x) ≤ (3338983933326369/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (71/128:ℝ) (143/256:ℝ)
    (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (27373264861214221/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_142 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_143 :
    (262578770606227/40000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (143/256:ℝ) (9/16:ℝ)
    (2322591790558180904343/4143304883478902172160:ℝ) (17235028451/100000000000000:ℝ) (25875044056449187/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_143
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0863).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^8*thetaFirstMode x) ≤ (65646633653247/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (143/256:ℝ) (9/16:ℝ)
    (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ) (25875044056449187/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_143 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_144 :
    (3223393168929803/500000000000000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (9/16:ℝ) (145/256:ℝ)
    (2472381744748202416041/4379996680278775605760:ℝ) (8005664329/50000000000000:ℝ) (9777624868232171/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_144
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0869).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^8*thetaFirstMode x) ≤ (6446981140166857/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/16:ℝ) (145/256:ℝ)
    (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ) (9777624868232171/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_144 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_145 :
    (6325036779756803/1000000000000000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (145/256:ℝ) (73/128:ℝ)
    (2630697969772508777559/4628436250915918927360:ℝ) (14865695153/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_145
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0875).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^8*thetaFirstMode x) ≤ (1581308025088437/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (145/256:ℝ) (73/128:ℝ)
    (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_145 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_146 :
    (6199536400537503/1000000000000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (73/128:ℝ) (147/256:ℝ)
    (2797962146921232130257/4889119879777782300160:ℝ) (6896893831/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_146
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0881).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^8*thetaFirstMode x) ≤ (1549933013345581/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (73/128:ℝ) (147/256:ℝ)
    (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_146 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_147 :
    (3035302333450563/500000000000000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (147/256:ℝ) (37/64:ℝ)
    (594922741712509294755/1032512240214680279552:ℝ) (12791464733/100000000000000:ℝ) (20533232419187341/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_147
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0887).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^8*thetaFirstMode x) ≤ (6070800465628863/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (147/256:ℝ) (37/64:ℝ)
    (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ) (20533232419187341/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_147 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_148 :
    (1484640869121119/250000000000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (37/64:ℝ) (149/256:ℝ)
    (3161110456538910701793/5449291680715587228160:ℝ) (5927388593/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_148
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0893).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^8*thetaFirstMode x) ≤ (14846898085243/2500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (37/64:ℝ) (149/256:ℝ)
    (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_148 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_149 :
    (2901867972746479/500000000000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (149/256:ℝ) (75/128:ℝ)
    (3357929197679323400991/5749861108172310146560:ℝ) (343123801/3125000000000:ℝ) (1822353562406607/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_149
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0899).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^8*thetaFirstMode x) ≤ (5803931474969877/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (149/256:ℝ) (75/128:ℝ)
    (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (1822353562406607/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_149 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_150 :
    (5666445219521331/1000000000000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (75/128:ℝ) (151/256:ℝ)
    (3565566396780466626009/6064838098423837058560:ℝ) (10163434077/100000000000000:ℝ) (17151813610223543/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_150
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0905).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^8*thetaFirstMode x) ≤ (2833320167307323/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (75/128:ℝ) (151/256:ℝ)
    (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ) (17151813610223543/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_150 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_151 :
    (2763506656560259/500000000000000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (151/256:ℝ) (19/32:ℝ)
    (3784538847414433095207/6394810604163109788160:ℝ) (9401783617/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_151
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0911).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^8*thetaFirstMode x) ≤ (2763603914519793/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (151/256:ℝ) (19/32:ℝ)
    (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_151 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_152 :
    (2692879992429463/500000000000000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (19/32:ℝ) (153/256:ℝ)
    (803076872185116228645/1348077287675556311552:ℝ) (1086470779/12500000000000:ℝ) (30329419364521959/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_152
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0917).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^8*thetaFirstMode x) ≤ (5385953717588189/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (19/32:ℝ) (153/256:ℝ)
    (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30329419364521959/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_152 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_153 :
    (5243001646045963/1000000000000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (153/256:ℝ) (77/128:ℝ)
    (4258662473983944316743/7102193807453257500160:ℝ) (8030298673/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_153
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0923).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^8*thetaFirstMode x) ≤ (262159720716889/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (153/256:ℝ) (77/128:ℝ)
    (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_153 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_154 :
    (5099050316063131/1000000000000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (77/128:ℝ) (155/256:ℝ)
    (4514955175067537709441/7480881854937014095360:ℝ) (3707226231/50000000000000:ℝ) (13373238132940231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_154
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0929).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^8*thetaFirstMode x) ≤ (5099241941234307/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (77/128:ℝ) (155/256:ℝ)
    (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_154 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_155 :
    (4954212624527141/1000000000000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (155/256:ℝ) (39/64:ℝ)
    (4784867650250851000959/7877121216105401397760:ℝ) (3420724001/50000000000000:ℝ) (2509238535479287/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_155
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0935).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^8*thetaFirstMode x) ≤ (4954402930124897/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (155/256:ℝ) (39/64:ℝ)
    (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_155 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_156 :
    (2404394430730391/500000000000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (39/64:ℝ) (157/256:ℝ)
    (5069029048681798692657/8291604583475060892160:ℝ) (3154324399/50000000000000:ℝ) (941002024403311/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_156
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0941).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^8*thetaFirstMode x) ≤ (4808977675857273/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (39/64:ℝ) (157/256:ℝ)
    (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ) (941002024403311/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_156 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_157 :
    (2331536043367389/500000000000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (157/256:ℝ) (79/128:ℝ)
    (1073618653626882244035/1745009456680404157952:ℝ) (1453388951/25000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_157
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0947).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^8*thetaFirstMode x) ≤ (466325924152983/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (157/256:ℝ) (79/128:ℝ)
    (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_157 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_158 :
    (2258673645776527/500000000000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (79/128:ℝ) (159/256:ℝ)
    (5682739761029596469193/9178187863912459548160:ℝ) (1070760377/20000000000000:ℝ) (10318317444428261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_158
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0953).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^8*thetaFirstMode x) ≤ (2258766311446633/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (79/128:ℝ) (159/256:ℝ)
    (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ) (10318317444428261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_158 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_159 :
    (4371890623965597/1000000000000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (159/256:ℝ) (5/8:ℝ)
    (6013674361321379726391/9651788693910057372160:ℝ) (492714641/10000000000000:ℝ) (9654376044293469/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_159
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0959).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^8*thetaFirstMode x) ≤ (874414794555557/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (159/256:ℝ) (5/8:ℝ)
    (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ) (9654376044293469/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_159 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

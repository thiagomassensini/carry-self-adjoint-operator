import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature4

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_4_128 :
    (941800999037319/7812500000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (1/2:ℝ) (129/256:ℝ)
    (1051135758085/2094049199616:ℝ) (4860477567/10000000000000:ℝ) (56635078811378937/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_128
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0771).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^4*thetaFirstMode x) ≤ (7534569419941989/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (1/2:ℝ) (129/256:ℝ)
    (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ) (56635078811378937/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_128 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_129 :
    (116488426290251971/1000000000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (129/256:ℝ) (65/128:ℝ)
    (1092676686395/2159997467136:ℝ) (45532882117/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_129
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0777).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^4*thetaFirstMode x) ≤ (364034300003107/3125000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (129/256:ℝ) (65/128:ℝ)
    (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_129 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_130 :
    (112477028377891639/1000000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (65/128:ℝ) (131/256:ℝ)
    (378506907135/742497101312:ℝ) (42632647211/100000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_130
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0783).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^4*thetaFirstMode x) ≤ (112479543517912909/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (65/128:ℝ) (131/256:ℝ)
    (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_130 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_131 :
    (27130142667962617/250000000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (131/256:ℝ) (33/64:ℝ)
    (1179698283715/2296554671616:ℝ) (1595837317/4000000000000:ℝ) (12229335208502793/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_131
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0789).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^4*thetaFirstMode x) ≤ (54261524933925703/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (131/256:ℝ) (33/64:ℝ)
    (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ) (12229335208502793/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_131 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_132 :
    (104623011973749557/1000000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (33/64:ℝ) (133/256:ℝ)
    (1225240263725/2367211716096:ℝ) (18657450969/50000000000000:ℝ) (46534764213673919/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_132
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0795).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^4*thetaFirstMode x) ≤ (104625453923532127/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (33/64:ℝ) (133/256:ℝ)
    (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ) (46534764213673919/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_132 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_133 :
    (100788033018129349/1000000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (133/256:ℝ) (67/128:ℝ)
    (424059341745/813162255872:ℝ) (3488201099/10000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_133
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0801).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^4*thetaFirstMode x) ≤ (25197609122627619/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (133/256:ℝ) (67/128:ℝ)
    (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_133 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_134 :
    (19403807407844973/200000000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (67/128:ℝ) (135/256:ℝ)
    (1320543409045/2513404340736:ℝ) (8147501041/25000000000000:ℝ) (21020821257204279/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_134
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0807).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^4*thetaFirstMode x) ≤ (48510700439709177/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (67/128:ℝ) (135/256:ℝ)
    (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (21020821257204279/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_134 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_135 :
    (93319151236001363/1000000000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (135/256:ℝ) (17/32:ℝ)
    (1370368736555/2588989134336:ℝ) (15215953059/50000000000000:ℝ) (2495419722748173/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_135
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0813).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^4*thetaFirstMode x) ≤ (93321474360627703/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (135/256:ℝ) (17/32:ℝ)
    (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ) (2495419722748173/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_135 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_136 :
    (44845614530490609/500000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (17/32:ℝ) (137/256:ℝ)
    (473895604455/888755343872:ℝ) (14200507633/50000000000000:ℝ) (2368537855823959/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_136
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0819).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^4*thetaFirstMode x) ≤ (2802922202011489/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (17/32:ℝ) (137/256:ℝ)
    (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ) (2368537855823959/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_136 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_137 :
    (86137853319634123/1000000000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (137/256:ℝ) (69/128:ℝ)
    (1474530932875/2745260100096:ℝ) (26490896929/100000000000000:ℝ) (35949100893156969/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_137
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0825).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^4*thetaFirstMode x) ≤ (86140092072368899/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (137/256:ℝ) (69/128:ℝ)
    (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ) (35949100893156969/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_137 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_138 :
    (82661340026445181/1000000000000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (69/128:ℝ) (139/256:ℝ)
    (1528934879885/2825996591616:ℝ) (24695376463/100000000000000:ℝ) (68163974002885677/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_138
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0831).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^4*thetaFirstMode x) ≤ (20665883818710591/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (69/128:ℝ) (139/256:ℝ)
    (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ) (68163974002885677/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_138 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_139 :
    (15852748594804817/200000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (139/256:ℝ) (35/64:ℝ)
    (528310978065/969500314112:ℝ) (184068259/800000000000:ℝ) (6458610204731741/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_139
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0837).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^4*thetaFirstMode x) ≤ (4954118371609273/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (139/256:ℝ) (35/64:ℝ)
    (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ) (6458610204731741/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_139 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_140 :
    (9493357372778883/125000000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (35/64:ℝ) (141/256:ℝ)
    (1642559874205/2992798772736:ℝ) (21424689441/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_140
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0843).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^4*thetaFirstMode x) ≤ (37974482491662327/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (35/64:ℝ) (141/256:ℝ)
    (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_140 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_141 :
    (72712233760839941/1000000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (141/256:ℝ) (71/128:ℝ)
    (1701850980515/3078915887616:ℝ) (1993841183/10000000000000:ℝ) (904402682722187/15625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_141
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0849).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^4*thetaFirstMode x) ≤ (36357147085827113/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (141/256:ℝ) (71/128:ℝ)
    (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (904402682722187/15625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_141 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_142 :
    (34780584176169537/500000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (71/128:ℝ) (143/256:ℝ)
    (587614013175/1055626092032:ℝ) (2318062031/12500000000000:ℝ) (27373264861214221/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_142
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0855).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^4*thetaFirstMode x) ≤ (6956318262989679/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (71/128:ℝ) (143/256:ℝ)
    (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (27373264861214221/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_142 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_143 :
    (66494726098655469/1000000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (143/256:ℝ) (9/16:ℝ)
    (1825569347035/3256712111616:ℝ) (17237965109/100000000000000:ℝ) (25875044056449187/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_143
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0861).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^4*thetaFirstMode x) ≤ (66496693782579713/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (143/256:ℝ) (9/16:ℝ)
    (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ) (25875044056449187/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_143 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_144 :
    (63513740114369399/1000000000000000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (9/16:ℝ) (145/256:ℝ)
    (1890069711845/3348443751936:ℝ) (64056239/400000000000:ℝ) (9777624868232171/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_144
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0867).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^4*thetaFirstMode x) ≤ (12703132162694581/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (9/16:ℝ) (145/256:ℝ)
    (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ) (9777624868232171/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_144 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_145 :
    (60618821147280419/1000000000000000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (145/256:ℝ) (73/128:ℝ)
    (652126819785/1147366579712:ℝ) (185852921/1250000000000:ℝ) (23078176624776193/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_145
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0873).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^4*thetaFirstMode x) ≤ (60620694556244529/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (145/256:ℝ) (73/128:ℝ)
    (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_145 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_146 :
    (5781036588516411/100000000000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (73/128:ℝ) (147/256:ℝ)
    (2024539435165/3537706799616:ℝ) (13796145899/100000000000000:ℝ) (21775266004453039/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_146
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0879).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^4*thetaFirstMode x) ≤ (28906095882820451/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (73/128:ℝ) (147/256:ℝ)
    (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_146 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_147 :
    (27544282772358991/500000000000000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (147/256:ℝ) (37/64:ℝ)
    (2094585008675/3635291844096:ℝ) (2558730853/20000000000000:ℝ) (20533232419187341/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_147
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0885).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^4*thetaFirstMode x) ≤ (27545171865640147/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (147/256:ℝ) (37/64:ℝ)
    (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ) (20533232419187341/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_147 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_148 :
    (6556676847420813/125000000000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (37/64:ℝ) (149/256:ℝ)
    (722185358895/1244960655872:ℝ) (5928404469/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_148
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0891).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^4*thetaFirstMode x) ≤ (52455145183996323/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (37/64:ℝ) (149/256:ℝ)
    (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_148 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_149 :
    (49904720837694363/1000000000000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (149/256:ℝ) (75/128:ℝ)
    (2240492066995/3836504449536:ℝ) (5490922951/50000000000000:ℝ) (1822353562406607/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_149
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0897).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^4*thetaFirstMode x) ≤ (6238300430691911/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (149/256:ℝ) (75/128:ℝ)
    (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (1822353562406607/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_149 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_150 :
    (47442112915596731/1000000000000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (75/128:ℝ) (151/256:ℝ)
    (2316432942005/3940186753536:ℝ) (10165180569/100000000000000:ℝ) (17151813610223543/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_150
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0903).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^4*thetaFirstMode x) ≤ (2372187388771351/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (75/128:ℝ) (151/256:ℝ)
    (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ) (17151813610223543/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_150 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_151 :
    (45065051650402727/1000000000000000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (151/256:ℝ) (19/32:ℝ)
    (798139734105/1348652175872:ℝ) (940340147/10000000000000:ℝ) (8066427405520841/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_151
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0909).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^4*thetaFirstMode x) ≤ (22533319437873941/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (151/256:ℝ) (19/32:ℝ)
    (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_151 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_152 :
    (10693209685392549/250000000000000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (19/32:ℝ) (153/256:ℝ)
    (2474491890325/4153841604096:ℝ) (1738652809/20000000000000:ℝ) (30329419364521959/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_152
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0915).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^4*thetaFirstMode x) ≤ (42774378514704599/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (19/32:ℝ) (153/256:ℝ)
    (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30329419364521959/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_152 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_153 :
    (40564626641638619/1000000000000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (153/256:ℝ) (77/128:ℝ)
    (2556692593835/4263869999616:ℝ) (4015842267/50000000000000:ℝ) (5698185426869039/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_153
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0921).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^4*thetaFirstMode x) ≤ (5070764901964713/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (153/256:ℝ) (77/128:ℝ)
    (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_153 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_154 :
    (38439428292465353/1000000000000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (77/128:ℝ) (155/256:ℝ)
    (880354483215/1458689971712:ℝ) (7415733977/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_154
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0927).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^4*thetaFirstMode x) ≤ (19220436984233183/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (77/128:ℝ) (155/256:ℝ)
    (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_154 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_155 :
    (4549515849792031/125000000000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (155/256:ℝ) (39/64:ℝ)
    (2727647147155/4490469735936:ℝ) (3421316157/50000000000000:ℝ) (2509238535479287/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_155
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0933).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^4*thetaFirstMode x) ≤ (18198762973602139/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (155/256:ℝ) (39/64:ℝ)
    (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_155 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_156 :
    (8608371286444749/250000000000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (39/64:ℝ) (157/256:ℝ)
    (2816486931965/4607098031616:ℝ) (3154871309/50000000000000:ℝ) (941002024403311/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_156
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0939).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^4*thetaFirstMode x) ≤ (17217419092554589/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (39/64:ℝ) (157/256:ℝ)
    (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ) (941002024403311/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_156 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_157 :
    (32550155746198909/1000000000000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (157/256:ℝ) (79/128:ℝ)
    (969208869825/1575327852032:ℝ) (1453641357/25000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_157
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0945).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^4*thetaFirstMode x) ≤ (16275731576801133/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (157/256:ℝ) (79/128:ℝ)
    (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_157 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_158 :
    (30744689936766883/1000000000000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (79/128:ℝ) (159/256:ℝ)
    (3001110548485/4847155247616:ℝ) (2677366609/50000000000000:ℝ) (10318317444428261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_158
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0951).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^4*thetaFirstMode x) ≤ (30745952243114833/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (79/128:ℝ) (159/256:ℝ)
    (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ) (10318317444428261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_158 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_159 :
    (29015547321603959/1000000000000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (159/256:ℝ) (5/8:ℝ)
    (3096983684795/4970642228736:ℝ) (1232001247/25000000000000:ℝ) (9654376044293469/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_159
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0957).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^4*thetaFirstMode x) ≤ (14508382550607089/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (159/256:ℝ) (5/8:ℝ)
    (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ) (9654376044293469/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_159 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

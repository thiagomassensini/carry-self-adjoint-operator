import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature5

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_160 :
    (∫ x in (5/8:ℝ)..(161/256:ℝ), x^10*thetaFirstMode x) ≤ (415378273199937/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/8:ℝ) (161/256:ℝ)
    (147725897/3125000000000:ℝ) (4346152043/100000000000000:ℝ) (4513506200394323/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_160 (thetaFirstMode_refined_node_0960).2 (thetaFirstMode_refined_node_0966).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_161 :
    (∫ x in (161/256:ℝ)..(81/128:ℝ), x^10*thetaFirstMode x) ≤ (162491968334773/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (161/256:ℝ) (81/128:ℝ)
    (4346152043/100000000000000:ℝ) (3993100837/100000000000000:ℝ) (16869263981906327/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_161 (thetaFirstMode_refined_node_0966).2 (thetaFirstMode_refined_node_0972).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_162 :
    (∫ x in (81/128:ℝ)..(163/256:ℝ), x^10*thetaFirstMode x) ≤ (1587447889551751/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (81/128:ℝ) (163/256:ℝ)
    (3993100837/100000000000000:ℝ) (3666235877/100000000000000:ℝ) (15751367210440041/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_162 (thetaFirstMode_refined_node_0972).2 (thetaFirstMode_refined_node_0978).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_163 :
    (∫ x in (163/256:ℝ)..(41/64:ℝ), x^10*thetaFirstMode x) ≤ (1549195546072201/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (163/256:ℝ) (41/64:ℝ)
    (3666235877/100000000000000:ℝ) (672764353/20000000000000:ℝ) (14697319411579383/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_163 (thetaFirstMode_refined_node_0978).2 (thetaFirstMode_refined_node_0984).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_164 :
    (∫ x in (41/64:ℝ)..(165/256:ℝ), x^10*thetaFirstMode x) ≤ (94391281876877/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (41/64:ℝ) (165/256:ℝ)
    (672764353/20000000000000:ℝ) (3084222233/100000000000000:ℝ) (6852096667522953/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_164 (thetaFirstMode_refined_node_0984).2 (thetaFirstMode_refined_node_0990).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_165 :
    (∫ x in (165/256:ℝ)..(83/128:ℝ), x^10*thetaFirstMode x) ≤ (735370137852499/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (165/256:ℝ) (83/128:ℝ)
    (3084222233/100000000000000:ℝ) (2825895597/100000000000000:ℝ) (1276914985091137/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_165 (thetaFirstMode_refined_node_0990).2 (thetaFirstMode_refined_node_0996).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_166 :
    (∫ x in (83/128:ℝ)..(167/256:ℝ), x^10*thetaFirstMode x) ≤ (1430731599488343/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (83/128:ℝ) (167/256:ℝ)
    (2825895597/100000000000000:ℝ) (1293695173/50000000000000:ℝ) (5944719025535047/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_166 (thetaFirstMode_refined_node_0996).2 (thetaFirstMode_refined_node_1002).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_167 :
    (∫ x in (167/256:ℝ)..(21/32:ℝ), x^10*thetaFirstMode x) ≤ (695165069335679/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (167/256:ℝ) (21/32:ℝ)
    (1293695173/50000000000000:ℝ) (1183670437/50000000000000:ℝ) (5531197575076283/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_167 (thetaFirstMode_refined_node_1002).2 (thetaFirstMode_refined_node_1008).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_168 :
    (∫ x in (21/32:ℝ)..(169/256:ℝ), x^10*thetaFirstMode x) ≤ (674815051890883/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (21/32:ℝ) (169/256:ℝ)
    (1183670437/50000000000000:ℝ) (2164463339/100000000000000:ℝ) (10285446230792657/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_168 (thetaFirstMode_refined_node_1008).2 (thetaFirstMode_refined_node_1014).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_169 :
    (∫ x in (169/256:ℝ)..(85/128:ℝ), x^10*thetaFirstMode x) ≤ (20448811371223/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (169/256:ℝ) (85/128:ℝ)
    (2164463339/100000000000000:ℝ) (1977551671/100000000000000:ℝ) (9556103793799823/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_169 (thetaFirstMode_refined_node_1014).2 (thetaFirstMode_refined_node_1020).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_170 :
    (∫ x in (85/128:ℝ)..(171/256:ℝ), x^10*thetaFirstMode x) ≤ (633850976806763/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (85/128:ℝ) (171/256:ℝ)
    (1977551671/100000000000000:ℝ) (902736853/50000000000000:ℝ) (2217991790435067/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_170 (thetaFirstMode_refined_node_1020).2 (thetaFirstMode_refined_node_1026).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_171 :
    (∫ x in (171/256:ℝ)..(43/64:ℝ), x^10*thetaFirstMode x) ≤ (613326069150177/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (171/256:ℝ) (43/64:ℝ)
    (902736853/50000000000000:ℝ) (51473983/3125000000000:ℝ) (65845773848071/8000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_171 (thetaFirstMode_refined_node_1026).2 (thetaFirstMode_refined_node_1032).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_172 :
    (∫ x in (43/64:ℝ)..(173/256:ℝ), x^10*thetaFirstMode x) ≤ (148207472390897/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (43/64:ℝ) (173/256:ℝ)
    (51473983/3125000000000:ℝ) (18770469/1250000000000:ℝ) (7630138077098641/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_172 (thetaFirstMode_refined_node_1032).2 (thetaFirstMode_refined_node_1038).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_173 :
    (∫ x in (173/256:ℝ)..(87/128:ℝ), x^10*thetaFirstMode x) ≤ (1144807262248763/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (173/256:ℝ) (87/128:ℝ)
    (18770469/1250000000000:ℝ) (683975811/50000000000000:ℝ) (7068070913210319/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_173 (thetaFirstMode_refined_node_1038).2 (thetaFirstMode_refined_node_1044).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_174 :
    (∫ x in (87/128:ℝ)..(175/256:ℝ), x^10*thetaFirstMode x) ≤ (1104173828954717/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (87/128:ℝ) (175/256:ℝ)
    (683975811/50000000000000:ℝ) (622618637/50000000000000:ℝ) (1308491592392887/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_174 (thetaFirstMode_refined_node_1044).2 (thetaFirstMode_refined_node_1050).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_175 :
    (∫ x in (175/256:ℝ)..(11/16:ℝ), x^10*thetaFirstMode x) ≤ (1063835367379603/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (175/256:ℝ) (11/16:ℝ)
    (622618637/50000000000000:ℝ) (566339291/50000000000000:ℝ) (6051318664087119/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_175 (thetaFirstMode_refined_node_1050).2 (thetaFirstMode_refined_node_1056).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_176 :
    (∫ x in (11/16:ℝ)..(177/256:ℝ), x^10*thetaFirstMode x) ≤ (1023864226911549/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/16:ℝ) (177/256:ℝ)
    (566339291/50000000000000:ℝ) (257378291/25000000000000:ℝ) (1118550559120073/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_176 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_177 :
    (∫ x in (177/256:ℝ)..(89/128:ℝ), x^10*thetaFirstMode x) ≤ (492164527640623/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (177/256:ℝ) (89/128:ℝ)
    (257378291/25000000000000:ℝ) (467514603/50000000000000:ℝ) (516493902482609/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_177 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_178 :
    (∫ x in (89/128:ℝ)..(179/256:ℝ), x^10*thetaFirstMode x) ≤ (472647330161587/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (89/128:ℝ) (179/256:ℝ)
    (467514603/50000000000000:ℝ) (84856263/10000000000000:ℝ) (4766133302660349/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_178 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_179 :
    (∫ x in (179/256:ℝ)..(45/64:ℝ), x^10*thetaFirstMode x) ≤ (906821892470571/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (179/256:ℝ) (45/64:ℝ)
    (84856263/10000000000000:ℝ) (769494387/100000000000000:ℝ) (2197333628875833/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_179 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_180 :
    (∫ x in (45/64:ℝ)..(181/256:ℝ), x^10*thetaFirstMode x) ≤ (868967553706153/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (45/64:ℝ) (181/256:ℝ)
    (769494387/100000000000000:ℝ) (697247869/100000000000000:ℝ) (1012236611442963/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_180 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_181 :
    (∫ x in (181/256:ℝ)..(91/128:ℝ), x^10*thetaFirstMode x) ≤ (103973040909401/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (181/256:ℝ) (91/128:ℝ)
    (697247869/100000000000000:ℝ) (63128643/10000000000000:ℝ) (465931073813781/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_181 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_182 :
    (∫ x in (91/128:ℝ)..(183/256:ℝ), x^10*thetaFirstMode x) ≤ (15906414636229/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (91/128:ℝ) (183/256:ℝ)
    (63128643/10000000000000:ℝ) (142777757/25000000000000:ℝ) (857180429569033/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_182 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_183 :
    (∫ x in (183/256:ℝ)..(23/32:ℝ), x^10*thetaFirstMode x) ≤ (189905273848433/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (183/256:ℝ) (23/32:ℝ)
    (142777757/25000000000000:ℝ) (129064491/25000000000000:ℝ) (3151382306242499/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_183 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_184 :
    (∫ x in (23/32:ℝ)..(185/256:ℝ), x^10*thetaFirstMode x) ≤ (90590693980319/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (23/32:ℝ) (185/256:ℝ)
    (129064491/25000000000000:ℝ) (466296741/100000000000000:ℝ) (2894113319235649/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_184 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_185 :
    (∫ x in (185/256:ℝ)..(93/128:ℝ), x^10*thetaFirstMode x) ≤ (345335030008271/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (185/256:ℝ) (93/128:ℝ)
    (466296741/100000000000000:ℝ) (26301751/6250000000000:ℝ) (2655662276511767/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_185 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_186 :
    (∫ x in (93/128:ℝ)..(187/256:ℝ), x^10*thetaFirstMode x) ≤ (657486436628843/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (93/128:ℝ) (187/256:ℝ)
    (26301751/6250000000000:ℝ) (189740827/50000000000000:ℝ) (1217419628144391/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_186 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_187 :
    (∫ x in (187/256:ℝ)..(47/64:ℝ), x^10*thetaFirstMode x) ≤ (625202413875261/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (187/256:ℝ) (47/64:ℝ)
    (189740827/50000000000000:ℝ) (170957443/50000000000000:ℝ) (278814361538547/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_187 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_188 :
    (∫ x in (47/64:ℝ)..(189/256:ℝ), x^10*thetaFirstMode x) ≤ (296920855771317/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (47/64:ℝ) (189/256:ℝ)
    (170957443/50000000000000:ℝ) (6156211/2000000000000:ℝ) (1020809179017363/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_188 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_189 :
    (∫ x in (189/256:ℝ)..(95/128:ℝ), x^10*thetaFirstMode x) ≤ (563424125553431/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (189/256:ℝ) (95/128:ℝ)
    (6156211/2000000000000:ℝ) (138437717/50000000000000:ℝ) (933567662673261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_189 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_190 :
    (∫ x in (95/128:ℝ)..(191/256:ℝ), x^10*thetaFirstMode x) ≤ (266982816859303/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (95/128:ℝ) (191/256:ℝ)
    (138437717/50000000000000:ℝ) (124419349/50000000000000:ℝ) (85305298899/50000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_190 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_191 :
    (∫ x in (191/256:ℝ)..(3/4:ℝ), x^10*thetaFirstMode x) ≤ (126369627849421/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (191/256:ℝ) (3/4:ℝ)
    (124419349/50000000000000:ℝ) (44690077/20000000000000:ℝ) (778811480076807/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_191 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature4

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^10*thetaFirstMode x) ≤ (192811524697007/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/2:ℝ) (129/256:ℝ)
    (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ) (56635078811378937/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_128 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^10*thetaFirstMode x) ≤ (1951845099741599/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (129/256:ℝ) (65/128:ℝ)
    (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_129 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^10*thetaFirstMode x) ≤ (123353013329379/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (65/128:ℝ) (131/256:ℝ)
    (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_130 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^10*thetaFirstMode x) ≤ (1993463724966571/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (131/256:ℝ) (33/64:ℝ)
    (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ) (12229335208502793/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_131 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^10*thetaFirstMode x) ≤ (3217978652769/1600000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (33/64:ℝ) (133/256:ℝ)
    (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ) (46534764213673919/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_132 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^10*thetaFirstMode x) ≤ (1013459081261959/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (133/256:ℝ) (67/128:ℝ)
    (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_133 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^10*thetaFirstMode x) ≤ (8161862910557/4000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (67/128:ℝ) (135/256:ℝ)
    (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (21020821257204279/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_134 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^10*thetaFirstMode x) ≤ (1025921681142403/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (135/256:ℝ) (17/32:ℝ)
    (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ) (2495419722748173/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_135 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^10*thetaFirstMode x) ≤ (2061021744760759/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (17/32:ℝ) (137/256:ℝ)
    (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ) (2368537855823959/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_136 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^10*thetaFirstMode x) ≤ (206797833936899/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (137/256:ℝ) (69/128:ℝ)
    (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ) (35949100893156969/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_137 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^10*thetaFirstMode x) ≤ (518174370010009/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (69/128:ℝ) (139/256:ℝ)
    (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ) (68163974002885677/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_138 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^10*thetaFirstMode x) ≤ (518792605122327/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (139/256:ℝ) (35/64:ℝ)
    (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ) (6458610204731741/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_139 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^10*thetaFirstMode x) ≤ (1037697675271773/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (35/64:ℝ) (141/256:ℝ)
    (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_140 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^10*thetaFirstMode x) ≤ (2073377378691393/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (141/256:ℝ) (71/128:ℝ)
    (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (904402682722187/15625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_141 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^10*thetaFirstMode x) ≤ (41382569630019/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (71/128:ℝ) (143/256:ℝ)
    (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (27373264861214221/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_142 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^10*thetaFirstMode x) ≤ (41253348397129/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (143/256:ℝ) (9/16:ℝ)
    (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ) (25875044056449187/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_143 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^10*thetaFirstMode x) ≤ (205401962297553/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (9/16:ℝ) (145/256:ℝ)
    (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ) (9777624868232171/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_144 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^10*thetaFirstMode x) ≤ (1021608520557393/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (145/256:ℝ) (73/128:ℝ)
    (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_145 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^10*thetaFirstMode x) ≤ (1015148983896541/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (73/128:ℝ) (147/256:ℝ)
    (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_146 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^10*thetaFirstMode x) ≤ (12595667706663/6250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (147/256:ℝ) (37/64:ℝ)
    (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ) (20533232419187341/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_147 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^10*thetaFirstMode x) ≤ (1998293969226103/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (37/64:ℝ) (149/256:ℝ)
    (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_148 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^10*thetaFirstMode x) ≤ (989657675198027/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (149/256:ℝ) (75/128:ℝ)
    (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (1822353562406607/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_149 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^10*thetaFirstMode x) ≤ (1958432307729737/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (75/128:ℝ) (151/256:ℝ)
    (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ) (17151813610223543/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_150 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^10*thetaFirstMode x) ≤ (1935711222258173/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (151/256:ℝ) (19/32:ℝ)
    (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_151 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^10*thetaFirstMode x) ≤ (1911223197606561/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (19/32:ℝ) (153/256:ℝ)
    (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30329419364521959/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_152 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^10*thetaFirstMode x) ≤ (377008742838537/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (153/256:ℝ) (77/128:ℝ)
    (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_153 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^10*thetaFirstMode x) ≤ (928626133452523/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (77/128:ℝ) (155/256:ℝ)
    (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_154 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^10*thetaFirstMode x) ≤ (1827931989578731/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (155/256:ℝ) (39/64:ℝ)
    (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_155 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^10*thetaFirstMode x) ≤ (449292317010861/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (39/64:ℝ) (157/256:ℝ)
    (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ) (941002024403311/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_156 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^10*thetaFirstMode x) ≤ (27578958487827/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (157/256:ℝ) (79/128:ℝ)
    (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_157 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^10*thetaFirstMode x) ≤ (865837954060067/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (79/128:ℝ) (159/256:ℝ)
    (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ) (10318317444428261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_158 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^10*thetaFirstMode x) ≤ (1697130700488607/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (159/256:ℝ) (5/8:ℝ)
    (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ) (9654376044293469/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_159 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

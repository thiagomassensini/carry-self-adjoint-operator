import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature4

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_128 :
    (1899225635377969041/1000000000000000000000000:ℝ) ≤ ∫ x in (1/2:ℝ)..(129/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/2:ℝ) (129/256:ℝ)
    (257/512:ℝ) (48612974743/100000000000000:ℝ) (56635078811378937/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_128
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0769).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_128 :
    (∫ x in (1/2:ℝ)..(129/256:ℝ), x^0*thetaFirstMode x) ≤ (949633179094687209/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/2:ℝ) (129/256:ℝ)
    (50216326329/100000000000000:ℝ) (47054917301/100000000000000:ℝ) (56635078811378937/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_128 (thetaFirstMode_refined_node_0768).2 (thetaFirstMode_refined_node_0774).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_129 :
    (1779196379245044549/1000000000000000000000000:ℝ) ≤ ∫ x in (129/256:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (129/256:ℝ) (65/128:ℝ)
    (259/512:ℝ) (22770282629/50000000000000:ℝ) (21586144939916833/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_129
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0775).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_129 :
    (∫ x in (129/256:ℝ)..(65/128:ℝ), x^0*thetaFirstMode x) ≤ (1779235352291160901/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (129/256:ℝ) (65/128:ℝ)
    (47054917301/100000000000000:ℝ) (44069380939/100000000000000:ℝ) (21586144939916833/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_129 (thetaFirstMode_refined_node_0774).2 (thetaFirstMode_refined_node_0780).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_130 :
    (1665874161223071983/1000000000000000000000000:ℝ) ≤ ∫ x in (65/128:ℝ)..(131/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (65/128:ℝ) (131/256:ℝ)
    (261/512:ℝ) (42639843507/100000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_130
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0781).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_130 :
    (∫ x in (65/128:ℝ)..(131/256:ℝ), x^0*thetaFirstMode x) ≤ (832955720437084267/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (65/128:ℝ) (131/256:ℝ)
    (44069380939/100000000000000:ℝ) (8250284983/20000000000000:ℝ) (102786981858788307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_130 (thetaFirstMode_refined_node_0780).2 (thetaFirstMode_refined_node_0786).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_131 :
    (311788204582375299/200000000000000000000000:ℝ) ≤ ∫ x in (131/256:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (131/256:ℝ) (33/64:ℝ)
    (263/512:ℝ) (1596106801/4000000000000:ℝ) (12229335208502793/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_131
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0787).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_131 :
    (∫ x in (131/256:ℝ)..(33/64:ℝ), x^0*thetaFirstMode x) ≤ (1558976664703590759/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (131/256:ℝ) (33/64:ℝ)
    (8250284983/20000000000000:ℝ) (9648265241/25000000000000:ℝ) (12229335208502793/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_131 (thetaFirstMode_refined_node_0786).2 (thetaFirstMode_refined_node_0792).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_132 :
    (729045377348829691/500000000000000000000000:ℝ) ≤ ∫ x in (33/64:ℝ)..(133/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (33/64:ℝ) (133/256:ℝ)
    (265/512:ℝ) (37321206119/100000000000000:ℝ) (46534764213673919/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_132
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0793).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_132 :
    (∫ x in (33/64:ℝ)..(133/256:ℝ), x^0*thetaFirstMode x) ≤ (291624962624842497/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/64:ℝ) (133/256:ℝ)
    (9648265241/25000000000000:ℝ) (36086598273/100000000000000:ℝ) (46534764213673919/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_132 (thetaFirstMode_refined_node_0792).2 (thetaFirstMode_refined_node_0798).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_133 :
    (1363028635772257211/1000000000000000000000000:ℝ) ≤ ∫ x in (133/256:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (133/256:ℝ) (67/128:ℝ)
    (267/512:ℝ) (8721976803/25000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_133
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0799).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_133 :
    (∫ x in (133/256:ℝ)..(67/128:ℝ), x^0*thetaFirstMode x) ≤ (1363061164353923077/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (133/256:ℝ) (67/128:ℝ)
    (36086598273/100000000000000:ℝ) (33724636797/100000000000000:ℝ) (88487185923985229/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_133 (thetaFirstMode_refined_node_0798).2 (thetaFirstMode_refined_node_0804).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_134 :
    (15918389647114943/12500000000000000000000:ℝ) ≤ ∫ x in (67/128:ℝ)..(135/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (67/128:ℝ) (135/256:ℝ)
    (269/512:ℝ) (16297758063/50000000000000:ℝ) (21020821257204279/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_134
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0805).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_134 :
    (∫ x in (67/128:ℝ)..(135/256:ℝ), x^0*thetaFirstMode x) ≤ (127350222308270287/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (67/128:ℝ) (135/256:ℝ)
    (33724636797/100000000000000:ℝ) (3150006051/10000000000000:ℝ) (21020821257204279/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_134 (thetaFirstMode_refined_node_0804).2 (thetaFirstMode_refined_node_0810).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_135 :
    (594572915203572439/500000000000000000000000:ℝ) ≤ ∫ x in (135/256:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (135/256:ℝ) (17/32:ℝ)
    (271/512:ℝ) (15218528157/50000000000000:ℝ) (2495419722748173/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_135
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0811).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_135 :
    (∫ x in (135/256:ℝ)..(17/32:ℝ), x^0*thetaFirstMode x) ≤ (297293863976115061/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (135/256:ℝ) (17/32:ℝ)
    (3150006051/10000000000000:ℝ) (2940603061/10000000000000:ℝ) (2495419722748173/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_135 (thetaFirstMode_refined_node_0810).2 (thetaFirstMode_refined_node_0816).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_136 :
    (1109790774867336269/1000000000000000000000000:ℝ) ≤ ∫ x in (17/32:ℝ)..(137/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (17/32:ℝ) (137/256:ℝ)
    (273/512:ℝ) (14202912517/50000000000000:ℝ) (2368537855823959/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_136
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0817).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_136 :
    (∫ x in (17/32:ℝ)..(137/256:ℝ), x^0*thetaFirstMode x) ≤ (1109819025050483711/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/32:ℝ) (137/256:ℝ)
    (2940603061/10000000000000:ℝ) (27435978683/100000000000000:ℝ) (2368537855823959/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_136 (thetaFirstMode_refined_node_0816).2 (thetaFirstMode_refined_node_0822).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_137 :
    (64697162271881413/62500000000000000000000:ℝ) ≤ ∫ x in (137/256:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (137/256:ℝ) (69/128:ℝ)
    (275/512:ℝ) (13247693251/50000000000000:ℝ) (35949100893156969/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_137
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0823).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_137 :
    (∫ x in (137/256:ℝ)..(69/128:ℝ), x^0*thetaFirstMode x) ≤ (258795380174558071/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (137/256:ℝ) (69/128:ℝ)
    (27435978683/100000000000000:ℝ) (5116719967/20000000000000:ℝ) (35949100893156969/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_137 (thetaFirstMode_refined_node_0822).2 (thetaFirstMode_refined_node_0828).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_138 :
    (753903160667543/781250000000000000000:ℝ) ≤ ∫ x in (69/128:ℝ)..(139/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (69/128:ℝ) (139/256:ℝ)
    (277/512:ℝ) (1234978251/5000000000000:ℝ) (68163974002885677/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_138
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0829).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_138 :
    (∫ x in (69/128:ℝ)..(139/256:ℝ), x^0*thetaFirstMode x) ≤ (96502169249968367/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (69/128:ℝ) (139/256:ℝ)
    (5116719967/20000000000000:ℝ) (2980355727/12500000000000:ℝ) (68163974002885677/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_138 (thetaFirstMode_refined_node_0828).2 (thetaFirstMode_refined_node_0834).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_139 :
    (899083763975831561/1000000000000000000000000:ℝ) ≤ ∫ x in (139/256:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (139/256:ℝ) (35/64:ℝ)
    (279/512:ℝ) (5753109521/25000000000000:ℝ) (6458610204731741/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_139
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0835).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_139 :
    (∫ x in (139/256:ℝ)..(35/64:ℝ), x^0*thetaFirstMode x) ≤ (899108180700680627/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (139/256:ℝ) (35/64:ℝ)
    (2980355727/12500000000000:ℝ) (22207918131/100000000000000:ℝ) (6458610204731741/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_139 (thetaFirstMode_refined_node_0834).2 (thetaFirstMode_refined_node_0840).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_140 :
    (83719601432831909/100000000000000000000000:ℝ) ≤ ∫ x in (35/64:ℝ)..(141/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (35/64:ℝ) (141/256:ℝ)
    (281/512:ℝ) (5357082377/25000000000000:ℝ) (30580084349091647/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_140
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0841).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_140 :
    (∫ x in (35/64:ℝ)..(141/256:ℝ), x^0*thetaFirstMode x) ≤ (837219247163674319/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/64:ℝ) (141/256:ℝ)
    (22207918131/100000000000000:ℝ) (20673261159/100000000000000:ℝ) (30580084349091647/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_140 (thetaFirstMode_refined_node_0840).2 (thetaFirstMode_refined_node_0846).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_141 :
    (77912041261472101/100000000000000000000000:ℝ) ≤ ∫ x in (141/256:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (141/256:ℝ) (71/128:ℝ)
    (283/512:ℝ) (19941802539/100000000000000:ℝ) (904402682722187/15625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_141
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0847).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_141 :
    (∫ x in (141/256:ℝ)..(71/128:ℝ), x^0*thetaFirstMode x) ≤ (38957125336184149/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (141/256:ℝ) (71/128:ℝ)
    (20673261159/100000000000000:ℝ) (19233555281/100000000000000:ℝ) (904402682722187/15625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_141 (thetaFirstMode_refined_node_0846).2 (thetaFirstMode_refined_node_0852).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_142 :
    (724653659946116279/1000000000000000000000000:ℝ) ≤ ∫ x in (71/128:ℝ)..(143/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (71/128:ℝ) (143/256:ℝ)
    (285/512:ℝ) (4636913251/25000000000000:ℝ) (27373264861214221/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_142
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0853).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_142 :
    (∫ x in (71/128:ℝ)..(143/256:ℝ), x^0*thetaFirstMode x) ≤ (724674659404642441/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (71/128:ℝ) (143/256:ℝ)
    (19233555281/100000000000000:ℝ) (17883710043/100000000000000:ℝ) (27373264861214221/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_142 (thetaFirstMode_refined_node_0852).2 (thetaFirstMode_refined_node_0858).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_143 :
    (336800637929563843/500000000000000000000000:ℝ) ≤ ∫ x in (143/256:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (143/256:ℝ) (9/16:ℝ)
    (287/512:ℝ) (215511281/1250000000000:ℝ) (25875044056449187/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_143
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0859).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_143 :
    (∫ x in (143/256:ℝ)..(9/16:ℝ), x^0*thetaFirstMode x) ≤ (336810611826419189/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (143/256:ℝ) (9/16:ℝ)
    (17883710043/100000000000000:ℝ) (2077357167/12500000000000:ℝ) (25875044056449187/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_143 (thetaFirstMode_refined_node_0858).2 (thetaFirstMode_refined_node_0864).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_144 :
    (156444333254271771/250000000000000000000000:ℝ) ≤ ∫ x in (9/16:ℝ)..(145/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (9/16:ℝ) (145/256:ℝ)
    (289/512:ℝ) (8008395751/50000000000000:ℝ) (9777624868232171/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_144
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0865).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_144 :
    (∫ x in (9/16:ℝ)..(145/256:ℝ), x^0*thetaFirstMode x) ≤ (312898135527834791/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/16:ℝ) (145/256:ℝ)
    (2077357167/12500000000000:ℝ) (3086868927/20000000000000:ℝ) (9777624868232171/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_144 (thetaFirstMode_refined_node_0864).2 (thetaFirstMode_refined_node_0870).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_145 :
    (72625524223187849/125000000000000000000000:ℝ) ≤ ∫ x in (145/256:ℝ)..(73/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (145/256:ℝ) (73/128:ℝ)
    (291/512:ℝ) (14870772819/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_145
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0871).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_145 :
    (∫ x in (145/256:ℝ)..(73/128:ℝ), x^0*thetaFirstMode x) ≤ (18156942590554513/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (145/256:ℝ) (73/128:ℝ)
    (3086868927/20000000000000:ℝ) (14325728273/100000000000000:ℝ) (23078176624776193/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_145 (thetaFirstMode_refined_node_0870).2 (thetaFirstMode_refined_node_0876).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_146 :
    (67389031104766511/125000000000000000000000:ℝ) ≤ ∫ x in (73/128:ℝ)..(147/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (73/128:ℝ) (147/256:ℝ)
    (293/512:ℝ) (6899252351/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_146
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0877).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_146 :
    (∫ x in (73/128:ℝ)..(147/256:ℝ), x^0*thetaFirstMode x) ≤ (539129288788579573/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (73/128:ℝ) (147/256:ℝ)
    (14325728273/100000000000000:ℝ) (6644383393/50000000000000:ℝ) (21775266004453039/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_146 (thetaFirstMode_refined_node_0876).2 (thetaFirstMode_refined_node_0882).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_147 :
    (62492457302337877/125000000000000000000000:ℝ) ≤ ∫ x in (147/256:ℝ)..(37/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (147/256:ℝ) (37/64:ℝ)
    (295/512:ℝ) (79974027/625000000000:ℝ) (20533232419187341/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_147
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0883).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_147 :
    (∫ x in (147/256:ℝ)..(37/64:ℝ), x^0*thetaFirstMode x) ≤ (62494475971496121/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (147/256:ℝ) (37/64:ℝ)
    (6644383393/50000000000000:ℝ) (6159707157/50000000000000:ℝ) (20533232419187341/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_147 (thetaFirstMode_refined_node_0882).2 (thetaFirstMode_refined_node_0888).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_148 :
    (92666419165706001/200000000000000000000000:ℝ) ≤ ∫ x in (37/64:ℝ)..(149/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (37/64:ℝ) (149/256:ℝ)
    (297/512:ℝ) (11858841173/100000000000000:ℝ) (19350003728002473/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_148
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0889).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_148 :
    (∫ x in (37/64:ℝ)..(149/256:ℝ), x^0*thetaFirstMode x) ≤ (463347392171064989/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (37/64:ℝ) (149/256:ℝ)
    (6159707157/50000000000000:ℝ) (5706907043/50000000000000:ℝ) (19350003728002473/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_148 (thetaFirstMode_refined_node_0888).2 (thetaFirstMode_refined_node_0894).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_149 :
    (429142494624368677/1000000000000000000000000:ℝ) ≤ ∫ x in (149/256:ℝ)..(75/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (149/256:ℝ) (75/128:ℝ)
    (299/512:ℝ) (549186531/5000000000000:ℝ) (1822353562406607/50000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_149
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0895).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_149 :
    (∫ x in (149/256:ℝ)..(75/128:ℝ), x^0*thetaFirstMode x) ≤ (85831394884627529/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (149/256:ℝ) (75/128:ℝ)
    (5706907043/50000000000000:ℝ) (5284145987/50000000000000:ℝ) (1822353562406607/50000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_149 (thetaFirstMode_refined_node_0894).2 (thetaFirstMode_refined_node_0900).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_150 :
    (397230798471978423/1000000000000000000000000:ℝ) ≤ ∫ x in (75/128:ℝ)..(151/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (75/128:ℝ) (151/256:ℝ)
    (301/512:ℝ) (406677099/4000000000000:ℝ) (17151813610223543/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_150
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0901).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_150 :
    (∫ x in (75/128:ℝ)..(151/256:ℝ), x^0*thetaFirstMode x) ≤ (397244497157605653/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (75/128:ℝ) (151/256:ℝ)
    (5284145987/50000000000000:ℝ) (76401173/781250000000:ℝ) (17151813610223543/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_150 (thetaFirstMode_refined_node_0900).2 (thetaFirstMode_refined_node_0906).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_151 :
    (22966482184011589/62500000000000000000000:ℝ) ≤ ∫ x in (151/256:ℝ)..(19/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (151/256:ℝ) (19/32:ℝ)
    (303/512:ℝ) (1175627463/12500000000000:ℝ) (8066427405520841/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_151
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0907).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_151 :
    (∫ x in (151/256:ℝ)..(19/32:ℝ), x^0*thetaFirstMode x) ≤ (183738333405423951/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (151/256:ℝ) (19/32:ℝ)
    (76401173/781250000000:ℝ) (9043660791/100000000000000:ℝ) (8066427405520841/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_151 (thetaFirstMode_refined_node_0906).2 (thetaFirstMode_refined_node_0912).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_152 :
    (339714472716873591/1000000000000000000000000:ℝ) ≤ ∫ x in (19/32:ℝ)..(153/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (19/32:ℝ) (153/256:ℝ)
    (305/512:ℝ) (8694762209/100000000000000:ℝ) (30329419364521959/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_152
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0913).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_152 :
    (∫ x in (19/32:ℝ)..(153/256:ℝ), x^0*thetaFirstMode x) ≤ (42465838878887071/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/32:ℝ) (153/256:ℝ)
    (9043660791/100000000000000:ℝ) (522378749/6250000000000:ℝ) (30329419364521959/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_152 (thetaFirstMode_refined_node_0912).2 (thetaFirstMode_refined_node_0918).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_153 :
    (156931291491482587/500000000000000000000000:ℝ) ≤ ∫ x in (153/256:ℝ)..(77/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (153/256:ℝ) (77/128:ℝ)
    (307/512:ℝ) (12551673/156250000000:ℝ) (5698185426869039/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_153
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0919).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_153 :
    (∫ x in (153/256:ℝ)..(77/128:ℝ), x^0*thetaFirstMode x) ≤ (156937069995550451/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (153/256:ℝ) (77/128:ℝ)
    (522378749/6250000000000:ℝ) (7719541601/100000000000000:ℝ) (5698185426869039/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_153 (thetaFirstMode_refined_node_0918).2 (thetaFirstMode_refined_node_0924).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_154 :
    (5795872097784851/20000000000000000000000:ℝ) ≤ ∫ x in (77/128:ℝ)..(155/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (77/128:ℝ) (155/256:ℝ)
    (309/512:ℝ) (741701579/10000000000000:ℝ) (13373238132940231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_154
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0925).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_154 :
    (∫ x in (77/128:ℝ)..(155/256:ℝ), x^0*thetaFirstMode x) ≤ (289804511784014899/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (77/128:ℝ) (155/256:ℝ)
    (7719541601/100000000000000:ℝ) (7125251383/100000000000000:ℝ) (13373238132940231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_154 (thetaFirstMode_refined_node_0924).2 (thetaFirstMode_refined_node_0930).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_155 :
    (267398915386589151/1000000000000000000000000:ℝ) ≤ ∫ x in (155/256:ℝ)..(39/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (155/256:ℝ) (39/64:ℝ)
    (311/512:ℝ) (6843816903/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_155
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0931).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_155 :
    (∫ x in (155/256:ℝ)..(39/64:ℝ), x^0*thetaFirstMode x) ≤ (267409202273696697/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (155/256:ℝ) (39/64:ℝ)
    (7125251383/100000000000000:ℝ) (6572481097/100000000000000:ℝ) (2509238535479287/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_155 (thetaFirstMode_refined_node_0930).2 (thetaFirstMode_refined_node_0936).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_156 :
    (246575483376455711/1000000000000000000000000:ℝ) ≤ ∫ x in (39/64:ℝ)..(157/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (39/64:ℝ) (157/256:ℝ)
    (313/512:ℝ) (1577709173/25000000000000:ℝ) (941002024403311/40000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_156
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0937).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_156 :
    (∫ x in (39/64:ℝ)..(157/256:ℝ), x^0*thetaFirstMode x) ≤ (61646294859623707/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (39/64:ℝ) (157/256:ℝ)
    (6572481097/100000000000000:ℝ) (302933141/5000000000000:ℝ) (941002024403311/40000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_156 (thetaFirstMode_refined_node_0936).2 (thetaFirstMode_refined_node_0942).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_157 :
    (113612824447884883/500000000000000000000000:ℝ) ≤ ∫ x in (157/256:ℝ)..(79/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (157/256:ℝ) (79/128:ℝ)
    (315/512:ℝ) (2907787643/50000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_157
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0943).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_157 :
    (∫ x in (157/256:ℝ)..(79/128:ℝ), x^0*thetaFirstMode x) ≤ (28404347780940371/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (157/256:ℝ) (79/128:ℝ)
    (302933141/5000000000000:ℝ) (2790681667/50000000000000:ℝ) (22040947956740601/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_157 (thetaFirstMode_refined_node_0942).2 (thetaFirstMode_refined_node_0948).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_158 :
    (41851381319620081/200000000000000000000000:ℝ) ≤ ∫ x in (79/128:ℝ)..(159/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (79/128:ℝ) (159/256:ℝ)
    (317/512:ℝ) (5355664767/100000000000000:ℝ) (10318317444428261/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_158
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0949).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_158 :
    (∫ x in (79/128:ℝ)..(159/256:ℝ), x^0*thetaFirstMode x) ≤ (20926550442098669/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (79/128:ℝ) (159/256:ℝ)
    (2790681667/50000000000000:ℝ) (256913933/5000000000000:ℝ) (10318317444428261/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_158 (thetaFirstMode_refined_node_0948).2 (thetaFirstMode_refined_node_0954).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_159 :
    (12036355914054157/62500000000000000000000:ℝ) ≤ ∫ x in (159/256:ℝ)..(5/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (159/256:ℝ) (5/8:ℝ)
    (319/512:ℝ) (985772753/20000000000000:ℝ) (9654376044293469/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_159
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0955).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_159 :
    (∫ x in (159/256:ℝ)..(5/8:ℝ), x^0*thetaFirstMode x) ≤ (7703591323760679/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (159/256:ℝ) (5/8:ℝ)
    (256913933/5000000000000:ℝ) (147725897/3125000000000:ℝ) (9654376044293469/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_159 (thetaFirstMode_refined_node_0954).2 (thetaFirstMode_refined_node_0960).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator

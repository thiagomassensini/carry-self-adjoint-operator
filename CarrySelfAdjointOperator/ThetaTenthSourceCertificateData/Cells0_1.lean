import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature1

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_032 :
    (29016692549888329791/200000000000000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/8:ℝ) (33/256:ℝ)
    (65/512:ℝ) (3714040946007/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_032
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0193).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^0*thetaFirstMode x) ≤ (145083932830940920839/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/8:ℝ) (33/256:ℝ)
    (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_032 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_033 :
    (140822586227334164631/1000000000000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (33/256:ℝ) (17/128:ℝ)
    (67/512:ℝ) (360496344351/10000000000000:ℝ) (372626855380705201/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_033
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0199).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^0*thetaFirstMode x) ≤ (4400720330595691859/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/256:ℝ) (17/128:ℝ)
    (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ) (372626855380705201/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_033 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_034 :
    (136652800143829405167/1000000000000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (17/128:ℝ) (35/256:ℝ)
    (69/512:ℝ) (3498217875589/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_034
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0205).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^0*thetaFirstMode x) ≤ (27330651749323706683/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/128:ℝ) (35/256:ℝ)
    (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_034 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_035 :
    (3314329867312176533/25000000000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (35/256:ℝ) (9/64:ℝ)
    (71/512:ℝ) (3393780950527/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_035
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0211).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^0*thetaFirstMode x) ≤ (6628682376397778243/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/256:ℝ) (9/64:ℝ)
    (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_035 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_036 :
    (128582842056633698201/1000000000000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (9/64:ℝ) (37/256:ℝ)
    (73/512:ℝ) (658325783107/20000000000000:ℝ) (288907166448900491/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_036
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0217).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^0*thetaFirstMode x) ≤ (64291644554206145549/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/64:ℝ) (37/256:ℝ)
    (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_036 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_037 :
    (62340398529082975921/500000000000000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (37/256:ℝ) (19/128:ℝ)
    (75/512:ℝ) (1595868786681/50000000000000:ℝ) (89290827741626873/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_037
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0223).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^0*thetaFirstMode x) ≤ (24936247662186744263/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (37/256:ℝ) (19/128:ℝ)
    (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ) (89290827741626873/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_037 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_038 :
    (30216524452731059021/250000000000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (19/128:ℝ) (39/256:ℝ)
    (77/512:ℝ) (1547041149511/50000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_038
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0229).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^0*thetaFirstMode x) ≤ (120866533251432777831/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/128:ℝ) (39/256:ℝ)
    (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_038 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_039 :
    (117137766386290932251/1000000000000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (39/256:ℝ) (5/32:ℝ)
    (79/512:ℝ) (1499319028417/50000000000000:ℝ) (349028961673015303/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_039
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0235).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^0*thetaFirstMode x) ≤ (58569098001326255249/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (39/256:ℝ) (5/32:ℝ)
    (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_039 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_040 :
    (56747404742148989209/500000000000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (5/32:ℝ) (41/256:ℝ)
    (81/512:ℝ) (2905379417603/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_040
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0241).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^0*thetaFirstMode x) ≤ (113495233266482168163/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/32:ℝ) (41/256:ℝ)
    (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_040 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_041 :
    (54968109557190807229/500000000000000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (41/256:ℝ) (21/128:ℝ)
    (83/512:ℝ) (175892536003/6250000000000:ℝ) (272524735160506569/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_041
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0247).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^0*thetaFirstMode x) ≤ (109936637053092239833/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/256:ℝ) (21/128:ℝ)
    (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (272524735160506569/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_041 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_042 :
    (21292194655891131061/200000000000000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (21/128:ℝ) (43/256:ℝ)
    (85/512:ℝ) (545063073663/20000000000000:ℝ) (168193502212474447/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_042
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0253).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^0*thetaFirstMode x) ≤ (106461385367514470639/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/128:ℝ) (43/256:ℝ)
    (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_042 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_043 :
    (103068036669283846697/1000000000000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (43/256:ℝ) (11/64:ℝ)
    (87/512:ℝ) (2576618447/97656250000:ℝ) (664134004242976343/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_043
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0259).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^0*thetaFirstMode x) ≤ (20613688580239586321/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/256:ℝ) (11/64:ℝ)
    (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_043 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_044 :
    (6234772584840220739/62500000000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (11/64:ℝ) (45/256:ℝ)
    (89/512:ℝ) (319209939079/12500000000000:ℝ) (655397632509854761/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_044
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0265).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^0*thetaFirstMode x) ≤ (99756761729526998851/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/64:ℝ) (45/256:ℝ)
    (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_044 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_045 :
    (19304977500869000761/200000000000000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (45/256:ℝ) (23/128:ℝ)
    (91/512:ℝ) (2470954904391/100000000000000:ℝ) (10102667702120131/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_045
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0271).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^0*thetaFirstMode x) ≤ (4826264100705148057/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/256:ℝ) (23/128:ℝ)
    (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ) (10102667702120131/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_045 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_046 :
    (93372544062007555091/1000000000000000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (23/128:ℝ) (47/256:ℝ)
    (93/512:ℝ) (2390256045431/100000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_046
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0277).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^0*thetaFirstMode x) ≤ (2917904147156632299/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/128:ℝ) (47/256:ℝ)
    (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_046 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_047 :
    (90298249484382824407/1000000000000000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (47/256:ℝ) (3/16:ℝ)
    (95/512:ℝ) (92462209897/4000000000000:ℝ) (628668827175261319/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_047
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0283).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^0*thetaFirstMode x) ≤ (18059726453953901487/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/256:ℝ) (3/16:ℝ)
    (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ) (628668827175261319/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_047 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_048 :
    (43650456219620050157/500000000000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (3/16:ℝ) (49/256:ℝ)
    (97/512:ℝ) (1117412285759/50000000000000:ℝ) (247842240871482451/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_048
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0289).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^0*thetaFirstMode x) ≤ (87301289365699486871/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/16:ℝ) (49/256:ℝ)
    (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ) (247842240871482451/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_048 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_049 :
    (84379432522083081733/1000000000000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (49/256:ℝ) (25/128:ℝ)
    (99/512:ℝ) (540008961651/25000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_049
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0295).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^0*thetaFirstMode x) ≤ (42189901797077074517/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (49/256:ℝ) (25/128:ℝ)
    (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_049 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_050 :
    (81532700971472272127/1000000000000000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (25/128:ℝ) (51/256:ℝ)
    (101/512:ℝ) (2087160687639/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_050
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0301).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^0*thetaFirstMode x) ≤ (5095816637197557781/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/128:ℝ) (51/256:ℝ)
    (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_050 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_051 :
    (39379800692369366417/500000000000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (51/256:ℝ) (13/64:ℝ)
    (103/512:ℝ) (504042628491/25000000000000:ℝ) (592037690565412011/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_051
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0307).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^0*thetaFirstMode x) ≤ (78759960767885815581/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (51/256:ℝ) (13/64:ℝ)
    (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_051 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_052 :
    (15211802086755025097/200000000000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (13/64:ℝ) (53/256:ℝ)
    (105/512:ℝ) (194703656763/10000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_052
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0313).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^0*thetaFirstMode x) ≤ (237685512456202829/3125000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (13/64:ℝ) (53/256:ℝ)
    (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_052 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_053 :
    (73429798579421058651/1000000000000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (53/256:ℝ) (27/128:ℝ)
    (107/512:ℝ) (1879729931687/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_053
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0319).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^0*thetaFirstMode x) ≤ (36715073155950035099/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (53/256:ℝ) (27/128:ℝ)
    (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_053 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_054 :
    (7087083078467682353/100000000000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (27/128:ℝ) (55/256:ℝ)
    (109/512:ℝ) (1814221548443/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_054
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0325).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^0*thetaFirstMode x) ≤ (3543558635528411397/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (27/128:ℝ) (55/256:ℝ)
    (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_054 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_055 :
    (17095241806568985831/250000000000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (55/256:ℝ) (7/32:ℝ)
    (111/512:ℝ) (1750482237681/100000000000000:ℝ) (221847156154640409/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_055
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0331).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^0*thetaFirstMode x) ≤ (17095325840016325213/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (55/256:ℝ) (7/32:ℝ)
    (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (221847156154640409/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_055 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_056 :
    (6595906400161018137/100000000000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (7/32:ℝ) (57/256:ℝ)
    (113/512:ℝ) (1688482714757/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_056
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0337).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^0*thetaFirstMode x) ≤ (65959394359553074759/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/32:ℝ) (57/256:ℝ)
    (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_056 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_057 :
    (15900993458259251453/250000000000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (57/256:ℝ) (29/128:ℝ)
    (115/512:ℝ) (1628193608631/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_057
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0343).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^0*thetaFirstMode x) ≤ (7950537304182154797/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/256:ℝ) (29/128:ℝ)
    (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_057 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_058 :
    (61314546768672253183/1000000000000000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (29/128:ℝ) (59/256:ℝ)
    (117/512:ℝ) (12262386561/781250000000:ℝ) (8222818714789663/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_058
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0349).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^0*thetaFirstMode x) ≤ (61314865631210181133/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/128:ℝ) (59/256:ℝ)
    (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ) (8222818714789663/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_058 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_059 :
    (29544815438173446613/500000000000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (59/256:ℝ) (15/64:ℝ)
    (119/512:ℝ) (189078604763/12500000000000:ℝ) (516782794844143017/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_059
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0355).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^0*thetaFirstMode x) ≤ (29544972011201934899/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/256:ℝ) (15/64:ℝ)
    (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ) (516782794844143017/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_059 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_060 :
    (28464036466320850007/500000000000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (15/64:ℝ) (61/256:ℝ)
    (121/512:ℝ) (728647080143/50000000000000:ℝ) (31706377237718811/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_060
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0361).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^0*thetaFirstMode x) ≤ (7116047548172582809/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (15/64:ℝ) (61/256:ℝ)
    (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ) (31706377237718811/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_060 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_061 :
    (10965743821236260523/200000000000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (61/256:ℝ) (31/128:ℝ)
    (123/512:ℝ) (280710381513/20000000000000:ℝ) (497823671186989721/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_061
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0367).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^0*thetaFirstMode x) ≤ (54829020890371769769/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (61/256:ℝ) (31/128:ℝ)
    (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ) (497823671186989721/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_061 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_062 :
    (26395207816362468043/500000000000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (31/128:ℝ) (63/256:ℝ)
    (125/512:ℝ) (1351372542879/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_062
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0373).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^0*thetaFirstMode x) ≤ (26395355887519204539/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (31/128:ℝ) (63/256:ℝ)
    (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_062 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_063 :
    (50812009483694646181/1000000000000000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (63/256:ℝ) (1/4:ℝ)
    (127/512:ℝ) (162590818501/12500000000000:ℝ) (23944799682406223/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_063
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0379).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^0*thetaFirstMode x) ≤ (50812300012024770137/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (63/256:ℝ) (1/4:ℝ)
    (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ) (23944799682406223/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_063 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator

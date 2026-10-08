import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature1

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_4_032 :
    (37693358970099071/1000000000000000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (1/8:ℝ) (33/256:ℝ)
    (1088630725/8572356096:ℝ) (742582132729/20000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_032
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0195).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^4*thetaFirstMode x) ≤ (37693480996894679/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (1/8:ℝ) (33/256:ℝ)
    (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_032 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_033 :
    (20650274024610777/500000000000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (33/256:ℝ) (17/128:ℝ)
    (1266682235/9676847616:ℝ) (3603890185209/100000000000000:ℝ) (372626855380705201/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_033
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0201).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^4*thetaFirstMode x) ≤ (41300684121300561/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (33/256:ℝ) (17/128:ℝ)
    (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ) (372626855380705201/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_033 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_034 :
    (9016143787497151/200000000000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (17/128:ℝ) (35/256:ℝ)
    (489102015/3628262912:ℝ) (3497198115757/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_034
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0207).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^4*thetaFirstMode x) ≤ (45080870101921043/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (17/128:ℝ) (35/256:ℝ)
    (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_034 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_035 :
    (12257374874404391/250000000000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (35/256:ℝ) (9/64:ℝ)
    (1692583555/12202446336:ℝ) (1696405728371/50000000000000:ℝ) (45629571400713733/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_035
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0213).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^4*thetaFirstMode x) ≤ (24514833416070613/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (35/256:ℝ) (9/64:ℝ)
    (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_035 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_036 :
    (26570877108000223/500000000000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (9/64:ℝ) (37/256:ℝ)
    (1944720365/13636271616:ℝ) (3290706716691/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_036
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0219).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^4*thetaFirstMode x) ≤ (10628387765253913/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (9/64:ℝ) (37/256:ℝ)
    (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_036 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_037 :
    (57411610567095641/1000000000000000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (37/256:ℝ) (19/128:ℝ)
    (742016625/5064300032:ℝ) (39885749149/1250000000000:ℝ) (89290827741626873/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_037
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0225).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^4*thetaFirstMode x) ≤ (57411813585033673/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (37/256:ℝ) (19/128:ℝ)
    (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ) (89290827741626873/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_037 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_038 :
    (61832488393531723/1000000000000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (19/128:ℝ) (39/256:ℝ)
    (2539036885/16879151616:ℝ) (3093246686931/100000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_038
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0231).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^4*thetaFirstMode x) ≤ (61832710975314733/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (19/128:ℝ) (39/256:ℝ)
    (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_038 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_039 :
    (66397132049041601/1000000000000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (39/256:ℝ) (5/32:ℝ)
    (2886281195/18702030336:ℝ) (2997842134509/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_039
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0237).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^4*thetaFirstMode x) ≤ (66397375371906803/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (39/256:ℝ) (5/32:ℝ)
    (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_039 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_040 :
    (71097645050485073/1000000000000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (5/32:ℝ) (41/256:ℝ)
    (1090173735/6889574912:ℝ) (2904621015451/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_040
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0243).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^4*thetaFirstMode x) ≤ (3554895515543851/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (5/32:ℝ) (41/256:ℝ)
    (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_040 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_041 :
    (37962763497546411/500000000000000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (41/256:ℝ) (21/128:ℝ)
    (3694637515/22786607616:ℝ) (281355767823/10000000000000:ℝ) (272524735160506569/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_041
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0249).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^4*thetaFirstMode x) ≤ (37962907702805233/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (41/256:ℝ) (21/128:ℝ)
    (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (272524735160506569/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_041 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_042 :
    (80871712493418891/1000000000000000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (21/128:ℝ) (43/256:ℝ)
    (4161656525/25063236096:ℝ) (544925219689/20000000000000:ℝ) (168193502212474447/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_042
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0255).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^4*thetaFirstMode x) ≤ (40436012640229651/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (21/128:ℝ) (43/256:ℝ)
    (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_042 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_043 :
    (85926611877695509/1000000000000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (43/256:ℝ) (11/64:ℝ)
    (1558251345/9168783872:ℝ) (2637799898199/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_043
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0261).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^4*thetaFirstMode x) ≤ (85926950278285107/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (43/256:ℝ) (11/64:ℝ)
    (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_043 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_044 :
    (91080153444824691/1000000000000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (11/64:ℝ) (45/256:ℝ)
    (5237258845/30123879936:ℝ) (2553052365357/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_044
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0267).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^4*thetaFirstMode x) ≤ (18216103740801587/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (11/64:ℝ) (45/256:ℝ)
    (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_044 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_045 :
    (24080456750599421/250000000000000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (45/256:ℝ) (23/128:ℝ)
    (5852656355/32923931136:ℝ) (3087945591/125000000000:ℝ) (10102667702120131/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_045
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0273).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^4*thetaFirstMode x) ≤ (96322220369174937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (45/256:ℝ) (23/128:ℝ)
    (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ) (10102667702120131/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_045 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_046 :
    (50820364240620903/500000000000000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (23/128:ℝ) (47/256:ℝ)
    (2174864055/11971599872:ℝ) (955873959/40000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_046
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0279).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^4*thetaFirstMode x) ≤ (101641151207473559/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (23/128:ℝ) (47/256:ℝ)
    (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_046 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_047 :
    (53512802700261163/500000000000000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (47/256:ℝ) (3/16:ℝ)
    (7256875675/39104964096:ℝ) (92440401589/4000000000000:ℝ) (628668827175261319/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_047
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0285).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^4*thetaFirstMode x) ≤ (13378257341925081/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (47/256:ℝ) (3/16:ℝ)
    (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ) (628668827175261319/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_047 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_048 :
    (56232451475706329/500000000000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (3/16:ℝ) (49/256:ℝ)
    (8053483685/42503087616:ℝ) (1117152020997/50000000000000:ℝ) (247842240871482451/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_048
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0291).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^4*thetaFirstMode x) ≤ (28116347035038957/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (3/16:ℝ) (49/256:ℝ)
    (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ) (247842240871482451/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_048 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_049 :
    (14743351312623801/125000000000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (49/256:ℝ) (25/128:ℝ)
    (2972854665/15372672512:ℝ) (2159538808159/100000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_049
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0297).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^4*thetaFirstMode x) ≤ (29486832195096179/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (49/256:ℝ) (25/128:ℝ)
    (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_049 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_050 :
    (123459308296256173/1000000000000000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (25/128:ℝ) (51/256:ℝ)
    (9856439005/49958785536:ℝ) (417337204461/20000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_050
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0303).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^4*thetaFirstMode x) ≤ (4938394435665637/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (25/128:ℝ) (51/256:ℝ)
    (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_050 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_051 :
    (2579804283530409/20000000000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (51/256:ℝ) (13/64:ℝ)
    (10871609315/54034607616:ℝ) (1007858583829/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_051
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0309).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^4*thetaFirstMode x) ≤ (128990802298766857/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (51/256:ℝ) (13/64:ℝ)
    (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_051 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_052 :
    (67263615048689039/500000000000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (13/64:ℝ) (53/256:ℝ)
    (3989585775/19451628032:ℝ) (486650886353/25000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_052
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0315).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^4*thetaFirstMode x) ≤ (134527854939015027/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (13/64:ℝ) (53/256:ℝ)
    (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_052 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_053 :
    (140057988278988803/1000000000000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (53/256:ℝ) (27/128:ℝ)
    (13152750835/62929199616:ℝ) (469829073363/25000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_053
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0321).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^4*thetaFirstMode x) ≤ (17507331376328733/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (53/256:ℝ) (27/128:ℝ)
    (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_053 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_054 :
    (29114019360552479/200000000000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (27/128:ℝ) (55/256:ℝ)
    (14428646645/67767323136:ℝ) (1813826405003/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_054
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0327).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^4*thetaFirstMode x) ≤ (145570798570870937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (27/128:ℝ) (55/256:ℝ)
    (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_054 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_055 :
    (151051184488771961/1000000000000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (55/256:ℝ) (7/32:ℝ)
    (5267231385/24293069312:ℝ) (109381546701/6250000000000:ℝ) (221847156154640409/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_055
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0333).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^4*thetaFirstMode x) ≤ (9440745400644737/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (55/256:ℝ) (7/32:ℝ)
    (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (221847156154640409/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_055 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_056 :
    (78244472441180591/500000000000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (7/32:ℝ) (57/256:ℝ)
    (17277338965/78274991616:ℝ) (422030519889/25000000000000:ℝ) (545183636290087911/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_056
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0339).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^4*thetaFirstMode x) ≤ (1222576000339319/7812500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (7/32:ℝ) (57/256:ℝ)
    (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_056 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_057 :
    (80935589604909427/500000000000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (57/256:ℝ) (29/128:ℝ)
    (18861226475/83964996096:ℝ) (1627849072149/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_057
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0345).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^4*thetaFirstMode x) ≤ (80936002330632623/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (57/256:ℝ) (29/128:ℝ)
    (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_057 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_058 :
    (20898229768520141/125000000000000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (29/128:ℝ) (59/256:ℝ)
    (6853068495/29986575872:ℝ) (78462816197/5000000000000:ℝ) (8222818714789663/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_058
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0351).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^4*thetaFirstMode x) ≤ (167186706901802757/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (29/128:ℝ) (59/256:ℝ)
    (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ) (8222818714789663/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_058 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_059 :
    (21552632784679767/125000000000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (59/256:ℝ) (15/64:ℝ)
    (22377331795/96269876736:ℝ) (1512314380703/100000000000000:ℝ) (516782794844143017/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_059
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0357).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^4*thetaFirstMode x) ≤ (43105493825921133/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (59/256:ℝ) (15/64:ℝ)
    (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ) (516782794844143017/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_059 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_060 :
    (22195652636235731/125000000000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (15/64:ℝ) (61/256:ℝ)
    (24321871805/102906318336:ℝ) (1456993752893/100000000000000:ℝ) (31706377237718811/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_060
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0363).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^4*thetaFirstMode x) ≤ (177566179313455379/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (15/64:ℝ) (61/256:ℝ)
    (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ) (31706377237718811/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_060 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_061 :
    (45651737608735281/250000000000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (61/256:ℝ) (31/128:ℝ)
    (8799768705/36626703872:ℝ) (350816233323/25000000000000:ℝ) (497823671186989721/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_061
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0369).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^4*thetaFirstMode x) ≤ (182607954733844497/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (61/256:ℝ) (31/128:ℝ)
    (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ) (497823671186989721/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_061 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_062 :
    (46883797075429863/250000000000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (31/128:ℝ) (63/256:ℝ)
    (28616333125/117202500096:ℝ) (84443650907/6250000000000:ℝ) (97670637171555123/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_062
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0375).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^4*thetaFirstMode x) ≤ (37507247900244223/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (31/128:ℝ) (63/256:ℝ)
    (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_062 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_063 :
    (192339208822421319/1000000000000000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (63/256:ℝ) (1/4:ℝ)
    (30979872635/124884911616:ℝ) (260092941239/20000000000000:ℝ) (23944799682406223/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_063
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0381).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^4*thetaFirstMode x) ≤ (48085076923524937/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (63/256:ℝ) (1/4:ℝ)
    (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ) (23944799682406223/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_063 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

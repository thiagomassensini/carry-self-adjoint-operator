import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature1

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_032 :
    (9805270173629/1000000000000000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/8:ℝ) (33/256:ℝ)
    (730222341159285/5748281504317952:ℝ) (3711782621959/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_032
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0197).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^8*thetaFirstMode x) ≤ (9805301874169/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/8:ℝ) (33/256:ℝ)
    (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_032 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_033 :
    (12127043159897/1000000000000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (33/256:ℝ) (17/128:ℝ)
    (4795188919157943/36622101413148160:ℝ) (3602818939147/100000000000000:ℝ) (372626855380705201/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_033
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0203).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^8*thetaFirstMode x) ≤ (6063541531133/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (33/256:ℝ) (17/128:ℝ)
    (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ) (372626855380705201/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_033 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_034 :
    (14888443930407/1000000000000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (17/128:ℝ) (35/256:ℝ)
    (6247526395102641/46332533517852160:ℝ) (3496180167453/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_034
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0209).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^8*thetaFirstMode x) ≤ (3722123447601/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (17/128:ℝ) (35/256:ℝ)
    (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_034 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_035 :
    (9075872740859/500000000000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (35/256:ℝ) (9/64:ℝ)
    (8078499778926159/58225454071144960:ℝ) (3391843597631/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_035
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0215).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^8*thetaFirstMode x) ≤ (1134487959679/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (35/256:ℝ) (9/64:ℝ)
    (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_035 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_036 :
    (2198483192539/100000000000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (9/64:ℝ) (37/256:ℝ)
    (10371833391193857/72708564804252160:ℝ) (3289785996133/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_036
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0221).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^8*thetaFirstMode x) ≤ (1099245410261/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/64:ℝ) (37/256:ℝ)
    (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_036 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_037 :
    (26461316400069/1000000000000000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (37/256:ℝ) (19/128:ℝ)
    (2645329456026675/18050233071498752:ℝ) (3189983630081/100000000000000:ℝ) (89290827741626873/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_037
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0227).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^8*thetaFirstMode x) ≤ (13230704929727/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (37/256:ℝ) (19/128:ℝ)
    (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ) (89290827741626873/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_037 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_038 :
    (1266424801587/40000000000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (19/128:ℝ) (39/256:ℝ)
    (16759748134830393/111391385333532160:ℝ) (309241229113/10000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_038
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0233).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^8*thetaFirstMode x) ≤ (6332146775067/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (19/128:ℝ) (39/256:ℝ)
    (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_038 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_039 :
    (7533601757419/200000000000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (39/256:ℝ) (5/32:ℝ)
    (21108185233275591/136744035433576960:ℝ) (599409463703/20000000000000:ℝ) (349028961673015303/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_039
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0239).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^8*thetaFirstMode x) ≤ (37668146666963/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (39/256:ℝ) (5/32:ℝ)
    (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_039 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_040 :
    (22287292556503/500000000000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (5/32:ℝ) (41/256:ℝ)
    (26432093791371609/167009112048540160:ℝ) (2903863621341/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_040
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0245).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^8*thetaFirstMode x) ≤ (22287375613619/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/32:ℝ) (41/256:ℝ)
    (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_040 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_041 :
    (52477232008407/1000000000000000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (41/256:ℝ) (21/128:ℝ)
    (32917849303728807/202980990606108160:ℝ) (351604462549/12500000000000:ℝ) (272524735160506569/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_041
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0251).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^8*thetaFirstMode x) ≤ (52477431123379/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (41/256:ℝ) (21/128:ℝ)
    (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (272524735160506569/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_041 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_042 :
    (61478506956513/1000000000000000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (21/128:ℝ) (43/256:ℝ)
    (8156311544891565/49111668780733952:ℝ) (2723937669481/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_042
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0257).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^8*thetaFirstMode x) ≤ (15369686117999/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (21/128:ℝ) (43/256:ℝ)
    (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_042 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_043 :
    (71686483957823/1000000000000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (43/256:ℝ) (11/64:ℝ)
    (50272907626205343/295754822586012160:ℝ) (2637143276417/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_043
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0263).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^8*thetaFirstMode x) ≤ (280026429559/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (43/256:ℝ) (11/64:ℝ)
    (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_043 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_044 :
    (10401817759561/125000000000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (11/64:ℝ) (45/256:ℝ)
    (61679411798377041/354710535855669760:ℝ) (2552425923669/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_044
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0269).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^8*thetaFirstMode x) ≤ (83214875429807/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/64:ℝ) (45/256:ℝ)
    (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_044 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_045 :
    (96181099393647/1000000000000000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (45/256:ℝ) (23/128:ℝ)
    (75331067100848559/423704371432783360:ℝ) (1234879344403/50000000000000:ℝ) (10102667702120131/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_045
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0275).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^8*thetaFirstMode x) ≤ (48090745882133/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (45/256:ℝ) (23/128:ℝ)
    (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ) (10102667702120131/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_045 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_046 :
    (110709291687051/1000000000000000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (23/128:ℝ) (47/256:ℝ)
    (91605462777481257/504167194710300160:ℝ) (1194557172351/50000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_046
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0281).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^8*thetaFirstMode x) ≤ (55354875820241/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (23/128:ℝ) (47/256:ℝ)
    (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_046 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_047 :
    (126926595608923/1000000000000000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (47/256:ℝ) (3/16:ℝ)
    (22186673770886955/119539193595863552:ℝ) (2310465379561/100000000000000:ℝ) (628668827175261319/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_047
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0287).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^8*thetaFirstMode x) ≤ (63463566337213/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (47/256:ℝ) (3/16:ℝ)
    (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ) (628668827175261319/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_047 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_048 :
    (28992879319269/200000000000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/16:ℝ) (49/256:ℝ)
    (133804837701602793/706068831528348160:ℝ) (1116892008393/50000000000000:ℝ) (247842240871482451/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_048
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0293).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^8*thetaFirstMode x) ≤ (144965021341077/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/16:ℝ) (49/256:ℝ)
    (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ) (247842240871482451/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_048 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_049 :
    (164957502218939/1000000000000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (49/256:ℝ) (25/128:ℝ)
    (160775853321491991/831261189349250560:ℝ) (2159042234709/100000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_049
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0299).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^8*thetaFirstMode x) ≤ (16495822632369/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (49/256:ℝ) (25/128:ℝ)
    (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_049 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_050 :
    (46760900534529/250000000000000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (25/128:ℝ) (51/256:ℝ)
    (192475564448517009/975462843111554560:ℝ) (2086211786141/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_050
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0305).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^8*thetaFirstMode x) ≤ (187044438475793/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (25/128:ℝ) (51/256:ℝ)
    (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_050 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_051 :
    (105681338167589/500000000000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (51/256:ℝ) (13/64:ℝ)
    (229614139092996207/1141096218995868160:ℝ) (1007632108921/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_051
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0311).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^8*thetaFirstMode x) ≤ (211363639050469/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (51/256:ℝ) (13/64:ℝ)
    (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_051 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_052 :
    (7439261053821/31250000000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (13/64:ℝ) (53/256:ℝ)
    (54598255949620845/266167146581207552:ℝ) (1946170889819/100000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_052
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0317).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^8*thetaFirstMode x) ≤ (238057458313459/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/64:ℝ) (53/256:ℝ)
    (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_052 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_053 :
    (13363361186031/50000000000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (53/256:ℝ) (27/128:ℝ)
    (323505440094667743/1547628340508700160:ℝ) (1878902994507/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_053
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0323).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^8*thetaFirstMode x) ≤ (10690739484843/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (53/256:ℝ) (27/128:ℝ)
    (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_053 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_054 :
    (149569051918097/500000000000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (27/128:ℝ) (55/256:ℝ)
    (382163785687980441/1794715319477839360:ℝ) (113339473489/6250000000000:ℝ) (564026236416942689/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_054
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0329).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^8*thetaFirstMode x) ≤ (299139544496019/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (27/128:ℝ) (55/256:ℝ)
    (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_054 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_055 :
    (33381126668717/100000000000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (55/256:ℝ) (7/32:ℝ)
    (450092942792761959/2075655332250933760:ℝ) (349945509609/20000000000000:ℝ) (221847156154640409/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_055
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0335).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^8*thetaFirstMode x) ≤ (166906452328793/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (55/256:ℝ) (7/32:ℝ)
    (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (221847156154640409/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_055 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_056 :
    (185713815184309/500000000000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (7/32:ℝ) (57/256:ℝ)
    (528550581246993657/2394348818532252160:ℝ) (1687761714569/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_056
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0341).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^8*thetaFirstMode x) ≤ (185714743691951/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/32:ℝ) (57/256:ℝ)
    (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_056 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_057 :
    (41212591640939/100000000000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (57/256:ℝ) (29/128:ℝ)
    (123787575796526235/551012753541565952:ℝ) (813752393251/50000000000000:ℝ) (214291693428588019/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_057
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0347).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^8*thetaFirstMode x) ≤ (206064007984133/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (57/256:ℝ) (29/128:ℝ)
    (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_057 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_058 :
    (228020889975139/500000000000000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (29/128:ℝ) (59/256:ℝ)
    (722812917611120193/3162462922265628160:ℝ) (156892740107/10000000000000:ℝ) (8222818714789663/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_058
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0353).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^8*thetaFirstMode x) ≤ (456044147397101/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (29/128:ℝ) (59/256:ℝ)
    (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ) (8222818714789663/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_058 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_059 :
    (251653458554457/500000000000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (59/256:ℝ) (15/64:ℝ)
    (841905060294227391/3621632464243356160:ℝ) (378000034967/25000000000000:ℝ) (516782794844143017/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_059
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0359).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^8*thetaFirstMode x) ≤ (503309579713123/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (59/256:ℝ) (15/64:ℝ)
    (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ) (516782794844143017/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_059 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_060 :
    (277024077394137/500000000000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (15/64:ℝ) (61/256:ℝ)
    (978130364965943409/4138112237655400960:ℝ) (1456693546909/100000000000000:ℝ) (31706377237718811/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_060
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0365).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^8*thetaFirstMode x) ≤ (554051141816879/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/64:ℝ) (61/256:ℝ)
    (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ) (31706377237718811/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_060 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_061 :
    (608386528449293/1000000000000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (61/256:ℝ) (31/128:ℝ)
    (1133608087849118607/4717927560779292160:ℝ) (28059562929/2000000000000:ℝ) (497823671186989721/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_061
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0371).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^8*thetaFirstMode x) ≤ (304194935623303/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (61/256:ℝ) (31/128:ℝ)
    (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ) (497823671186989721/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_061 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_062 :
    (666436353627581/1000000000000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (31/128:ℝ) (63/256:ℝ)
    (262135666824211125/1073524536622218752:ℝ) (168853057581/12500000000000:ℝ) (97670637171555123/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_062
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0377).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^8*thetaFirstMode x) ≤ (333220042840711/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/128:ℝ) (63/256:ℝ)
    (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_062 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_063 :
    (728304297106211/1000000000000000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (63/256:ℝ) (1/4:ℝ)
    (1511920914525505143/6094295942728092160:ℝ) (650101513471/50000000000000:ℝ) (23944799682406223/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_063
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0383).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^8*thetaFirstMode x) ≤ (728308454111511/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (63/256:ℝ) (1/4:ℝ)
    (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ) (23944799682406223/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_063 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

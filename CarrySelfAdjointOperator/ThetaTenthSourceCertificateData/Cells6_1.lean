import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature1

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_032 :
    (607846313076457/1000000000000000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/8:ℝ) (33/256:ℝ)
    (2148278933255/16913827039232:ℝ) (371234625647/10000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_032
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0196).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^6*thetaFirstMode x) ≤ (75981034961701/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/8:ℝ) (33/256:ℝ)
    (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_032 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_033 :
    (707605124367001/1000000000000000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (33/256:ℝ) (17/128:ℝ)
    (2655697006585/20285249878016:ℝ) (900838553917/25000000000000:ℝ) (372626855380705201/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_033
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0202).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^6*thetaFirstMode x) ≤ (353803727154419/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (33/256:ℝ) (17/128:ℝ)
    (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ) (372626855380705201/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_033 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_034 :
    (819142284204563/1000000000000000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (17/128:ℝ) (35/256:ℝ)
    (3262570400103/24199058905088:ℝ) (218543051877/6250000000000:ℝ) (737736862199491809/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_034
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0208).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^6*thetaFirstMode x) ≤ (204786257336791/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (17/128:ℝ) (35/256:ℝ)
    (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_034 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_035 :
    (943258152467071/1000000000000000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (35/256:ℝ) (9/64:ℝ)
    (3984641617817/28722928068608:ℝ) (678465449279/20000000000000:ℝ) (45629571400713733/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_035
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0214).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^6*thetaFirstMode x) ≤ (58953835618899/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (35/256:ℝ) (9/64:ℝ)
    (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_035 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_036 :
    (1080750024562099/1000000000000000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (9/64:ℝ) (37/256:ℝ)
    (4839586825255/33930676299776:ℝ) (3290246102813/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_036
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0220).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^6*thetaFirstMode x) ≤ (1080753776888023/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/64:ℝ) (37/256:ℝ)
    (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_036 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_037 :
    (154050881714167/125000000000000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (37/256:ℝ) (19/128:ℝ)
    (5847188792025/39902628780032:ℝ) (1595210775743/50000000000000:ℝ) (89290827741626873/62500000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_037
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0226).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^6*thetaFirstMode x) ≤ (1232411409317797/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (37/256:ℝ) (19/128:ℝ)
    (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ) (89290827741626873/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_037 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_038 :
    (279801015092263/200000000000000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (19/128:ℝ) (39/256:ℝ)
    (7029519853895/46725988530176:ℝ) (77320732023/2500000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_038
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0232).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^6*thetaFirstMode x) ≤ (1399010108790937/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (19/128:ℝ) (39/256:ℝ)
    (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_038 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_039 :
    (1581301370365831/1000000000000000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (39/256:ℝ) (5/32:ℝ)
    (8411135176633/54495218321408:ℝ) (2997444537467/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_039
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0238).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^6*thetaFirstMode x) ≤ (395326790545779/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (39/256:ℝ) (5/32:ℝ)
    (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_039 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_040 :
    (890014700527307/500000000000000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (5/32:ℝ) (41/256:ℝ)
    (10019276603847/63312432908288:ℝ) (2904242146377/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_040
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0244).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^6*thetaFirstMode x) ≤ (1780036038699879/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (5/32:ℝ) (41/256:ℝ)
    (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_040 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_041 :
    (1995893559716491/1000000000000000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (41/256:ℝ) (21/128:ℝ)
    (11884087371065/73287801583616:ℝ) (2813196532533/100000000000000:ℝ) (272524735160506569/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_041
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0250).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^6*thetaFirstMode x) ≤ (31185955270999/15625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (41/256:ℝ) (21/128:ℝ)
    (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (272524735160506569/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_041 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_042 :
    (1114781980869137/500000000000000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (21/128:ℝ) (43/256:ℝ)
    (14038837968295/84539961055232:ℝ) (2724281740861/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_042
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0256).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^6*thetaFirstMode x) ≤ (278696572568279/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (21/128:ℝ) (43/256:ℝ)
    (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_042 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_043 :
    (124083566033521/50000000000000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (43/256:ℝ) (11/64:ℝ)
    (16520163433305/97196438644736:ℝ) (2637471456499/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_043
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0262).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^6*thetaFirstMode x) ≤ (2481681089111491/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (43/256:ℝ) (11/64:ℝ)
    (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_043 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_044 :
    (2752801938935257/1000000000000000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (11/64:ℝ) (45/256:ℝ)
    (19368312357863/111394085808128:ℝ) (1276369512389/50000000000000:ℝ) (655397632509854761/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_044
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0268).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^6*thetaFirstMode x) ≤ (688203243227827/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (11/64:ℝ) (45/256:ℝ)
    (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_044 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_045 :
    (608698569546349/200000000000000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (45/256:ℝ) (23/128:ℝ)
    (22627407889177/127279521978368:ℝ) (2470057471063/100000000000000:ℝ) (10102667702120131/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_045
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0274).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^6*thetaFirstMode x) ≤ (3043505270750957/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (45/256:ℝ) (23/128:ℝ)
    (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ) (10102667702120131/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_045 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_046 :
    (3354227128314233/1000000000000000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (23/128:ℝ) (47/256:ℝ)
    (26345721008775/145009588729856:ℝ) (1194699760201/50000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_046
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0280).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^6*thetaFirstMode x) ≤ (13102504186223/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (23/128:ℝ) (47/256:ℝ)
    (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_046 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_047 :
    (1842714722838981/500000000000000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (47/256:ℝ) (3/16:ℝ)
    (30575956371065/164751814264832:ℝ) (2310737617121/100000000000000:ℝ) (628668827175261319/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_047
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0286).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^6*thetaFirstMode x) ≤ (3685445048579227/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (47/256:ℝ) (3/16:ℝ)
    (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ) (628668827175261319/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_047 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_048 :
    (807492364796641/200000000000000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/16:ℝ) (49/256:ℝ)
    (35375550983815/186684888221696:ℝ) (2234043944303/100000000000000:ℝ) (247842240871482451/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_048
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0292).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^6*thetaFirstMode x) ≤ (201873961680197/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/16:ℝ) (49/256:ℝ)
    (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ) (247842240871482451/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_048 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_049 :
    (4410619691293029/1000000000000000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (49/256:ℝ) (25/128:ℝ)
    (40806986012793/210999146805248:ℝ) (269911305387/12500000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_049
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0298).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^6*thetaFirstMode x) ≤ (551329882865097/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (49/256:ℝ) (25/128:ℝ)
    (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_049 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_050 :
    (961025643956827/200000000000000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (25/128:ℝ) (51/256:ℝ)
    (46938111992807/237897068238848:ℝ) (1043224416013/50000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_050
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0304).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^6*thetaFirstMode x) ≤ (961029943365237/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (25/128:ℝ) (51/256:ℝ)
    (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_050 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_051 :
    (2610569492556329/500000000000000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (51/256:ℝ) (13/64:ℝ)
    (53842487727385/267593778538496:ℝ) (251936328269/12500000000000:ℝ) (592037690565412011/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_051
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0310).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^6*thetaFirstMode x) ≤ (2610581389561473/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (51/256:ℝ) (13/64:ℝ)
    (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_051 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_052 :
    (5658726966870281/1000000000000000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (13/64:ℝ) (53/256:ℝ)
    (61599733159335/300317567608832:ℝ) (486596789031/25000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_052
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0316).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^6*thetaFirstMode x) ≤ (5658753237559067/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (13/64:ℝ) (53/256:ℝ)
    (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_052 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_053 :
    (764735988736047/125000000000000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (53/256:ℝ) (27/128:ℝ)
    (70295896494425/336310415661056:ℝ) (1879109587161/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_053
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0322).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^6*thetaFirstMode x) ≤ (1529479211255413/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (53/256:ℝ) (27/128:ℝ)
    (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_053 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_054 :
    (3299268031801877/500000000000000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (27/128:ℝ) (55/256:ℝ)
    (80023835860423/375828529952768:ℝ) (1813628937867/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_054
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0328).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^6*thetaFirstMode x) ≤ (659856785900049/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (27/128:ℝ) (55/256:ℝ)
    (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_054 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_055 :
    (3550251157468479/500000000000000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (55/256:ℝ) (7/32:ℝ)
    (90883615783737/419142891849728:ℝ) (874958049499/50000000000000:ℝ) (221847156154640409/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_055
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0334).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^6*thetaFirstMode x) ≤ (7100537174285511/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (55/256:ℝ) (7/32:ℝ)
    (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (221847156154640409/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_055 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_056 :
    (7623532726913229/1000000000000000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (7/32:ℝ) (57/256:ℝ)
    (102982918765895/466539814209536:ℝ) (1687941852021/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_056
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0340).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^6*thetaFirstMode x) ≤ (3811785430834793/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/32:ℝ) (57/256:ℝ)
    (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_056 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_057 :
    (1020910936708943/125000000000000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (57/256:ℝ) (29/128:ℝ)
    (116437472242105/518321509087232:ℝ) (813838443789/50000000000000:ℝ) (214291693428588019/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_057
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0346).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^6*thetaFirstMode x) ≤ (4083664561435837/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (57/256:ℝ) (29/128:ℝ)
    (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_057 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_058 :
    (8731340319488399/1000000000000000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (29/128:ℝ) (59/256:ℝ)
    (131371491204135/574806665762816:ℝ) (1569091823787/100000000000000:ℝ) (8222818714789663/7812500000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_058
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0352).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^6*thetaFirstMode x) ≤ (1746277133894821/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (29/128:ℝ) (59/256:ℝ)
    (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ) (8222818714789663/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_058 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_059 :
    (74521425816197/8000000000000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (59/256:ℝ) (15/64:ℝ)
    (147918136769753/636331039090688:ℝ) (378039306089/25000000000000:ℝ) (516782794844143017/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_059
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0358).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^6*thetaFirstMode x) ≤ (4657613765617943/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (59/256:ℝ) (15/64:ℝ)
    (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ) (516782794844143017/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_059 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_060 :
    (4959100898898879/500000000000000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (15/64:ℝ) (61/256:ℝ)
    (166219990980967/703248048171008:ℝ) (1456843616537/100000000000000:ℝ) (31706377237718811/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_060
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0364).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^6*thetaFirstMode x) ≤ (1983651059285819/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (15/64:ℝ) (61/256:ℝ)
    (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ) (31706377237718811/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_060 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_061 :
    (1317465730635887/125000000000000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (61/256:ℝ) (31/128:ℝ)
    (186429548113305/775929385342976:ℝ) (701560754439/50000000000000:ℝ) (497823671186989721/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_061
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0370).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^6*thetaFirstMode x) ≤ (16468412163717/1562500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (61/256:ℝ) (31/128:ℝ)
    (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ) (497823671186989721/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_061 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_062 :
    (558949025860013/50000000000000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (31/128:ℝ) (63/256:ℝ)
    (208709722778375/854765635500032:ℝ) (1350961408769/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_062
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0376).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^6*thetaFirstMode x) ≤ (5589521575344419/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (31/128:ℝ) (63/256:ℝ)
    (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_062 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_063 :
    (11835112826587523/1000000000000000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (63/256:ℝ) (1/4:ℝ)
    (233234375101945/940166905726976:ℝ) (1300333839769/100000000000000:ℝ) (23944799682406223/25000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_063
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0382).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^6*thetaFirstMode x) ≤ (11835180412229823/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (63/256:ℝ) (1/4:ℝ)
    (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ) (23944799682406223/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_063 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

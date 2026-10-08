import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature2

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_4_064 :
    (197008654430539319/1000000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (1/4:ℝ) (65/256:ℝ)
    (11165689815/44312986112:ℝ) (312833588019/25000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_064
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0387).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^4*thetaFirstMode x) ≤ (197009801688281837/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (1/4:ℝ) (65/256:ℝ)
    (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_064 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_065 :
    (201533566074147499/1000000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (65/256:ℝ) (33/128:ℝ)
    (36175296955/141376436736:ℝ) (601838973369/50000000000000:ℝ) (184017103411496703/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_065
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0393).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^4*thetaFirstMode x) ≤ (100767381186624751/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (65/256:ℝ) (33/128:ℝ)
    (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ) (184017103411496703/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_065 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_066 :
    (205904411430854923/1000000000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (33/128:ℝ) (67/256:ℝ)
    (39022160765/150209327616:ℝ) (578733076081/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_066
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0399).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^4*thetaFirstMode x) ≤ (51476414340538867/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (33/128:ℝ) (67/256:ℝ)
    (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_066 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_067 :
    (52528027762085969/250000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (67/256:ℝ) (17/64:ℝ)
    (14015167425/53149932032:ℝ) (222533942791/20000000000000:ℝ) (88261133131181809/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_067
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0405).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^4*thetaFirstMode x) ≤ (210113407138132921/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (67/256:ℝ) (17/64:ℝ)
    (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ) (88261133131181809/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_067 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_068 :
    (214148062374950289/1000000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (17/64:ℝ) (69/256:ℝ)
    (45253402285/169110191616:ℝ) (534629738669/50000000000000:ℝ) (107998327769847/125000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_068
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0411).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^4*thetaFirstMode x) ≤ (107074704540856677/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (17/64:ℝ) (69/256:ℝ)
    (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ) (107998327769847/125000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_068 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_069 :
    (425789378176587/1953125000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (69/256:ℝ) (35/128:ℝ)
    (48654184595/179203047936:ℝ) (513603201403/50000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_069
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0417).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^4*thetaFirstMode x) ≤ (218005559339186391/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (69/256:ℝ) (35/128:ℝ)
    (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_069 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_070 :
    (13854551466643837/62500000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (35/128:ℝ) (71/256:ℝ)
    (17418806535/63247027712:ℝ) (986481581501/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_070
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0423).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^4*thetaFirstMode x) ≤ (55418568125330701/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (35/128:ℝ) (71/256:ℝ)
    (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_070 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_071 :
    (28143374808572669/125000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (71/256:ℝ) (9/32:ℝ)
    (56068927915/200737199616:ℝ) (947056250241/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_071
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0429).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^4*thetaFirstMode x) ≤ (112574249533703139/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (71/256:ℝ) (9/32:ℝ)
    (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_071 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_072 :
    (45684037670057033/200000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (9/32:ℝ) (73/256:ℝ)
    (60100783925/212204484096:ℝ) (7100795361/781250000000:ℝ) (24701951795471107/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_072
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0435).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^4*thetaFirstMode x) ≤ (114210870340278017/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (9/32:ℝ) (73/256:ℝ)
    (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (24701951795471107/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_072 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_073 :
    (115743229490564377/500000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (73/256:ℝ) (37/128:ℝ)
    (21453773145/74718735872:ℝ) (871989821331/100000000000000:ℝ) (386185615014076073/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_073
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0441).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^4*thetaFirstMode x) ≤ (46297612626039127/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (73/256:ℝ) (37/128:ℝ)
    (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ) (386185615014076073/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_073 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_074 :
    (234340451144975319/1000000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (37/128:ℝ) (75/256:ℝ)
    (68860127245/236605825536:ℝ) (209073014059/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_074
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0447).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^4*thetaFirstMode x) ≤ (234342107123285431/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (37/128:ℝ) (75/256:ℝ)
    (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_074 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_075 :
    (118488694550943189/500000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (75/256:ℝ) (19/64:ℝ)
    (73607064755/249566977536:ℝ) (801780473903/100000000000000:ℝ) (23018684593509581/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_075
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0453).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^4*thetaFirstMode x) ≤ (236979096836961457/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (75/256:ℝ) (19/64:ℝ)
    (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ) (23018684593509581/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_075 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_076 :
    (239393086932640197/1000000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (19/64:ℝ) (77/256:ℝ)
    (26204085855/87684495872:ℝ) (96053406609/12500000000000:ℝ) (718932361707831433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_076
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0459).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^4*thetaFirstMode x) ≤ (47878969254498631/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (19/64:ℝ) (77/256:ℝ)
    (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_076 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_077 :
    (120791976363285209/500000000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (77/256:ℝ) (39/128:ℝ)
    (83886103075/277079364096:ℝ) (736204800113/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_077
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0465).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^4*thetaFirstMode x) ≤ (120792881718256689/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (77/256:ℝ) (39/128:ℝ)
    (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_077 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_078 :
    (243546990620598899/1000000000000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (39/128:ℝ) (79/256:ℝ)
    (89439274085/291658799616:ℝ) (352542881727/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_078
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0471).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^4*thetaFirstMode x) ≤ (121774426191407261/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (39/128:ℝ) (79/256:ℝ)
    (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_078 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_079 :
    (61319950187763651/250000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (79/256:ℝ) (5/16:ℝ)
    (31760907465/102268723712:ℝ) (5400344349/800000000000:ℝ) (166728513122296977/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_079
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0477).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^4*thetaFirstMode x) ≤ (245281713162973651/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (79/256:ℝ) (5/16:ℝ)
    (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ) (166728513122296977/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_079 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_080 :
    (61695144288136013/250000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (5/16:ℝ) (81/256:ℝ)
    (101427682405/322536039936:ℝ) (646049805863/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_080
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0483).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^4*thetaFirstMode x) ≤ (246782539729644399/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (5/16:ℝ) (81/256:ℝ)
    (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_080 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_081 :
    (62012025918546191/250000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (81/256:ℝ) (41/128:ℝ)
    (107885674715/338863151616:ℝ) (309039745557/50000000000000:ℝ) (126624657912986459/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_081
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0489).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^4*thetaFirstMode x) ≤ (124025057922782937/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (81/256:ℝ) (41/128:ℝ)
    (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ) (126624657912986459/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_081 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_082 :
    (249081747956384299/1000000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (41/128:ℝ) (83/256:ℝ)
    (38222836575/118600812032:ℝ) (295552913387/50000000000000:ℝ) (154128683512619971/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_082
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0495).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^4*thetaFirstMode x) ≤ (249083809068444141/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (41/128:ℝ) (83/256:ℝ)
    (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_082 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_083 :
    (124940726776947739/500000000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (83/256:ℝ) (21/64:ℝ)
    (121788291235/373369007616:ℝ) (565102837013/100000000000000:ℝ) (300052897882409501/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_083
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0501).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^4*thetaFirstMode x) ≤ (31235445358740127/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (83/256:ℝ) (21/64:ℝ)
    (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ) (300052897882409501/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_083 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_084 :
    (250447730266967837/1000000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (21/64:ℝ) (85/256:ℝ)
    (129257420045/391578164736:ℝ) (270022426323/50000000000000:ℝ) (291951206062636471/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_084
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0507).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^4*thetaFirstMode x) ≤ (31306235870744451/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (21/64:ℝ) (85/256:ℝ)
    (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_084 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_085 :
    (31347705344891513/125000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (85/256:ℝ) (43/128:ℝ)
    (45696199185/136815130112:ℝ) (10318130411/2000000000000:ℝ) (56791022721725001/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_085
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0513).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^4*thetaFirstMode x) ≤ (250783845938152483/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (85/256:ℝ) (43/128:ℝ)
    (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ) (56791022721725001/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_085 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_086 :
    (5017695950868241/20000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (43/128:ℝ) (87/256:ℝ)
    (145294829365/429986351616:ℝ) (492662812623/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_086
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0519).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^4*thetaFirstMode x) ≤ (15680440388761179/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (43/128:ℝ) (87/256:ℝ)
    (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_086 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_087 :
    (250759328435348773/1000000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (87/256:ℝ) (11/32:ℝ)
    (153889428875/450216900096:ℝ) (94057806861/20000000000000:ℝ) (536580549127126453/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_087
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0525).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^4*thetaFirstMode x) ≤ (250761621543935689/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (87/256:ℝ) (11/32:ℝ)
    (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (536580549127126453/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_087 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_088 :
    (125203940267804627/500000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (11/32:ℝ) (89/256:ℝ)
    (54295340295/157051023872:ℝ) (448760832603/100000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_088
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0531).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^4*thetaFirstMode x) ≤ (62602554233410953/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (11/32:ℝ) (89/256:ℝ)
    (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_088 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_089 :
    (124916796433556353/500000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (89/256:ℝ) (45/128:ℝ)
    (172298545195/492811086336:ℝ) (214027101841/50000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_089
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0537).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^4*thetaFirstMode x) ≤ (62458992833916627/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (89/256:ℝ) (45/128:ℝ)
    (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_089 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_090 :
    (249040079742139323/1000000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (45/128:ℝ) (91/256:ℝ)
    (182141260205/515207348736:ℝ) (204072749989/50000000000000:ℝ) (245647015792921217/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_090
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0543).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^4*thetaFirstMode x) ≤ (249042498985395157/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (45/128:ℝ) (91/256:ℝ)
    (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_090 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_091 :
    (248031410958941881/1000000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (91/256:ℝ) (23/64:ℝ)
    (64142915505/179452815872:ℝ) (389011436837/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_091
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0549).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^4*thetaFirstMode x) ≤ (124016934804737387/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (91/256:ℝ) (23/64:ℝ)
    (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_091 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_092 :
    (61703022735584883/250000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (23/64:ℝ) (93/256:ℝ)
    (203175910525/562281156096:ℝ) (370629098703/100000000000000:ℝ) (231145058214661231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_092
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0555).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^4*thetaFirstMode x) ≤ (246814587559852391/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (23/64:ℝ) (93/256:ℝ)
    (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ) (231145058214661231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_092 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_093 :
    (245387036910180937/1000000000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (93/256:ℝ) (47/128:ℝ)
    (214397988035/586992431616:ℝ) (176487972411/50000000000000:ℝ) (224077469909545329/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_093
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0561).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^4*thetaFirstMode x) ≤ (49077913997426873/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (93/256:ℝ) (47/128:ℝ)
    (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ) (224077469909545329/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_093 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_094 :
    (243761556187692389/1000000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (47/128:ℝ) (95/256:ℝ)
    (75370182615/204169805312:ℝ) (168014907247/50000000000000:ℝ) (217134160115492507/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_094
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0567).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^4*thetaFirstMode x) ≤ (243764124149848481/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (47/128:ℝ) (95/256:ℝ)
    (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ) (217134160115492507/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_094 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_4_095 :
    (967765291024033/4000000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 4 (95/256:ℝ) (3/8:ℝ)
    (238329495355/638849435136:ℝ) (39971116481/12500000000000:ℝ) (52579114235318267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_095
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0573).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_4_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^4*thetaFirstMode x) ≤ (12097196198343251/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 4 (95/256:ℝ) (3/8:ℝ)
    (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_095 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

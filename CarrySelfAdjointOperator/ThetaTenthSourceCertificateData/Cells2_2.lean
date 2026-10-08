import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature2

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_2_064 :
    (3103456807888165359/1000000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (1/4:ℝ) (65/256:ℝ)
    (3220227/12780544:ℝ) (625729691661/50000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_064
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0386).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^2*thetaFirstMode x) ≤ (1551737444004206533/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (1/4:ℝ) (65/256:ℝ)
    (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_064 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_065 :
    (615709171569606603/200000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (65/256:ℝ) (33/128:ℝ)
    (3372333/13179904:ℝ) (240759471259/20000000000000:ℝ) (184017103411496703/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_065
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0392).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^2*thetaFirstMode x) ≤ (123142565583632411/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (65/256:ℝ) (33/128:ℝ)
    (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ) (184017103411496703/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_065 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_066 :
    (190714703101155883/62500000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (33/128:ℝ) (67/256:ℝ)
    (3529155/13585408:ℝ) (144697522813/12500000000000:ℝ) (901314286011735199/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_066
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0398).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^2*thetaFirstMode x) ≤ (762863430386038191/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (33/128:ℝ) (67/256:ℝ)
    (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_066 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_067 :
    (3022221252581406813/1000000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (67/256:ℝ) (17/64:ℝ)
    (3690765/13997056:ℝ) (1112778596561/100000000000000:ℝ) (88261133131181809/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_067
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0404).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^2*thetaFirstMode x) ≤ (3022239903050270873/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (67/256:ℝ) (17/64:ℝ)
    (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ) (88261133131181809/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_067 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_068 :
    (1495500630856722261/500000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (17/64:ℝ) (69/256:ℝ)
    (3857235/14414848:ℝ) (106936343329/10000000000000:ℝ) (107998327769847/125000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_068
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0410).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^2*thetaFirstMode x) ≤ (299102007890508779/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (17/64:ℝ) (69/256:ℝ)
    (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ) (107998327769847/125000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_068 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_069 :
    (2957873534902526701/1000000000000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (69/256:ℝ) (35/128:ℝ)
    (4028637/14838784:ℝ) (1027305643347/100000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_069
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0416).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^2*thetaFirstMode x) ≤ (2957892506851474779/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (69/256:ℝ) (35/128:ℝ)
    (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_069 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_070 :
    (2922936939052788551/1000000000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (35/128:ℝ) (71/256:ℝ)
    (4205043/15268864:ℝ) (493288154281/50000000000000:ℝ) (103376351291781417/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_070
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0422).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^2*thetaFirstMode x) ≤ (584591210727206279/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (35/128:ℝ) (71/256:ℝ)
    (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_070 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_071 :
    (577258140990890103/200000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (71/256:ℝ) (9/32:ℝ)
    (4386525/15705088:ℝ) (947146656921/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_071
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0428).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^2*thetaFirstMode x) ≤ (1443154974965310847/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (71/256:ℝ) (9/32:ℝ)
    (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_071 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_072 :
    (11392136764947549/4000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (9/32:ℝ) (73/256:ℝ)
    (4573155/16147456:ℝ) (227247019309/25000000000000:ℝ) (24701951795471107/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_072
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0434).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^2*thetaFirstMode x) ≤ (71201338856814611/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (9/32:ℝ) (73/256:ℝ)
    (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (24701951795471107/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_072 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_073 :
    (1404133328757858389/500000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (73/256:ℝ) (37/128:ℝ)
    (4765005/16595968:ℝ) (21801803337/2500000000000:ℝ) (386185615014076073/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_073
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0440).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^2*thetaFirstMode x) ≤ (561657225234586169/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (73/256:ℝ) (37/128:ℝ)
    (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ) (386185615014076073/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_073 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_074 :
    (691771761673957639/250000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (37/128:ℝ) (75/256:ℝ)
    (4962147/17050624:ℝ) (836370578727/100000000000000:ℝ) (75441357932300963/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_074
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0446).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^2*thetaFirstMode x) ≤ (1383553304243233191/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (37/128:ℝ) (75/256:ℝ)
    (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_074 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_075 :
    (272459377679349143/100000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (75/256:ℝ) (19/64:ℝ)
    (5164653/17511424:ℝ) (801855368771/100000000000000:ℝ) (23018684593509581/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_075
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0452).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^2*thetaFirstMode x) ≤ (2724613419154965127/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (75/256:ℝ) (19/64:ℝ)
    (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ) (23018684593509581/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_075 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_076 :
    (670221135510662697/250000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (19/64:ℝ) (77/256:ℝ)
    (5372595/17978368:ℝ) (153699735063/20000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_076
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0458).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^2*thetaFirstMode x) ≤ (670226063101034953/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (19/64:ℝ) (77/256:ℝ)
    (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_076 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_077 :
    (1318028061836155109/500000000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (77/256:ℝ) (39/128:ℝ)
    (5586045/18451456:ℝ) (36813644941/5000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_077
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0464).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^2*thetaFirstMode x) ≤ (1318037944718618253/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (77/256:ℝ) (39/128:ℝ)
    (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_077 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_078 :
    (80943881564599967/31250000000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (39/128:ℝ) (79/256:ℝ)
    (5805075/18930688:ℝ) (352575340453/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_078
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0470).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^2*thetaFirstMode x) ≤ (2590224018651364757/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (39/128:ℝ) (79/256:ℝ)
    (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_078 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_079 :
    (1271711613314056593/500000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (79/256:ℝ) (5/16:ℝ)
    (6029757/19416064:ℝ) (337552458191/50000000000000:ℝ) (166728513122296977/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_079
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0476).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^2*thetaFirstMode x) ≤ (2543443065468384017/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (79/256:ℝ) (5/16:ℝ)
    (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ) (166728513122296977/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_079 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_080 :
    (2495806175155244391/1000000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (5/16:ℝ) (81/256:ℝ)
    (6260163/19907584:ℝ) (646108764843/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_080
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0482).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^2*thetaFirstMode x) ≤ (623956507931994077/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (5/16:ℝ) (81/256:ℝ)
    (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_080 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_081 :
    (1223722241383468843/500000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (81/256:ℝ) (41/128:ℝ)
    (6496365/20405248:ℝ) (123627132367/20000000000000:ℝ) (126624657912986459/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_081
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0488).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^2*thetaFirstMode x) ≤ (61186608615224617/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (81/256:ℝ) (41/128:ℝ)
    (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ) (126624657912986459/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_081 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_082 :
    (479685572082715637/200000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (41/128:ℝ) (83/256:ℝ)
    (6738435/20909056:ℝ) (147789832401/25000000000000:ℝ) (154128683512619971/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_082
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0494).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^2*thetaFirstMode x) ≤ (2398447715138960799/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (41/128:ℝ) (83/256:ℝ)
    (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_082 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_083 :
    (36700690169257257/15625000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (83/256:ℝ) (21/64:ℝ)
    (6986445/21419008:ℝ) (282576893697/50000000000000:ℝ) (300052897882409501/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_083
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0500).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^2*thetaFirstMode x) ≤ (14680400038447041/6250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (83/256:ℝ) (21/64:ℝ)
    (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ) (300052897882409501/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_083 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_084 :
    (229877930595202287/100000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (21/64:ℝ) (85/256:ℝ)
    (7240467/21935104:ℝ) (540093361307/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_084
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0506).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^2*thetaFirstMode x) ≤ (2298799109676720441/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (21/64:ℝ) (85/256:ℝ)
    (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_084 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_085 :
    (2248317073609733271/1000000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (85/256:ℝ) (43/128:ℝ)
    (7500573/22457344:ℝ) (257976346853/50000000000000:ℝ) (56791022721725001/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_085
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0512).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^2*thetaFirstMode x) ≤ (1124168416850695389/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (85/256:ℝ) (43/128:ℝ)
    (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ) (56791022721725001/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_085 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_086 :
    (274692386698411033/125000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (43/128:ℝ) (87/256:ℝ)
    (7766835/22985728:ℝ) (24635337609/5000000000000:ℝ) (55213458929619209/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_086
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0518).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^2*thetaFirstMode x) ≤ (439511759625796581/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (43/128:ℝ) (87/256:ℝ)
    (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_086 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_087 :
    (1073262351335337461/500000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (87/256:ℝ) (11/32:ℝ)
    (8039325/23520256:ℝ) (18813233521/4000000000000:ℝ) (536580549127126453/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_087
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0524).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^2*thetaFirstMode x) ≤ (268318042488348677/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (87/256:ℝ) (11/32:ℝ)
    (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (536580549127126453/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_087 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_088 :
    (1047675434407037371/500000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (11/32:ℝ) (89/256:ℝ)
    (8318115/24060928:ℝ) (224400297143/50000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_088
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0530).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^2*thetaFirstMode x) ≤ (1047685213587315213/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (11/32:ℝ) (89/256:ℝ)
    (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_088 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_089 :
    (1022046057073037907/500000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (89/256:ℝ) (45/128:ℝ)
    (8603277/24607744:ℝ) (428092013329/100000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_089
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0536).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^2*thetaFirstMode x) ≤ (2044111582247427969/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (89/256:ℝ) (45/128:ℝ)
    (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_089 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_090 :
    (1992820446651724469/1000000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (45/128:ℝ) (91/256:ℝ)
    (8894883/25160704:ℝ) (20409072197/5000000000000:ℝ) (245647015792921217/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_090
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0542).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^2*thetaFirstMode x) ≤ (398567962664732081/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (45/128:ℝ) (91/256:ℝ)
    (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_090 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_091 :
    (1941605300455800203/1000000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (91/256:ℝ) (23/64:ℝ)
    (9193005/25719808:ℝ) (38904559797/10000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_091
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0548).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^2*thetaFirstMode x) ≤ (970812277373916701/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (91/256:ℝ) (23/64:ℝ)
    (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_091 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_092 :
    (236314185554937937/125000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (23/64:ℝ) (93/256:ℝ)
    (9497715/26285056:ℝ) (370661556507/100000000000000:ℝ) (231145058214661231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_092
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0554).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^2*thetaFirstMode x) ≤ (1890532615613435683/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (23/64:ℝ) (93/256:ℝ)
    (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ) (231145058214661231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_092 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_093 :
    (1839609138969001579/1000000000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (93/256:ℝ) (47/128:ℝ)
    (9809085/26856448:ℝ) (353006775571/100000000000000:ℝ) (224077469909545329/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_093
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0560).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^2*thetaFirstMode x) ≤ (367925627311380323/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (93/256:ℝ) (47/128:ℝ)
    (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ) (224077469909545329/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_093 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_094 :
    (1788953700697291401/1000000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (47/128:ℝ) (95/256:ℝ)
    (10127187/27433984:ℝ) (168029545683/50000000000000:ℝ) (217134160115492507/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_094
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0566).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^2*thetaFirstMode x) ≤ (447243138621655851/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (47/128:ℝ) (95/256:ℝ)
    (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ) (217134160115492507/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_094 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_095 :
    (1738605875013233183/1000000000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (95/256:ℝ) (3/8:ℝ)
    (10452093/28017664:ℝ) (319796725049/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_095
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0572).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^2*thetaFirstMode x) ≤ (1738624575058859589/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (95/256:ℝ) (3/8:ℝ)
    (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_095 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

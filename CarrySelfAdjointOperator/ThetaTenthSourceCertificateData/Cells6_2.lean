import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature2

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_064 :
    (6253594299008659/500000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (1/4:ℝ) (65/256:ℝ)
    (260188853259783/1032563465259008:ℝ) (1251209358709/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_064
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0388).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^6*thetaFirstMode x) ≤ (6253630699637767/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (1/4:ℝ) (65/256:ℝ)
    (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_064 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_065 :
    (13194194826142151/1000000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (65/256:ℝ) (33/128:ℝ)
    (289770553653497/1132406395762688:ℝ) (601779286253/50000000000000:ℝ) (184017103411496703/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_065
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0394).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x) ≤ (13194273111253733/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (65/256:ℝ) (33/128:ℝ)
    (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ) (184017103411496703/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_065 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_066 :
    (13895042431885553/1000000000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (33/128:ℝ) (67/256:ℝ)
    (322189499008615/1240168251938816:ℝ) (1157352154767/100000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_066
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0400).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^6*thetaFirstMode x) ≤ (277902529464499/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (33/128:ℝ) (67/256:ℝ)
    (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_066 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_067 :
    (14608569403455443/1000000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (67/256:ℝ) (17/64:ℝ)
    (357668934677145/1356343732447232:ℝ) (278140215523/25000000000000:ℝ) (88261133131181809/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_067
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0406).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x) ≤ (7304329738475223/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (67/256:ℝ) (17/64:ℝ)
    (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ) (88261133131181809/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_067 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_068 :
    (15333544306578437/1000000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (17/64:ℝ) (69/256:ℝ)
    (396445943426855/1481450361153536:ℝ) (1069155550087/100000000000000:ℝ) (107998327769847/125000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_068
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0412).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^6*thetaFirstMode x) ≤ (3833410172775011/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (17/64:ℝ) (69/256:ℝ)
    (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ) (107998327769847/125000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_068 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_069 :
    (3213734029270911/200000000000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (69/256:ℝ) (35/128:ℝ)
    (438772078999513/1616029178697728:ℝ) (1027107189069/100000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_069
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0418).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x) ≤ (803438656158197/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (69/256:ℝ) (35/128:ℝ)
    (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_069 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_070 :
    (8406294280967599/500000000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (35/128:ℝ) (71/256:ℝ)
    (484914018720327/1760645444384768:ℝ) (197277375897/20000000000000:ℝ) (103376351291781417/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_070
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0424).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^6*thetaFirstMode x) ≤ (3362539682772689/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (35/128:ℝ) (71/256:ℝ)
    (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_070 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_071 :
    (4390971083000119/250000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (71/256:ℝ) (9/32:ℝ)
    (535154235440825/1915889348397056:ℝ) (946965866963/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_071
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0430).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x) ≤ (17564001342909693/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (71/256:ℝ) (9/32:ℝ)
    (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_071 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_072 :
    (18321090169658913/1000000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (9/32:ℝ) (73/256:ℝ)
    (589791689097415/2082376734328832:ℝ) (908815557063/100000000000000:ℝ) (24701951795471107/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_072
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0436).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^6*thetaFirstMode x) ≤ (9160607311768727/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (9/32:ℝ) (73/256:ℝ)
    (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (24701951795471107/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_072 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_073 :
    (19082691781552571/1000000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (73/256:ℝ) (37/128:ℝ)
    (649142538167865/2260749832042496:ℝ) (871907529641/100000000000000:ℝ) (386185615014076073/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_073
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0442).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x) ≤ (4770705990477047/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (73/256:ℝ) (37/128:ℝ)
    (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ) (386185615014076073/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_073 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_074 :
    (19847133167121193/1000000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (37/128:ℝ) (75/256:ℝ)
    (713540871307943/2451678000846848:ℝ) (209053388221/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_074
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0448).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^6*thetaFirstMode x) ≤ (4961818338997227/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (37/128:ℝ) (75/256:ℝ)
    (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_074 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_075 :
    (10306411065134227/500000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (75/256:ℝ) (19/64:ℝ)
    (783339459450457/2655858482997248:ℝ) (100213199617/12500000000000:ℝ) (23018684593509581/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_075
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0454).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x) ≤ (10306485303796221/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (75/256:ℝ) (19/64:ℝ)
    (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ) (23018684593509581/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_075 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_076 :
    (21378135977702823/1000000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (19/64:ℝ) (77/256:ℝ)
    (858910528648935/2874017167517696:ℝ) (768355847181/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_076
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0460).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^6*thetaFirstMode x) ≤ (21378293020242531/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (19/64:ℝ) (77/256:ℝ)
    (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_076 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_077 :
    (691919605430207/31250000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (77/256:ℝ) (39/128:ℝ)
    (940646553948185/3106909364344832:ℝ) (736136717087/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_077
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0466).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x) ≤ (11070796627279263/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (77/256:ℝ) (39/128:ℝ)
    (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_077 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_078 :
    (715657197651907/31250000000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (39/128:ℝ) (79/256:ℝ)
    (1028961074563975/3355320588793856:ℝ) (705020860683/100000000000000:ℝ) (342041472533647013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_078
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0472).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^6*thetaFirstMode x) ≤ (4580241062432377/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (39/128:ℝ) (79/256:ℝ)
    (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_078 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_079 :
    (2956908282877369/125000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (79/256:ℝ) (5/16:ℝ)
    (1124289530654073/3620067356346368:ℝ) (168745296153/25000000000000:ℝ) (166728513122296977/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_079
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0478).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x) ≤ (23655450619337433/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (79/256:ℝ) (5/16:ℝ)
    (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ) (166728513122296977/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_079 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_080 :
    (24402450199010551/1000000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (5/16:ℝ) (81/256:ℝ)
    (1227090121962887/3901997987760128:ℝ) (322995429879/50000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_080
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0484).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^6*thetaFirstMode x) ≤ (24402644180350189/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (5/16:ℝ) (81/256:ℝ)
    (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_080 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_081 :
    (5028179383101973/200000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (81/256:ℝ) (41/128:ℝ)
    (1337844688621945/4201993424500736:ℝ) (618023332451/100000000000000:ℝ) (126624657912986459/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_081
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0490).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^6*thetaFirstMode x) ≤ (25141100770347431/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (81/256:ℝ) (41/128:ℝ)
    (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ) (126624657912986459/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_081 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_082 :
    (25868927170421091/1000000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (41/128:ℝ) (83/256:ℝ)
    (1457059614388455/4520968054495232:ℝ) (591052335239/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_082
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0496).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^6*thetaFirstMode x) ≤ (12934570569426329/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (41/128:ℝ) (83/256:ℝ)
    (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_082 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_083 :
    (1329243694023147/50000000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (83/256:ℝ) (21/64:ℝ)
    (1585266752604185/4859870548207616:ℝ) (113010379443/20000000000000:ℝ) (300052897882409501/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_083
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0502).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^6*thetaFirstMode x) ≤ (26585098193306107/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (83/256:ℝ) (21/64:ℝ)
    (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ) (300052897882409501/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_083 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_084 :
    (1091483530244093/40000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (21/64:ℝ) (85/256:ℝ)
    (1723024375156903/5219684705036288:ℝ) (33749772119/6250000000000:ℝ) (291951206062636471/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_084
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0508).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^6*thetaFirstMode x) ≤ (27287323133750533/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (21/64:ℝ) (85/256:ℝ)
    (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_084 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_085 :
    (13986972928986091/500000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (85/256:ℝ) (43/128:ℝ)
    (1870918144726617/5601430310033408:ℝ) (128965089171/25000000000000:ℝ) (56791022721725001/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_085
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0514).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^6*thetaFirstMode x) ≤ (2797419150999811/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (85/256:ℝ) (43/128:ℝ)
    (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ) (56791022721725001/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_085 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_086 :
    (7160963137089103/250000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (43/128:ℝ) (87/256:ℝ)
    (2029562110598855/6006164000946176:ℝ) (19704755271/4000000000000:ℝ) (55213458929619209/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_086
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0520).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^6*thetaFirstMode x) ≤ (28644109172157359/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (43/128:ℝ) (87/256:ℝ)
    (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_086 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_087 :
    (14647625154030307/500000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (87/256:ℝ) (11/32:ℝ)
    (2199599728327225/6434980145580032:ℝ) (470247238747/100000000000000:ℝ) (536580549127126453/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_087
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0526).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^6*thetaFirstMode x) ≤ (29295518087904709/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (87/256:ℝ) (11/32:ℝ)
    (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (536580549127126453/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_087 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_088 :
    (14963311446601989/500000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (11/32:ℝ) (89/256:ℝ)
    (2381704903527495/6889011729483776:ℝ) (44872107857/10000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_088
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0532).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^6*thetaFirstMode x) ≤ (29926901999739857/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (11/32:ℝ) (89/256:ℝ)
    (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_088 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_089 :
    (30536501306711451/1000000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (89/256:ℝ) (45/128:ℝ)
    (2576583060085433/7369431253956608:ℝ) (428016401207/100000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_089
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0538).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^6*thetaFirstMode x) ≤ (6107358379205973/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (89/256:ℝ) (45/128:ℝ)
    (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_089 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_090 :
    (3112346905955583/100000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (45/128:ℝ) (91/256:ℝ)
    (2784972233060647/7877451644377088:ℝ) (204054781369/50000000000000:ℝ) (245647015792921217/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_090
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0544).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^6*thetaFirstMode x) ≤ (15561885636010921/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (45/128:ℝ) (91/256:ℝ)
    (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_090 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_091 :
    (31686167197816891/1000000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (91/256:ℝ) (23/64:ℝ)
    (3007644186568665/8414327168854016:ℝ) (77795456401/20000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_091
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0550).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^6*thetaFirstMode x) ≤ (31686481157694531/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (91/256:ℝ) (23/64:ℝ)
    (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_091 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_092 :
    (16111649537918541/500000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (23/64:ℝ) (93/256:ℝ)
    (3245405556923495/8981354367199232:ℝ) (185298323403/50000000000000:ℝ) (231145058214661231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_092
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0556).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^6*thetaFirstMode x) ≤ (16111812445109521/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (23/64:ℝ) (93/256:ℝ)
    (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ) (231145058214661231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_092 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_093 :
    (32733634853198277/1000000000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (93/256:ℝ) (47/128:ℝ)
    (3499099021322905/9579872990222336:ℝ) (35294511961/10000000000000:ℝ) (224077469909545329/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_093
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0562).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^6*thetaFirstMode x) ≤ (32733972611462233/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (93/256:ℝ) (47/128:ℝ)
    (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ) (224077469909545329/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_093 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_094 :
    (16608007848979343/500000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (47/128:ℝ) (95/256:ℝ)
    (3769604492358663/10211266949347328:ℝ) (33600054281/10000000000000:ℝ) (217134160115492507/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_094
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0568).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^6*thetaFirstMode x) ≤ (3321636547102601/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (47/128:ℝ) (95/256:ℝ)
    (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ) (217134160115492507/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_094 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_095 :
    (1346774307151449/40000000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (95/256:ℝ) (3/8:ℝ)
    (4057840338633977/10876965276551168:ℝ) (319741143511/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_095
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0574).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^6*thetaFirstMode x) ≤ (2104357469889959/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (95/256:ℝ) (3/8:ℝ)
    (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_095 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

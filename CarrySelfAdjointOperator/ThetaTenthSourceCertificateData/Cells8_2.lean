import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature2

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_064 :
    (794088453857029/1000000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (1/4:ℝ) (65/256:ℝ)
    (1740175468704392841/6905636680726120960:ℝ) (312771103803/25000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_064
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0389).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^8*thetaFirstMode x) ≤ (397046536891349/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (1/4:ℝ) (65/256:ℝ)
    (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_064 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_065 :
    (863877435948259/1000000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (65/256:ℝ) (33/128:ℝ)
    (1998562918031146359/7809963970327836160:ℝ) (601719622347/50000000000000:ℝ) (184017103411496703/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_065
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0395).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^8*thetaFirstMode x) ≤ (431941279545377/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (65/256:ℝ) (33/128:ℝ)
    (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ) (184017103411496703/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_065 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_066 :
    (468874739827483/500000000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (33/128:ℝ) (67/256:ℝ)
    (2290508312768691057/8816267219187228160:ℝ) (578619100303/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_066
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0401).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^8*thetaFirstMode x) ≤ (937755148687177/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (33/128:ℝ) (67/256:ℝ)
    (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_066 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_067 :
    (1015771577069191/1000000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (67/256:ℝ) (17/64:ℝ)
    (523953028089808515/1986849740868925952:ℝ) (222490410103/20000000000000:ℝ) (88261133131181809/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_067
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0407).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^8*thetaFirstMode x) ≤ (507888918540211/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (67/256:ℝ) (17/64:ℝ)
    (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ) (88261133131181809/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_067 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_068 :
    (1097998638413603/1000000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (17/64:ℝ) (69/256:ℝ)
    (2990441164477942593/11174368100215452160:ℝ) (534525830191/50000000000000:ℝ) (107998327769847/125000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_068
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0413).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^8*thetaFirstMode x) ≤ (219601107391219/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (17/64:ℝ) (69/256:ℝ)
    (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ) (107998327769847/125000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_068 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_069 :
    (1184472691280757/1000000000000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (69/256:ℝ) (35/128:ℝ)
    (3407025864107161791/12547889060924853760:ℝ) (513504005171/50000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_069
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0419).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^8*thetaFirstMode x) ≤ (1184480278384469/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (69/256:ℝ) (35/128:ℝ)
    (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_069 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_070 :
    (637611061381551/500000000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (35/128:ℝ) (71/256:ℝ)
    (3874419549088930809/14066927919229519360:ℝ) (986292210119/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_070
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0425).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^8*thetaFirstMode x) ≤ (159403806370877/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (35/128:ℝ) (71/256:ℝ)
    (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_070 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_071 :
    (1370260970432819/1000000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (71/256:ℝ) (9/32:ℝ)
    (4397964224531456007/15744504565196700160:ℝ) (946875514151/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_071
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0431).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^8*thetaFirstMode x) ≤ (685135047394653/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (71/256:ℝ) (9/32:ℝ)
    (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_071 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_072 :
    (1469588267768477/1000000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (9/32:ℝ) (73/256:ℝ)
    (996695256742326405/3518919113747927552:ℝ) (181745867269/20000000000000:ℝ) (24701951795471107/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_072
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0437).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^8*thetaFirstMode x) ≤ (45924945182693/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (9/32:ℝ) (73/256:ℝ)
    (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (24701951795471107/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_072 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_073 :
    (393296862371847/250000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (73/256:ℝ) (37/128:ℝ)
    (5637281108870877543/19632189611037468160:ℝ) (871825264493/100000000000000:ℝ) (386185615014076073/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_073
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0443).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^8*thetaFirstMode x) ≤ (157319834135863/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (73/256:ℝ) (37/128:ℝ)
    (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ) (386185615014076073/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_073 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_074 :
    (420256455466797/250000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (37/128:ℝ) (75/256:ℝ)
    (6366249662322494241/21873345290796674560:ℝ) (104516884289/12500000000000:ℝ) (75441357932300963/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_074
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0449).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^8*thetaFirstMode x) ≤ (1681037690091029/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (37/128:ℝ) (75/256:ℝ)
    (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_074 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_075 :
    (1793054102877379/1000000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (75/256:ℝ) (19/64:ℝ)
    (7177837152534081759/24335251372240130560:ℝ) (801630743121/100000000000000:ℝ) (23018684593509581/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_075
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0455).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^8*thetaFirstMode x) ≤ (448266753114571/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (75/256:ℝ) (19/64:ℝ)
    (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ) (23018684593509581/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_075 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_076 :
    (954603018239953/500000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (19/64:ℝ) (77/256:ℝ)
    (8080123862216333457/27036289542638748160:ℝ) (192071115779/25000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_076
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0461).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^8*thetaFirstMode x) ≤ (1909220054837913/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (19/64:ℝ) (77/256:ℝ)
    (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_076 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_077 :
    (2029398085168327/1000000000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (77/256:ℝ) (39/128:ℝ)
    (1816371645569997795/5999219949625943552:ℝ) (736068654267/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_077
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0467).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^8*thetaFirstMode x) ≤ (253676660260151/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (77/256:ℝ) (39/128:ℝ)
    (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_077 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_078 :
    (2153529204248073/1000000000000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (39/128:ℝ) (79/256:ℝ)
    (10192502262515829993/33235648177494300160:ℝ) (704955976797/100000000000000:ℝ) (342041472533647013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_078
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0473).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^8*thetaFirstMode x) ≤ (2153545651772567/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (39/128:ℝ) (79/256:ℝ)
    (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_078 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_079 :
    (2281480700994133/1000000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (79/256:ℝ) (5/16:ℝ)
    (11422279416358375191/36777297964497103360:ℝ) (337459671627/50000000000000:ℝ) (166728513122296977/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_079
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0479).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^8*thetaFirstMode x) ≤ (285187309172977/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (79/256:ℝ) (5/16:ℝ)
    (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ) (166728513122296977/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_079 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_080 :
    (1206558090631249/500000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (5/16:ℝ) (81/256:ℝ)
    (12782224971512359209/40644882680317749760:ℝ) (322965965079/50000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_080
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0485).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^8*thetaFirstMode x) ≤ (301641919360713/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (5/16:ℝ) (81/256:ℝ)
    (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_080 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_081 :
    (1274140792829713/500000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (81/256:ℝ) (41/128:ℝ)
    (14284239070852168407/44863782688534812160:ℝ) (617967189223/100000000000000:ℝ) (126624657912986459/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_081
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0491).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^8*thetaFirstMode x) ≤ (63707555971829/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (81/256:ℝ) (41/128:ℝ)
    (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ) (126624657912986459/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_081 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_082 :
    (1343402658395189/500000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (41/128:ℝ) (83/256:ℝ)
    (3188228496497630685/9892200887210173952:ℝ) (29549942907/5000000000000:ℝ) (154128683512619971/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_082
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0497).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^8*thetaFirstMode x) ≤ (2686827529829191/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (41/128:ℝ) (83/256:ℝ)
    (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_082 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_083 :
    (2828498458591181/1000000000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (83/256:ℝ) (21/64:ℝ)
    (17766735204530144943/54465262754276508160:ℝ) (565000970919/100000000000000:ℝ) (300052897882409501/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_083
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0503).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^8*thetaFirstMode x) ≤ (1414261156716769/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (83/256:ℝ) (21/64:ℝ)
    (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ) (300052897882409501/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_083 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_084 :
    (2973155088199437/1000000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (21/64:ℝ) (85/256:ℝ)
    (19775858017267564641/59907066245820060160:ℝ) (53994786779/10000000000000:ℝ) (291951206062636471/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_084
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0509).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^8*thetaFirstMode x) ≤ (1486590334192631/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (21/64:ℝ) (85/256:ℝ)
    (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_084 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_085 :
    (3120552680090323/1000000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (85/256:ℝ) (43/128:ℝ)
    (21984457092577248159/65818805832858856960:ℝ) (515814204633/100000000000000:ℝ) (56791022721725001/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_085
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0515).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^8*thetaFirstMode x) ≤ (3120580070616149/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (85/256:ℝ) (43/128:ℝ)
    (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ) (56791022721725001/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_085 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_086 :
    (1635226300999999/500000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (43/128:ℝ) (87/256:ℝ)
    (24409651773064480857/72234846544296732160:ℝ) (492574961981/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_086
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0521).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^8*thetaFirstMode x) ≤ (654096377815563/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (43/128:ℝ) (87/256:ℝ)
    (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_086 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_087 :
    (1711300350506857/500000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (87/256:ℝ) (11/32:ℝ)
    (5413961127233958075/15838324523948298752:ℝ) (117551363383/25000000000000:ℝ) (536580549127126453/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_087
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0527).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^8*thetaFirstMode x) ≤ (3422631971892817/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (87/256:ℝ) (11/32:ℝ)
    (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (536580549127126453/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_087 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_088 :
    (357672797819207/100000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (11/32:ℝ) (89/256:ℝ)
    (29984600961233742393/86727736009265052160:ℝ) (89736266843/20000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_088
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0533).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^8*thetaFirstMode x) ≤ (3576761320979203/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (11/32:ℝ) (89/256:ℝ)
    (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_088 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_089 :
    (933137837303219/250000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (89/256:ℝ) (45/128:ℝ)
    (33175116720304347591/94884058348837864960:ℝ) (42797860779/10000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_089
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0539).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^8*thetaFirstMode x) ≤ (3732586852632673/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (89/256:ℝ) (45/128:ℝ)
    (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_089 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_090 :
    (972443621990393/250000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (45/128:ℝ) (91/256:ℝ)
    (36663910216296708609/103703836492258332160:ℝ) (408073633973/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_090
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0545).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^8*thetaFirstMode x) ≤ (3889812241134897/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (45/128:ℝ) (91/256:ℝ)
    (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_090 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_091 :
    (4048088749677267/1000000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (91/256:ℝ) (23/64:ℝ)
    (40475102494972215807/113232801681326748160:ℝ) (388943135103/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_091
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0551).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^8*thetaFirstMode x) ≤ (4048128841855853/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (91/256:ℝ) (23/64:ℝ)
    (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_091 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_092 :
    (4207174169435811/1000000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (23/64:ℝ) (93/256:ℝ)
    (8926893532018987965/24703856487388477952:ℝ) (370564202331/100000000000000:ℝ) (231145058214661231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_092
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0557).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^8*thetaFirstMode x) ≤ (2103608344868647/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (23/64:ℝ) (93/256:ℝ)
    (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ) (231145058214661231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_092 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_093 :
    (174668021260593/40000000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (93/256:ℝ) (47/128:ℝ)
    (49169526224045867343/134614321254731292160:ℝ) (11028571917/3125000000000:ℝ) (224077469909545329/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_093
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0563).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^8*thetaFirstMode x) ≤ (436674556869587/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (93/256:ℝ) (47/128:ℝ)
    (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ) (224077469909545329/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_093 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_094 :
    (4526328504677781/1000000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (47/128:ℝ) (95/256:ℝ)
    (54109642629131284041/146571795189741237760:ℝ) (83992819407/25000000000000:ℝ) (217134160115492507/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_094
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0569).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^8*thetaFirstMode x) ≤ (905275229364807/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (47/128:ℝ) (95/256:ℝ)
    (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ) (217134160115492507/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_094 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_095 :
    (4685710837735137/1000000000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (95/256:ℝ) (3/8:ℝ)
    (59486127077809925559/159448540415669455360:ℝ) (39964170157/12500000000000:ℝ) (52579114235318267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_095
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0575).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^8*thetaFirstMode x) ≤ (468576117198911/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (95/256:ℝ) (3/8:ℝ)
    (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_095 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

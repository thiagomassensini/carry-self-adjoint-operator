import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature2

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_0_064 :
    (6111543628117409193/125000000000000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (1/4:ℝ) (65/256:ℝ)
    (129/512:ℝ) (1251584440439/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_064
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0385).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^0*thetaFirstMode x) ≤ (48892633969144890411/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (1/4:ℝ) (65/256:ℝ)
    (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ) (938914864620939517/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_064 (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_065 :
    (5878785583543787463/125000000000000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (65/256:ℝ) (33/128:ℝ)
    (131/512:ℝ) (37622399689/3125000000000:ℝ) (184017103411496703/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_065
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0391).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^0*thetaFirstMode x) ≤ (47030564059803306841/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (65/256:ℝ) (33/128:ℝ)
    (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ) (184017103411496703/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_065 (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_066 :
    (45224669512071821429/1000000000000000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (33/128:ℝ) (67/256:ℝ)
    (133/512:ℝ) (115769423549/10000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_066
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0397).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^0*thetaFirstMode x) ≤ (22612471691893022321/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (33/128:ℝ) (67/256:ℝ)
    (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ) (901314286011735199/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_066 (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_067 :
    (43474359972078232313/1000000000000000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (67/256:ℝ) (17/64:ℝ)
    (135/512:ℝ) (69555468773/6250000000000:ℝ) (88261133131181809/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_067
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0403).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^0*thetaFirstMode x) ≤ (2717164272407457289/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (67/256:ℝ) (17/64:ℝ)
    (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ) (88261133131181809/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_067 (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_068 :
    (20889108200841499239/500000000000000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (17/64:ℝ) (69/256:ℝ)
    (137/512:ℝ) (1069467409093/100000000000000:ℝ) (107998327769847/125000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_068
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0409).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^0*thetaFirstMode x) ≤ (20889239669557235897/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (17/64:ℝ) (69/256:ℝ)
    (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ) (107998327769847/125000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_068 (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_069 :
    (31355549766504329/781250000000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (69/256:ℝ) (35/128:ℝ)
    (139/512:ℝ) (102740490249/10000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_069
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0415).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^0*thetaFirstMode x) ≤ (1003384030676144819/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (69/256:ℝ) (35/128:ℝ)
    (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ) (845449928069915711/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_069 (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_070 :
    (308351135307275127/8000000000000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (35/128:ℝ) (71/256:ℝ)
    (141/512:ℝ) (246667763263/25000000000000:ℝ) (103376351291781417/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_070
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0421).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^0*thetaFirstMode x) ≤ (38544144067224187/1000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (35/128:ℝ) (71/256:ℝ)
    (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ) (103376351291781417/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_070 (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_071 :
    (9250864202535088077/250000000000000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (71/256:ℝ) (9/32:ℝ)
    (143/512:ℝ) (473618539969/50000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_071
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0427).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^0*thetaFirstMode x) ≤ (4625462954066474423/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (71/256:ℝ) (9/32:ℝ)
    (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ) (808678613472023763/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_071 (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_072 :
    (35512680462249370503/1000000000000000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (9/32:ℝ) (73/256:ℝ)
    (145/512:ℝ) (14204286931/1562500000000:ℝ) (24701951795471107/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_072
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0433).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^0*thetaFirstMode x) ≤ (35512921995364540243/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (9/32:ℝ) (73/256:ℝ)
    (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ) (24701951795471107/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_072 (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_073 :
    (34070451798410960813/1000000000000000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (73/256:ℝ) (37/128:ℝ)
    (147/512:ℝ) (872154459999/100000000000000:ℝ) (386185615014076073/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_073
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0439).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^0*thetaFirstMode x) ≤ (34070688085912453373/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (73/256:ℝ) (37/128:ℝ)
    (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ) (386185615014076073/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_073 (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_074 :
    (3267566714943892829/100000000000000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (37/128:ℝ) (75/256:ℝ)
    (149/512:ℝ) (418224557351/50000000000000:ℝ) (75441357932300963/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_074
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0445).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^0*thetaFirstMode x) ≤ (1633794911821732171/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (37/128:ℝ) (75/256:ℝ)
    (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ) (75441357932300963/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_074 (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_075 :
    (31327230778308378027/1000000000000000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (75/256:ℝ) (19/64:ℝ)
    (151/512:ℝ) (801930276291/100000000000000:ℝ) (23018684593509581/31250000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_075
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0451).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^0*thetaFirstMode x) ≤ (15663728355636934473/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (75/256:ℝ) (19/64:ℝ)
    (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ) (23018684593509581/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_075 (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_076 :
    (3002405539553019283/100000000000000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (19/64:ℝ) (77/256:ℝ)
    (153/512:ℝ) (768570109637/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_076
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0457).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^0*thetaFirstMode x) ≤ (30024276222201333089/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (19/64:ℝ) (77/256:ℝ)
    (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ) (718932361707831433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_076 (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_077 :
    (14382531329470078343/500000000000000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (77/256:ℝ) (39/128:ℝ)
    (155/512:ℝ) (736341008679/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_077
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0463).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^0*thetaFirstMode x) ≤ (1797829901780429633/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (77/256:ℝ) (39/128:ℝ)
    (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ) (701424832893595261/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_077 (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_078 :
    (27549183658216151629/1000000000000000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (39/128:ℝ) (79/256:ℝ)
    (157/512:ℝ) (176303902207/25000000000000:ℝ) (342041472533647013/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_078
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0469).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^0*thetaFirstMode x) ≤ (27549394421165352991/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (39/128:ℝ) (79/256:ℝ)
    (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ) (342041472533647013/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_078 (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_079 :
    (13187679691963684047/500000000000000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (79/256:ℝ) (5/16:ℝ)
    (159/512:ℝ) (27006671959/4000000000000:ℝ) (166728513122296977/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_079
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0475).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^0*thetaFirstMode x) ≤ (13187782595945678781/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (79/256:ℝ) (5/16:ℝ)
    (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ) (166728513122296977/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_079 (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_080 :
    (3155317647429513067/125000000000000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (5/16:ℝ) (81/256:ℝ)
    (161/512:ℝ) (32308386653/5000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_080
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0481).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^0*thetaFirstMode x) ≤ (6310685521346400857/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (5/16:ℝ) (81/256:ℝ)
    (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ) (649925234224416177/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_080 (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_081 :
    (2414969117690202269/100000000000000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (81/256:ℝ) (41/128:ℝ)
    (163/512:ℝ) (309095920617/50000000000000:ℝ) (126624657912986459/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_081
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0487).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^0*thetaFirstMode x) ≤ (2414988723496548587/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (81/256:ℝ) (41/128:ℝ)
    (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ) (126624657912986459/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_081 (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_082 :
    (23095782716334765553/1000000000000000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (41/128:ℝ) (83/256:ℝ)
    (165/512:ℝ) (591212840587/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_082
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0493).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^0*thetaFirstMode x) ≤ (2886996747725390643/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (41/128:ℝ) (83/256:ℝ)
    (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ) (154128683512619971/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_082 (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_083 :
    (2759975093437352683/125000000000000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (83/256:ℝ) (21/64:ℝ)
    (167/512:ℝ) (565204745437/100000000000000:ℝ) (300052897882409501/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_083
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0499).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^0*thetaFirstMode x) ≤ (22079987276682044571/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (83/256:ℝ) (21/64:ℝ)
    (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ) (300052897882409501/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_083 (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_084 :
    (21100742214163363359/1000000000000000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (21/64:ℝ) (85/256:ℝ)
    (169/512:ℝ) (540141877167/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_084
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0505).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^0*thetaFirstMode x) ≤ (21100924064524835781/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (21/64:ℝ) (85/256:ℝ)
    (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ) (291951206062636471/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_084 (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_085 :
    (20157616421595628981/1000000000000000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (85/256:ℝ) (43/128:ℝ)
    (171/512:ℝ) (515998873633/100000000000000:ℝ) (56791022721725001/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_085
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0511).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^0*thetaFirstMode x) ≤ (20157793651632960787/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (85/256:ℝ) (43/128:ℝ)
    (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ) (56791022721725001/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_085 (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_086 :
    (3849889077123443381/200000000000000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (43/128:ℝ) (87/256:ℝ)
    (173/512:ℝ) (4927506981/1000000000000:ℝ) (55213458929619209/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_086
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0517).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^0*thetaFirstMode x) ≤ (962480902738082997/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (43/128:ℝ) (87/256:ℝ)
    (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ) (55213458929619209/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_086 (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_087 :
    (18375264163967150267/1000000000000000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (87/256:ℝ) (11/32:ℝ)
    (175/512:ℝ) (18814905909/4000000000000:ℝ) (536580549127126453/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_087
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0523).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^0*thetaFirstMode x) ≤ (4593858083158026429/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (87/256:ℝ) (11/32:ℝ)
    (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ) (536580549127126453/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_087 (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_088 :
    (8767060585063005481/500000000000000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (11/32:ℝ) (89/256:ℝ)
    (177/512:ℝ) (448840361591/100000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_088
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0529).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^0*thetaFirstMode x) ≤ (701371395982106623/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/32:ℝ) (89/256:ℝ)
    (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ) (521252858377755433/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_088 (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_089 :
    (1672507846827486329/100000000000000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (89/256:ℝ) (45/128:ℝ)
    (179/512:ℝ) (214064914129/50000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_089
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0535).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^0*thetaFirstMode x) ≤ (1672523782065730467/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (89/256:ℝ) (45/128:ℝ)
    (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ) (506155968807570953/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_089 (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_090 :
    (15947212050871685153/1000000000000000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (45/128:ℝ) (91/256:ℝ)
    (181/512:ℝ) (408217392869/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_090
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0541).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^0*thetaFirstMode x) ≤ (7973683544558002347/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/128:ℝ) (91/256:ℝ)
    (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ) (245647015792921217/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_090 (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_091 :
    (7599806048720252089/500000000000000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (91/256:ℝ) (23/64:ℝ)
    (183/512:ℝ) (15563190551/4000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_091
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0547).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^0*thetaFirstMode x) ≤ (1899970360654522393/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (91/256:ℝ) (23/64:ℝ)
    (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ) (476670897321257883/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_091 (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_092 :
    (2896276643086337031/200000000000000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (23/64:ℝ) (93/256:ℝ)
    (185/512:ℝ) (370694018701/100000000000000:ℝ) (231145058214661231/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_092
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0553).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^0*thetaFirstMode x) ≤ (14481529817183504689/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/64:ℝ) (93/256:ℝ)
    (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ) (231145058214661231/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_092 (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_093 :
    (43098889571743783/3125000000000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (93/256:ℝ) (47/128:ℝ)
    (187/512:ℝ) (22064850653/6250000000000:ℝ) (224077469909545329/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_093
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0559).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^0*thetaFirstMode x) ≤ (13791787143693353879/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (93/256:ℝ) (47/128:ℝ)
    (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ) (224077469909545329/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_093 (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_094 :
    (656476527646931403/50000000000000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (47/128:ℝ) (95/256:ℝ)
    (189/512:ℝ) (336088372119/100000000000000:ℝ) (217134160115492507/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_094
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0565).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^0*thetaFirstMode x) ≤ (41030215557561309/3125000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/128:ℝ) (95/256:ℝ)
    (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ) (217134160115492507/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_094 (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_lower_0_095 :
    (390443438744433993/31250000000000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 0 (95/256:ℝ) (3/8:ℝ)
    (191/512:ℝ) (319824521899/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_095
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0571).1
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaSource_curvature_cell_upper_0_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^0*thetaFirstMode x) ≤ (12494324476215599447/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (95/256:ℝ) (3/8:ℝ)
    (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ) (52579114235318267/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_095 (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature14
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative21
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative22

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_448 :
    (41135717595863/500000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(449/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1214868874618164916978457/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (7/8:ℝ) (449/512:ℝ)-(7/8:ℝ)*thetaPowerMass 0 (7/8:ℝ) (449/512:ℝ)) ≤
      thetaFirstModeFirst (7/8:ℝ)*(thetaPowerMass 1 (7/8:ℝ) (449/512:ℝ)-(7/8:ℝ)*thetaPowerMass 0 (7/8:ℝ) (449/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0676.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (7/8:ℝ) (449/512:ℝ)
    (7/8:ℝ) (436103/10000000000000:ℝ) (-1214868874618164916978457/781250000000000000000000000000:ℝ) (24584581102903339971/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_448
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1344).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_448 :
    (∫ x in (7/8:ℝ)..(449/512:ℝ), x^0*thetaFirstMode x) ≤ (10284474986397/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (7/8:ℝ) (449/512:ℝ)
    (136283/3125000000000:ℝ) (508389/12500000000000:ℝ) (24584581102903339971/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_448 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1345).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_449 :
    (38357853459803/500000000000000000000000:ℝ) ≤ ∫ x in (449/512:ℝ)..(225/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2274070919420238827123631/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (449/512:ℝ) (225/256:ℝ)-(130381348261662627095241/148673423925516220418560:ℝ)*thetaPowerMass 0 (449/512:ℝ) (225/256:ℝ)) ≤
      thetaFirstModeFirst (130381348261662627095241/148673423925516220418560:ℝ)*(thetaPowerMass 1 (449/512:ℝ) (225/256:ℝ)-(130381348261662627095241/148673423925516220418560:ℝ)*thetaPowerMass 0 (449/512:ℝ) (225/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0678.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (449/512:ℝ) (225/256:ℝ)
    (130381348261662627095241/148673423925516220418560:ℝ) (4065399/100000000000000:ℝ) (-2274070919420238827123631/1562500000000000000000000000000:ℝ) (46218050966034724083/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_449
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1349).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_449 :
    (∫ x in (449/512:ℝ)..(225/256:ℝ), x^0*thetaFirstMode x) ≤ (38359880544219/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (449/512:ℝ) (225/256:ℝ)
    (508389/12500000000000:ℝ) (379193/10000000000000:ℝ) (46218050966034724083/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_449 (thetaFirstMode_refined_node_1345).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_450 :
    (13967809377/195312500000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(451/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6814254382419506285542371/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (225/256:ℝ) (451/512:ℝ)-(225/256:ℝ)*thetaPowerMass 0 (225/256:ℝ) (451/512:ℝ)) ≤
      thetaFirstModeFirst (225/256:ℝ)*(thetaPowerMass 1 (225/256:ℝ) (451/512:ℝ)-(225/256:ℝ)*thetaPowerMass 0 (225/256:ℝ) (451/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0679.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (225/256:ℝ) (451/512:ℝ)
    (225/256:ℝ) (3791907/100000000000000:ℝ) (-6814254382419506285542371/5000000000000000000000000000000:ℝ) (10857980484460440403/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_450
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1350).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_450 :
    (∫ x in (225/256:ℝ)..(451/512:ℝ), x^0*thetaFirstMode x) ≤ (71519069070011/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (225/256:ℝ) (451/512:ℝ)
    (379193/10000000000000:ℝ) (220899/6250000000000:ℝ) (10857980484460440403/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_450 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1351).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_451 :
    (6664874652413/100000000000000000000000:ℝ) ≤ ∫ x in (451/512:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-398383235380354727994879/312500000000000000000000000000:ℝ)*(thetaPowerMass 1 (451/512:ℝ) (113/128:ℝ)-(135702249480635062632759/154054636064115110786560:ℝ)*thetaPowerMass 0 (451/512:ℝ) (113/128:ℝ)) ≤
      thetaFirstModeFirst (135702249480635062632759/154054636064115110786560:ℝ)*(thetaPowerMass 1 (451/512:ℝ) (113/128:ℝ)-(135702249480635062632759/154054636064115110786560:ℝ)*thetaPowerMass 0 (451/512:ℝ) (113/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0681.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (451/512:ℝ) (113/128:ℝ)
    (135702249480635062632759/154054636064115110786560:ℝ) (353289/10000000000000:ℝ) (-398383235380354727994879/312500000000000000000000000000:ℝ) (40802309277093263701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_451
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1355).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_451 :
    (∫ x in (451/512:ℝ)..(113/128:ℝ), x^0*thetaFirstMode x) ≤ (33326176069529/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (451/512:ℝ) (113/128:ℝ)
    (220899/6250000000000:ℝ) (3293411/100000000000000:ℝ) (40802309277093263701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_451 (thetaFirstMode_refined_node_1351).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_452 :
    (62095986505631/1000000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(453/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2982729760082492234380577/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (113/128:ℝ) (453/512:ℝ)-(113/128:ℝ)*thetaPowerMass 0 (113/128:ℝ) (453/512:ℝ)) ≤
      thetaFirstModeFirst (113/128:ℝ)*(thetaPowerMass 1 (113/128:ℝ) (453/512:ℝ)-(113/128:ℝ)*thetaPowerMass 0 (113/128:ℝ) (453/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0682.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (113/128:ℝ) (453/512:ℝ)
    (113/128:ℝ) (3293391/100000000000000:ℝ) (-2982729760082492234380577/2500000000000000000000000000000:ℝ) (9580276645360851979/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_452
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1356).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_452 :
    (∫ x in (113/128:ℝ)..(453/512:ℝ), x^0*thetaFirstMode x) ≤ (31049719773723/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (113/128:ℝ) (453/512:ℝ)
    (3293411/100000000000000:ℝ) (383501/12500000000000:ℝ) (9580276645360851979/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_452 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1357).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_453 :
    (57838076385093/1000000000000000000000000:ℝ) ≤ ∫ x in (453/512:ℝ)..(227/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1115405432254215581692793/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (453/512:ℝ) (227/256:ℝ)-(141215303034674977169457/159605509118049574428160:ℝ)*thetaPowerMass 0 (453/512:ℝ) (227/256:ℝ)) ≤
      thetaFirstModeFirst (141215303034674977169457/159605509118049574428160:ℝ)*(thetaPowerMass 1 (453/512:ℝ) (227/256:ℝ)-(141215303034674977169457/159605509118049574428160:ℝ)*thetaPowerMass 0 (453/512:ℝ) (227/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0684.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (453/512:ℝ) (227/256:ℝ)
    (141215303034674977169457/159605509118049574428160:ℝ) (1533353/50000000000000:ℝ) (-1115405432254215581692793/1000000000000000000000000000000:ℝ) (719612273135570069/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_453
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1361).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_453 :
    (∫ x in (453/512:ℝ)..(227/256:ℝ), x^0*thetaFirstMode x) ≤ (7230161638417/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (453/512:ℝ) (227/256:ℝ)
    (383501/12500000000000:ℝ) (714307/25000000000000:ℝ) (719612273135570069/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_453 (thetaFirstMode_refined_node_1357).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_454 :
    (53856869859233/1000000000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(455/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6520673449891673726020543/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (227/256:ℝ) (455/512:ℝ)-(227/256:ℝ)*thetaPowerMass 0 (227/256:ℝ) (455/512:ℝ)) ≤
      thetaFirstModeFirst (227/256:ℝ)*(thetaPowerMass 1 (227/256:ℝ) (455/512:ℝ)-(227/256:ℝ)*thetaPowerMass 0 (227/256:ℝ) (455/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0685.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (227/256:ℝ) (455/512:ℝ)
    (227/256:ℝ) (285721/10000000000000:ℝ) (-6520673449891673726020543/6250000000000000000000000000000:ℝ) (33773470833088802241/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_454
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1362).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_454 :
    (∫ x in (227/256:ℝ)..(455/512:ℝ), x^0*thetaFirstMode x) ≤ (26929969436293/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (227/256:ℝ) (455/512:ℝ)
    (714307/25000000000000:ℝ) (2660177/100000000000000:ℝ) (33773470833088802241/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_454 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1363).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_455 :
    (1566737106603/31250000000000000000000:ℝ) ≤ ∫ x in (455/512:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-609264086806244446373891/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (455/512:ℝ) (57/64:ℝ)-(29385310700934990796995/33066121515527560919552:ℝ)*thetaPowerMass 0 (455/512:ℝ) (57/64:ℝ)) ≤
      thetaFirstModeFirst (29385310700934990796995/33066121515527560919552:ℝ)*(thetaPowerMass 1 (455/512:ℝ) (57/64:ℝ)-(29385310700934990796995/33066121515527560919552:ℝ)*thetaPowerMass 0 (455/512:ℝ) (57/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0687.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (455/512:ℝ) (57/64:ℝ)
    (29385310700934990796995/33066121515527560919552:ℝ) (664761/25000000000000:ℝ) (-609264086806244446373891/625000000000000000000000000000:ℝ) (7923176181761866589/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_455
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1367).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_455 :
    (∫ x in (455/512:ℝ)..(57/64:ℝ), x^0*thetaFirstMode x) ≤ (50138437813467/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (455/512:ℝ) (57/64:ℝ)
    (2660177/100000000000000:ℝ) (1238007/50000000000000:ℝ) (7923176181761866589/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_455 (thetaFirstMode_refined_node_1363).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_456 :
    (46658114429003/1000000000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(457/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11391209723696625120842823/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (57/64:ℝ) (457/512:ℝ)-(57/64:ℝ)*thetaPowerMass 0 (57/64:ℝ) (457/512:ℝ)) ≤
      thetaFirstModeFirst (57/64:ℝ)*(thetaPowerMass 1 (57/64:ℝ) (457/512:ℝ)-(57/64:ℝ)*thetaPowerMass 0 (57/64:ℝ) (457/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0688.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (57/64:ℝ) (457/512:ℝ)
    (57/64:ℝ) (2475999/100000000000000:ℝ) (-11391209723696625120842823/12500000000000000000000000000000:ℝ) (3716451004630729741/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_456
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1368).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_456 :
    (∫ x in (57/64:ℝ)..(457/512:ℝ), x^0*thetaFirstMode x) ≤ (23330413648773/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (57/64:ℝ) (457/512:ℝ)
    (1238007/50000000000000:ℝ) (460789/20000000000000:ℝ) (3716451004630729741/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_456 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1369).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_457 :
    (8681902757803/200000000000000000000000:ℝ) ≤ ∫ x in (457/512:ℝ)..(229/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-425495981963120782550659/500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (457/512:ℝ) (229/256:ℝ)-(152842207727465608740993/171234597812449350300160:ℝ)*thetaPowerMass 0 (457/512:ℝ) (229/256:ℝ)) ≤
      thetaFirstModeFirst (152842207727465608740993/171234597812449350300160:ℝ)*(thetaPowerMass 1 (457/512:ℝ) (229/256:ℝ)-(152842207727465608740993/171234597812449350300160:ℝ)*thetaPowerMass 0 (457/512:ℝ) (229/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0690.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (457/512:ℝ) (229/256:ℝ)
    (152842207727465608740993/171234597812449350300160:ℝ) (28787/1250000000000:ℝ) (-425495981963120782550659/500000000000000000000000000000:ℝ) (435685314641347487/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_457
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1373).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_457 :
    (∫ x in (457/512:ℝ)..(229/256:ℝ), x^0*thetaFirstMode x) ≤ (2713252680613/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (457/512:ℝ) (229/256:ℝ)
    (460789/20000000000000:ℝ) (2143221/100000000000000:ℝ) (435685314641347487/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_457 (thetaFirstMode_refined_node_1369).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_458 :
    (40375474961889/1000000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(459/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-19877077925909999432716887/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (229/256:ℝ) (459/512:ℝ)-(229/256:ℝ)*thetaPowerMass 0 (229/256:ℝ) (459/512:ℝ)) ≤
      thetaFirstModeFirst (229/256:ℝ)*(thetaPowerMass 1 (229/256:ℝ) (459/512:ℝ)-(229/256:ℝ)*thetaPowerMass 0 (229/256:ℝ) (459/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0691.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (229/256:ℝ) (459/512:ℝ)
    (229/256:ℝ) (2143207/100000000000000:ℝ) (-19877077925909999432716887/25000000000000000000000000000000:ℝ) (26143417121733651497/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_458
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1374).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_458 :
    (∫ x in (229/256:ℝ)..(459/512:ℝ), x^0*thetaFirstMode x) ≤ (504723736121/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (229/256:ℝ) (459/512:ℝ)
    (2143221/100000000000000:ℝ) (996569/50000000000000:ℝ) (26143417121733651497/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_458 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1375).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_459 :
    (3754279037927/100000000000000000000000:ℝ) ≤ ∫ x in (459/512:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2318882435067136478747643/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (459/512:ℝ) (115/128:ℝ)-(158968638409273606456191/177322249882403159887360:ℝ)*thetaPowerMass 0 (459/512:ℝ) (115/128:ℝ)) ≤
      thetaFirstModeFirst (158968638409273606456191/177322249882403159887360:ℝ)*(thetaPowerMass 1 (459/512:ℝ) (115/128:ℝ)-(158968638409273606456191/177322249882403159887360:ℝ)*thetaPowerMass 0 (459/512:ℝ) (115/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0693.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (459/512:ℝ) (115/128:ℝ)
    (158968638409273606456191/177322249882403159887360:ℝ) (1992283/100000000000000:ℝ) (-2318882435067136478747643/3125000000000000000000000000000:ℝ) (24504501761032275709/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_459
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1379).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_459 :
    (∫ x in (459/512:ℝ)..(115/128:ℝ), x^0*thetaFirstMode x) ≤ (4693128717939/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (459/512:ℝ) (115/128:ℝ)
    (996569/50000000000000:ℝ) (1853031/100000000000000:ℝ) (24504501761032275709/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_459 (thetaFirstMode_refined_node_1375).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_460 :
    (8724670138257/250000000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(461/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6928938958040826438853041/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (115/128:ℝ) (461/512:ℝ)-(115/128:ℝ)*thetaPowerMass 0 (115/128:ℝ) (461/512:ℝ)) ≤
      thetaFirstModeFirst (115/128:ℝ)*(thetaPowerMass 1 (115/128:ℝ) (461/512:ℝ)-(115/128:ℝ)*thetaPowerMass 0 (115/128:ℝ) (461/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0694.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (115/128:ℝ) (461/512:ℝ)
    (115/128:ℝ) (926509/50000000000000:ℝ) (-6928938958040826438853041/10000000000000000000000000000000:ℝ) (4592334517383534719/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_460
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1380).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_460 :
    (∫ x in (115/128:ℝ)..(461/512:ℝ), x^0*thetaFirstMode x) ≤ (17450415703969/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (115/128:ℝ) (461/512:ℝ)
    (1853031/100000000000000:ℝ) (861137/50000000000000:ℝ) (4592334517383534719/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_460 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1381).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_461 :
    (32431470862487/1000000000000000000000000:ℝ) ≤ ∫ x in (461/512:ℝ)..(231/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4039347728469461010626529/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (461/512:ℝ) (231/256:ℝ)-(165312387803273059105209/183598439372905969845760:ℝ)*thetaPowerMass 0 (461/512:ℝ) (231/256:ℝ)) ≤
      thetaFirstModeFirst (165312387803273059105209/183598439372905969845760:ℝ)*(thetaPowerMass 1 (461/512:ℝ) (231/256:ℝ)-(165312387803273059105209/183598439372905969845760:ℝ)*thetaPowerMass 0 (461/512:ℝ) (231/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0696.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (461/512:ℝ) (231/256:ℝ)
    (165312387803273059105209/183598439372905969845760:ℝ) (430383/25000000000000:ℝ) (-4039347728469461010626529/6250000000000000000000000000000:ℝ) (21509694396691431421/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_461
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1385).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_461 :
    (∫ x in (461/512:ℝ)..(231/256:ℝ), x^0*thetaFirstMode x) ≤ (16216730715137/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (461/512:ℝ) (231/256:ℝ)
    (861137/50000000000000:ℝ) (40007/2500000000000:ℝ) (21509694396691431421/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_461 (thetaFirstMode_refined_node_1381).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_462 :
    (15064934631453/500000000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(463/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-376962510432121021121593/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (231/256:ℝ) (463/512:ℝ)-(231/256:ℝ)*thetaPowerMass 0 (231/256:ℝ) (463/512:ℝ)) ≤
      thetaFirstModeFirst (231/256:ℝ)*(thetaPowerMass 1 (231/256:ℝ) (463/512:ℝ)-(231/256:ℝ)*thetaPowerMass 0 (231/256:ℝ) (463/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0697.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (231/256:ℝ) (463/512:ℝ)
    (231/256:ℝ) (1600269/100000000000000:ℝ) (-376962510432121021121593/625000000000000000000000000000:ℝ) (2517955737992315821/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_462
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1386).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_462 :
    (∫ x in (231/256:ℝ)..(463/512:ℝ), x^0*thetaFirstMode x) ≤ (30131770522307/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (231/256:ℝ) (463/512:ℝ)
    (40007/2500000000000:ℝ) (743247/50000000000000:ℝ) (2517955737992315821/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_462 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1387).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_463 :
    (27983490000801/1000000000000000000000000:ℝ) ≤ ∫ x in (463/512:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-14056240598261792362790163/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (463/512:ℝ) (29/32:ℝ)-(171880171452079192654407/190068149254242844572160:ℝ)*thetaPowerMass 0 (463/512:ℝ) (29/32:ℝ)) ≤
      thetaFirstModeFirst (171880171452079192654407/190068149254242844572160:ℝ)*(thetaPowerMass 1 (463/512:ℝ) (29/32:ℝ)-(171880171452079192654407/190068149254242844572160:ℝ)*thetaPowerMass 0 (463/512:ℝ) (29/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0699.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (463/512:ℝ) (29/32:ℝ)
    (171880171452079192654407/190068149254242844572160:ℝ) (1485851/100000000000000:ℝ) (-14056240598261792362790163/25000000000000000000000000000000:ℝ) (589337504137818281/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_463
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1391).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_463 :
    (∫ x in (463/512:ℝ)..(29/32:ℝ), x^0*thetaFirstMode x) ≤ (5597048808161/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (463/512:ℝ) (29/32:ℝ)
    (743247/50000000000000:ℝ) (690197/50000000000000:ℝ) (589337504137818281/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_463 (thetaFirstMode_refined_node_1387).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_464 :
    (6495587051287/250000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(465/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6555004609038838449985561/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (29/32:ℝ) (465/512:ℝ)-(29/32:ℝ)*thetaPowerMass 0 (29/32:ℝ) (465/512:ℝ)) ≤
      thetaFirstModeFirst (29/32:ℝ)*(thetaPowerMass 1 (29/32:ℝ) (465/512:ℝ)-(29/32:ℝ)*thetaPowerMass 0 (29/32:ℝ) (465/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0700.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (29/32:ℝ) (465/512:ℝ)
    (29/32:ℝ) (276077/20000000000000:ℝ) (-6555004609038838449985561/12500000000000000000000000000000:ℝ) (1103169072384304323/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_464
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1392).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_464 :
    (∫ x in (29/32:ℝ)..(465/512:ℝ), x^0*thetaFirstMode x) ≤ (25984011703011/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (29/32:ℝ) (465/512:ℝ)
    (690197/50000000000000:ℝ) (1281491/100000000000000:ℝ) (1103169072384304323/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_464 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1393).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_465 :
    (6029312646449/250000000000000000000000:ℝ) ≤ ∫ x in (465/512:ℝ)..(233/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-95422043151049020597989/195312500000000000000000000000:ℝ)*(thetaPowerMass 1 (465/512:ℝ) (233/256:ℝ)-(35735776399208126994885/39347294353086520381952:ℝ)*thetaPowerMass 0 (465/512:ℝ) (233/256:ℝ)) ≤
      thetaFirstModeFirst (35735776399208126994885/39347294353086520381952:ℝ)*(thetaPowerMass 1 (465/512:ℝ) (233/256:ℝ)-(35735776399208126994885/39347294353086520381952:ℝ)*thetaPowerMass 0 (465/512:ℝ) (233/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0702.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (465/512:ℝ) (233/256:ℝ)
    (35735776399208126994885/39347294353086520381952:ℝ) (256187/20000000000000:ℝ) (-95422043151049020597989/195312500000000000000000000000:ℝ) (8257550955968549439/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_465
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1397).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_465 :
    (∫ x in (465/512:ℝ)..(233/256:ℝ), x^0*thetaFirstMode x) ≤ (12059399404777/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (465/512:ℝ) (233/256:ℝ)
    (1281491/100000000000000:ℝ) (297331/25000000000000:ℝ) (8257550955968549439/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_465 (thetaFirstMode_refined_node_1393).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_466 :
    (4475879059597/200000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(467/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5692558824771531178850603/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (233/256:ℝ) (467/512:ℝ)-(233/256:ℝ)*thetaPowerMass 0 (233/256:ℝ) (467/512:ℝ)) ≤
      thetaFirstModeFirst (233/256:ℝ)*(thetaPowerMass 1 (233/256:ℝ) (467/512:ℝ)-(233/256:ℝ)*thetaPowerMass 0 (233/256:ℝ) (467/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0703.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (233/256:ℝ) (467/512:ℝ)
    (233/256:ℝ) (297329/25000000000000:ℝ) (-5692558824771531178850603/12500000000000000000000000000000:ℝ) (15447963605229410411/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_466
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1398).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_466 :
    (∫ x in (233/256:ℝ)..(467/512:ℝ), x^0*thetaFirstMode x) ≤ (22380867626217/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (233/256:ℝ) (467/512:ℝ)
    (297331/25000000000000:ℝ) (1103459/100000000000000:ℝ) (15447963605229410411/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_466 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1399).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_467 :
    (103803181351/5000000000000000000000:ℝ) ≤ ∫ x in (467/512:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-5300364402117373609737747/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (467/512:ℝ) (117/128:ℝ)-(185715593048194171355943/203608610322761788188160:ℝ)*thetaPowerMass 0 (467/512:ℝ) (117/128:ℝ)) ≤
      thetaFirstModeFirst (185715593048194171355943/203608610322761788188160:ℝ)*(thetaPowerMass 1 (467/512:ℝ) (117/128:ℝ)-(185715593048194171355943/203608610322761788188160:ℝ)*thetaPowerMass 0 (467/512:ℝ) (117/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0705.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (467/512:ℝ) (117/128:ℝ)
    (185715593048194171355943/203608610322761788188160:ℝ) (551489/50000000000000:ℝ) (-5300364402117373609737747/12500000000000000000000000000000:ℝ) (14445480376358809353/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_467
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1403).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_467 :
    (∫ x in (467/512:ℝ)..(117/128:ℝ), x^0*thetaFirstMode x) ≤ (415240152557/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (467/512:ℝ) (117/128:ℝ)
    (1103459/100000000000000:ℝ) (1023489/100000000000000:ℝ) (14445480376358809353/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_467 (thetaFirstMode_refined_node_1399).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_468 :
    (4813303341001/250000000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(469/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-19750930930569036197061423/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (117/128:ℝ) (469/512:ℝ)-(117/128:ℝ)*thetaPowerMass 0 (117/128:ℝ) (469/512:ℝ)) ≤
      thetaFirstModeFirst (117/128:ℝ)*(thetaPowerMass 1 (117/128:ℝ) (469/512:ℝ)-(117/128:ℝ)*thetaPowerMass 0 (117/128:ℝ) (469/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0706.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (117/128:ℝ) (469/512:ℝ)
    (117/128:ℝ) (511741/50000000000000:ℝ) (-19750930930569036197061423/50000000000000000000000000000000:ℝ) (3376000050664325273/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_468
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1404).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_468 :
    (∫ x in (117/128:ℝ)..(469/512:ℝ), x^0*thetaFirstMode x) ≤ (601703319943/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (117/128:ℝ) (469/512:ℝ)
    (1023489/100000000000000:ℝ) (949031/100000000000000:ℝ) (3376000050664325273/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_468 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1405).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_469 :
    (17849924056503/1000000000000000000000000:ℝ) ≤ ∫ x in (469/512:ℝ)..(235/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4594795814467300481242593/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (469/512:ℝ) (235/256:ℝ)-(192997563136753342300641/210689881453211795484160:ℝ)*thetaPowerMass 0 (469/512:ℝ) (235/256:ℝ)) ≤
      thetaFirstModeFirst (192997563136753342300641/210689881453211795484160:ℝ)*(thetaPowerMass 1 (469/512:ℝ) (235/256:ℝ)-(192997563136753342300641/210689881453211795484160:ℝ)*thetaPowerMass 0 (469/512:ℝ) (235/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0708.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (469/512:ℝ) (235/256:ℝ)
    (192997563136753342300641/210689881453211795484160:ℝ) (118577/12500000000000:ℝ) (-4594795814467300481242593/12500000000000000000000000000000:ℝ) (6310040703464386403/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_469
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1409).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_469 :
    (∫ x in (469/512:ℝ)..(235/256:ℝ), x^0*thetaFirstMode x) ≤ (3570225853189/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (469/512:ℝ) (235/256:ℝ)
    (949031/100000000000000:ℝ) (879727/100000000000000:ℝ) (6310040703464386403/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_469 (thetaFirstMode_refined_node_1405).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_470 :
    (4135984603019/250000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(471/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-17111536951308867281704801/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (235/256:ℝ) (471/512:ℝ)-(235/256:ℝ)*thetaPowerMass 0 (235/256:ℝ) (471/512:ℝ)) ≤
      thetaFirstModeFirst (235/256:ℝ)*(thetaPowerMass 1 (235/256:ℝ) (471/512:ℝ)-(235/256:ℝ)*thetaPowerMass 0 (235/256:ℝ) (471/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0709.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (235/256:ℝ) (471/512:ℝ)
    (235/256:ℝ) (879721/100000000000000:ℝ) (-17111536951308867281704801/50000000000000000000000000000000:ℝ) (589523037444283507/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_470
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1410).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_470 :
    (∫ x in (235/256:ℝ)..(471/512:ℝ), x^0*thetaFirstMode x) ≤ (16545081862243/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (235/256:ℝ) (471/512:ℝ)
    (879727/100000000000000:ℝ) (815239/100000000000000:ℝ) (589523037444283507/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_470 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1411).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_471 :
    (7664454410093/500000000000000000000000:ℝ) ≤ ∫ x in (471/512:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15913526783585675278320063/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (471/512:ℝ) (59/64:ℝ)-(200532239716009818864159/217985716752994642792960:ℝ)*thetaPowerMass 0 (471/512:ℝ) (59/64:ℝ)) ≤
      thetaFirstModeFirst (200532239716009818864159/217985716752994642792960:ℝ)*(thetaPowerMass 1 (471/512:ℝ) (59/64:ℝ)-(200532239716009818864159/217985716752994642792960:ℝ)*thetaPowerMass 0 (471/512:ℝ) (59/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0711.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (471/512:ℝ) (59/64:ℝ)
    (200532239716009818864159/217985716752994642792960:ℝ) (814881/100000000000000:ℝ) (-15913526783585675278320063/50000000000000000000000000000000:ℝ) (11012034271656253791/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_471
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1415).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_471 :
    (∫ x in (471/512:ℝ)..(59/64:ℝ), x^0*thetaFirstMode x) ≤ (7664984734943/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (471/512:ℝ) (59/64:ℝ)
    (815239/100000000000000:ℝ) (3021/400000000000:ℝ) (11012034271656253791/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_471 (thetaFirstMode_refined_node_1411).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_472 :
    (7099391680361/500000000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(473/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-59228152473932116783149/200000000000000000000000000000:ℝ)*(thetaPowerMass 1 (59/64:ℝ) (473/512:ℝ)-(59/64:ℝ)*thetaPowerMass 0 (59/64:ℝ) (473/512:ℝ)) ≤
      thetaFirstModeFirst (59/64:ℝ)*(thetaPowerMass 1 (59/64:ℝ) (473/512:ℝ)-(59/64:ℝ)*thetaPowerMass 0 (59/64:ℝ) (473/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0712.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (59/64:ℝ) (473/512:ℝ)
    (59/64:ℝ) (188811/25000000000000:ℝ) (-59228152473932116783149/200000000000000000000000000000:ℝ) (2056376216470054499/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_472
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1416).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_472 :
    (∫ x in (59/64:ℝ)..(473/512:ℝ), x^0*thetaFirstMode x) ≤ (14199797808651/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (59/64:ℝ) (473/512:ℝ)
    (3021/400000000000:ℝ) (699463/100000000000000:ℝ) (2056376216470054499/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_472 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1417).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_473 :
    (1314802850791/100000000000000000000000:ℝ) ≤ ∫ x in (473/512:ℝ)..(237/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-344050173313491711150469/1250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (473/512:ℝ) (237/256:ℝ)-(208327263246534084091857/225501664871413871772160:ℝ)*thetaPowerMass 0 (473/512:ℝ) (237/256:ℝ)) ≤
      thetaFirstModeFirst (208327263246534084091857/225501664871413871772160:ℝ)*(thetaPowerMass 1 (473/512:ℝ) (237/256:ℝ)-(208327263246534084091857/225501664871413871772160:ℝ)*thetaPowerMass 0 (473/512:ℝ) (237/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0714.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (473/512:ℝ) (237/256:ℝ)
    (208327263246534084091857/225501664871413871772160:ℝ) (139831/20000000000000:ℝ) (-344050173313491711150469/1250000000000000000000000000000:ℝ) (2343066204438221/244140625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_473
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1421).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_473 :
    (∫ x in (473/512:ℝ)..(237/256:ℝ), x^0*thetaFirstMode x) ≤ (328723834597/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (473/512:ℝ) (237/256:ℝ)
    (699463/100000000000000:ℝ) (1619/250000000000:ℝ) (2343066204438221/244140625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_473 (thetaFirstMode_refined_node_1417).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_474 :
    (12171279830597/1000000000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(475/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-31993395088703516659901/125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (237/256:ℝ) (475/512:ℝ)-(237/256:ℝ)*thetaPowerMass 0 (237/256:ℝ) (475/512:ℝ)) ≤
      thetaFirstModeFirst (237/256:ℝ)*(thetaPowerMass 1 (237/256:ℝ) (475/512:ℝ)-(237/256:ℝ)*thetaPowerMass 0 (237/256:ℝ) (475/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0715.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (237/256:ℝ) (475/512:ℝ)
    (237/256:ℝ) (129519/20000000000000:ℝ) (-31993395088703516659901/125000000000000000000000000000:ℝ) (8955372340503951647/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_474
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1422).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_474 :
    (∫ x in (237/256:ℝ)..(475/512:ℝ), x^0*thetaFirstMode x) ≤ (12172174148051/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (237/256:ℝ) (475/512:ℝ)
    (1619/250000000000:ℝ) (2997/500000000000:ℝ) (8955372340503951647/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_474 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1423).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_475 :
    (11263677771947/1000000000000000000000000:ℝ) ≤ ∫ x in (475/512:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-11886899664204266836359249/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (475/512:ℝ) (119/128:ℝ)-(43278094269113915002275/46648678704053587338752:ℝ)*thetaPowerMass 0 (475/512:ℝ) (119/128:ℝ)) ≤
      thetaFirstModeFirst (43278094269113915002275/46648678704053587338752:ℝ)*(thetaPowerMass 1 (475/512:ℝ) (119/128:ℝ)-(43278094269113915002275/46648678704053587338752:ℝ)*thetaPowerMass 0 (475/512:ℝ) (119/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0717.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (475/512:ℝ) (119/128:ℝ)
    (43278094269113915002275/46648678704053587338752:ℝ) (299567/50000000000000:ℝ) (-11886899664204266836359249/50000000000000000000000000000000:ℝ) (8353889591520146871/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_475
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1427).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_475 :
    (∫ x in (475/512:ℝ)..(119/128:ℝ), x^0*thetaFirstMode x) ≤ (2816125180673/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (475/512:ℝ) (119/128:ℝ)
    (2997/500000000000:ℝ) (69327/12500000000000:ℝ) (8353889591520146871/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_475 (thetaFirstMode_refined_node_1423).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_476 :
    (2605133141033/250000000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(477/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-690433050305430380128671/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (119/128:ℝ) (477/512:ℝ)-(119/128:ℝ)*thetaPowerMass 0 (119/128:ℝ) (477/512:ℝ)) ≤
      thetaFirstModeFirst (119/128:ℝ)*(thetaPowerMass 1 (119/128:ℝ) (477/512:ℝ)-(119/128:ℝ)*thetaPowerMass 0 (119/128:ℝ) (477/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0718.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (119/128:ℝ) (477/512:ℝ)
    (119/128:ℝ) (138653/25000000000000:ℝ) (-690433050305430380128671/3125000000000000000000000000000:ℝ) (7790397053757855993/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_476
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1428).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_476 :
    (∫ x in (119/128:ℝ)..(477/512:ℝ), x^0*thetaFirstMode x) ≤ (10421305663031/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (119/128:ℝ) (477/512:ℝ)
    (69327/12500000000000:ℝ) (513021/100000000000000:ℝ) (7790397053757855993/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_476 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1429).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_477 :
    (9637545265271/1000000000000000000000000:ℝ) ≤ ∫ x in (477/512:ℝ)..(239/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-205093524455116597851793/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (477/512:ℝ) (239/256:ℝ)-(224729903008522098228393/241216691509014397212160:ℝ)*thetaPowerMass 0 (477/512:ℝ) (239/256:ℝ)) ≤
      thetaFirstModeFirst (224729903008522098228393/241216691509014397212160:ℝ)*(thetaPowerMass 1 (477/512:ℝ) (239/256:ℝ)-(224729903008522098228393/241216691509014397212160:ℝ)*thetaPowerMass 0 (477/512:ℝ) (239/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0720.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (477/512:ℝ) (239/256:ℝ)
    (224729903008522098228393/241216691509014397212160:ℝ) (512793/100000000000000:ℝ) (-205093524455116597851793/1000000000000000000000000000000:ℝ) (1452532084929160941/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_477
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1433).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_477 :
    (∫ x in (477/512:ℝ)..(239/256:ℝ), x^0*thetaFirstMode x) ≤ (963826418443/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (477/512:ℝ) (239/256:ℝ)
    (513021/100000000000000:ℝ) (474399/100000000000000:ℝ) (1452532084929160941/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_477 (thetaFirstMode_refined_node_1429).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_478 :
    (8910613110259/1000000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(479/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4762097396131135711131297/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (239/256:ℝ) (479/512:ℝ)-(239/256:ℝ)*thetaPowerMass 0 (239/256:ℝ) (479/512:ℝ)) ≤
      thetaFirstModeFirst (239/256:ℝ)*(thetaPowerMass 1 (239/256:ℝ) (479/512:ℝ)-(239/256:ℝ)*thetaPowerMass 0 (239/256:ℝ) (479/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0721.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (239/256:ℝ) (479/512:ℝ)
    (239/256:ℝ) (94879/20000000000000:ℝ) (-4762097396131135711131297/25000000000000000000000000000000:ℝ) (6768571694957169177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_478
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1434).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_478 :
    (∫ x in (239/256:ℝ)..(479/512:ℝ), x^0*thetaFirstMode x) ≤ (8911305330089/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (239/256:ℝ) (479/512:ℝ)
    (474399/100000000000000:ℝ) (438549/100000000000000:ℝ) (6768571694957169177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_478 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1435).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_479 :
    (4117990678303/500000000000000000000000:ℝ) ≤ ∫ x in (479/512:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1767134288055586409173623/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (479/512:ℝ) (15/16:ℝ)-(233353802902454023413591/249427470805914151528960:ℝ)*thetaPowerMass 0 (479/512:ℝ) (15/16:ℝ)) ≤
      thetaFirstModeFirst (233353802902454023413591/249427470805914151528960:ℝ)*(thetaPowerMass 1 (479/512:ℝ) (15/16:ℝ)-(233353802902454023413591/249427470805914151528960:ℝ)*thetaPowerMass 0 (479/512:ℝ) (15/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0723.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (479/512:ℝ) (15/16:ℝ)
    (233353802902454023413591/249427470805914151528960:ℝ) (438353/100000000000000:ℝ) (-1767134288055586409173623/10000000000000000000000000000000:ℝ) (3153062464355029157/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_479
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1439).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_479 :
    (∫ x in (479/512:ℝ)..(15/16:ℝ), x^0*thetaFirstMode x) ≤ (8236611986081/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (479/512:ℝ) (15/16:ℝ)
    (438549/100000000000000:ℝ) (405281/100000000000000:ℝ) (3153062464355029157/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_479 (thetaFirstMode_refined_node_1435).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator

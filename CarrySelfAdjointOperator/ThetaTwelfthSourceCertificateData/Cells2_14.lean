import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature14
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative21
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative22

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_2_448 :
    (31564823945957/500000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(449/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-142184216259104877/97656250000000000000000:ℝ)*(thetaPowerMass 3 (7/8:ℝ) (449/512:ℝ)-(449/512:ℝ)*thetaPowerMass 2 (7/8:ℝ) (449/512:ℝ)) ≤
      thetaFirstModeFirst (449/512:ℝ)*(thetaPowerMass 3 (7/8:ℝ) (449/512:ℝ)-(449/512:ℝ)*thetaPowerMass 2 (7/8:ℝ) (449/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0677.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (7/8:ℝ) (449/512:ℝ)
    (449/512:ℝ) (254193/6250000000000:ℝ) (-142184216259104877/97656250000000000000000:ℝ) (24584581102903339971/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_448
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1345).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_448 :
    (∫ x in (7/8:ℝ)..(449/512:ℝ), x^2*thetaFirstMode x) ≤ (1972858903317/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (7/8:ℝ) (449/512:ℝ)
    (136283/3125000000000:ℝ) (508389/12500000000000:ℝ) (24584581102903339971/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_448 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1345).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_449 :
    (29563962878073/500000000000000000000000:ℝ) ≤ ∫ x in (449/512:ℝ)..(225/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2274070919420238827123631/1562500000000000000000000000000:ℝ)*(thetaPowerMass 3 (449/512:ℝ) (225/256:ℝ)-(130381348261662627095241/148673423925516220418560:ℝ)*thetaPowerMass 2 (449/512:ℝ) (225/256:ℝ)) ≤
      thetaFirstModeFirst (130381348261662627095241/148673423925516220418560:ℝ)*(thetaPowerMass 3 (449/512:ℝ) (225/256:ℝ)-(130381348261662627095241/148673423925516220418560:ℝ)*thetaPowerMass 2 (449/512:ℝ) (225/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0678.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (449/512:ℝ) (225/256:ℝ)
    (130381348261662627095241/148673423925516220418560:ℝ) (4065399/100000000000000:ℝ) (-2274070919420238827123631/1562500000000000000000000000000:ℝ) (46218050966034724083/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_449
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1349).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_449 :
    (∫ x in (449/512:ℝ)..(225/256:ℝ), x^2*thetaFirstMode x) ≤ (11826210518939/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (449/512:ℝ) (225/256:ℝ)
    (508389/12500000000000:ℝ) (379193/10000000000000:ℝ) (46218050966034724083/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_449 (thetaFirstMode_refined_node_1345).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_450 :
    (55366535285297/1000000000000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(451/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-797074562701286519/625000000000000000000000:ℝ)*(thetaPowerMass 3 (225/256:ℝ) (451/512:ℝ)-(451/512:ℝ)*thetaPowerMass 2 (225/256:ℝ) (451/512:ℝ)) ≤
      thetaFirstModeFirst (451/512:ℝ)*(thetaPowerMass 3 (225/256:ℝ) (451/512:ℝ)-(451/512:ℝ)*thetaPowerMass 2 (225/256:ℝ) (451/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0680.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (225/256:ℝ) (451/512:ℝ)
    (451/512:ℝ) (1767181/50000000000000:ℝ) (-797074562701286519/625000000000000000000000:ℝ) (10857980484460440403/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_450
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1351).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_450 :
    (∫ x in (225/256:ℝ)..(451/512:ℝ), x^2*thetaFirstMode x) ≤ (13842049812809/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (225/256:ℝ) (451/512:ℝ)
    (379193/10000000000000:ℝ) (220899/6250000000000:ℝ) (10857980484460440403/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_450 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1351).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_451 :
    (51827041052977/1000000000000000000000000:ℝ) ≤ ∫ x in (451/512:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-398383235380354727994879/312500000000000000000000000000:ℝ)*(thetaPowerMass 3 (451/512:ℝ) (113/128:ℝ)-(135702249480635062632759/154054636064115110786560:ℝ)*thetaPowerMass 2 (451/512:ℝ) (113/128:ℝ)) ≤
      thetaFirstModeFirst (135702249480635062632759/154054636064115110786560:ℝ)*(thetaPowerMass 3 (451/512:ℝ) (113/128:ℝ)-(135702249480635062632759/154054636064115110786560:ℝ)*thetaPowerMass 2 (451/512:ℝ) (113/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0681.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (451/512:ℝ) (113/128:ℝ)
    (135702249480635062632759/154054636064115110786560:ℝ) (353289/10000000000000:ℝ) (-398383235380354727994879/312500000000000000000000000000:ℝ) (40802309277093263701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_451
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1355).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_451 :
    (∫ x in (451/512:ℝ)..(113/128:ℝ), x^2*thetaFirstMode x) ≤ (2591492336679/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (451/512:ℝ) (113/128:ℝ)
    (220899/6250000000000:ℝ) (3293411/100000000000000:ℝ) (40802309277093263701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_451 (thetaFirstMode_refined_node_1351).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_452 :
    (12125523294857/250000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(453/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-55791939676208617551/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (113/128:ℝ) (453/512:ℝ)-(453/512:ℝ)*thetaPowerMass 2 (113/128:ℝ) (453/512:ℝ)) ≤
      thetaFirstModeFirst (453/512:ℝ)*(thetaPowerMass 3 (113/128:ℝ) (453/512:ℝ)-(453/512:ℝ)*thetaPowerMass 2 (113/128:ℝ) (453/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0683.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (113/128:ℝ) (453/512:ℝ)
    (453/512:ℝ) (3067989/100000000000000:ℝ) (-55791939676208617551/50000000000000000000000000:ℝ) (9580276645360851979/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_452
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1357).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_452 :
    (∫ x in (113/128:ℝ)..(453/512:ℝ), x^2*thetaFirstMode x) ≤ (48503576393407/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (113/128:ℝ) (453/512:ℝ)
    (3293411/100000000000000:ℝ) (383501/12500000000000:ℝ) (9580276645360851979/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_452 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1357).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_453 :
    (45375069256967/1000000000000000000000000:ℝ) ≤ ∫ x in (453/512:ℝ)..(227/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1115405432254215581692793/1000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (453/512:ℝ) (227/256:ℝ)-(141215303034674977169457/159605509118049574428160:ℝ)*thetaPowerMass 2 (453/512:ℝ) (227/256:ℝ)) ≤
      thetaFirstModeFirst (141215303034674977169457/159605509118049574428160:ℝ)*(thetaPowerMass 3 (453/512:ℝ) (227/256:ℝ)-(141215303034674977169457/159605509118049574428160:ℝ)*thetaPowerMass 2 (453/512:ℝ) (227/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0684.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (453/512:ℝ) (227/256:ℝ)
    (141215303034674977169457/159605509118049574428160:ℝ) (1533353/50000000000000:ℝ) (-1115405432254215581692793/1000000000000000000000000000000:ℝ) (719612273135570069/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_453
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1361).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_453 :
    (∫ x in (453/512:ℝ)..(227/256:ℝ), x^2*thetaFirstMode x) ≤ (45377594539589/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (453/512:ℝ) (227/256:ℝ)
    (383501/12500000000000:ℝ) (714307/25000000000000:ℝ) (719612273135570069/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_453 (thetaFirstMode_refined_node_1357).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_454 :
    (5304919824953/125000000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(455/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-76187694673310493/78125000000000000000000:ℝ)*(thetaPowerMass 3 (227/256:ℝ) (455/512:ℝ)-(455/512:ℝ)*thetaPowerMass 2 (227/256:ℝ) (455/512:ℝ)) ≤
      thetaFirstModeFirst (455/512:ℝ)*(thetaPowerMass 3 (227/256:ℝ) (455/512:ℝ)-(455/512:ℝ)*thetaPowerMass 2 (227/256:ℝ) (455/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0686.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (227/256:ℝ) (455/512:ℝ)
    (455/512:ℝ) (8313/312500000000:ℝ) (-76187694673310493/78125000000000000000000:ℝ) (33773470833088802241/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_454
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1363).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_454 :
    (∫ x in (227/256:ℝ)..(455/512:ℝ), x^2*thetaFirstMode x) ≤ (4244069668391/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (227/256:ℝ) (455/512:ℝ)
    (714307/25000000000000:ℝ) (2660177/100000000000000:ℝ) (33773470833088802241/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_454 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1363).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_455 :
    (9920000971689/250000000000000000000000:ℝ) ≤ ∫ x in (455/512:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-609264086806244446373891/625000000000000000000000000000:ℝ)*(thetaPowerMass 3 (455/512:ℝ) (57/64:ℝ)-(29385310700934990796995/33066121515527560919552:ℝ)*thetaPowerMass 2 (455/512:ℝ) (57/64:ℝ)) ≤
      thetaFirstModeFirst (29385310700934990796995/33066121515527560919552:ℝ)*(thetaPowerMass 3 (455/512:ℝ) (57/64:ℝ)-(29385310700934990796995/33066121515527560919552:ℝ)*thetaPowerMass 2 (455/512:ℝ) (57/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0687.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (455/512:ℝ) (57/64:ℝ)
    (29385310700934990796995/33066121515527560919552:ℝ) (664761/25000000000000:ℝ) (-609264086806244446373891/625000000000000000000000000000:ℝ) (7923176181761866589/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_455
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1367).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_455 :
    (∫ x in (455/512:ℝ)..(57/64:ℝ), x^2*thetaFirstMode x) ≤ (39682261367027/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (455/512:ℝ) (57/64:ℝ)
    (2660177/100000000000000:ℝ) (1238007/50000000000000:ℝ) (7923176181761866589/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_455 (thetaFirstMode_refined_node_1363).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_456 :
    (1159094604719/31250000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(457/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-4256624562084654193/5000000000000000000000000:ℝ)*(thetaPowerMass 3 (57/64:ℝ) (457/512:ℝ)-(457/512:ℝ)*thetaPowerMass 2 (57/64:ℝ) (457/512:ℝ)) ≤
      thetaFirstModeFirst (457/512:ℝ)*(thetaPowerMass 3 (57/64:ℝ) (457/512:ℝ)-(457/512:ℝ)*thetaPowerMass 2 (57/64:ℝ) (457/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0689.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (57/64:ℝ) (457/512:ℝ)
    (457/512:ℝ) (230393/10000000000000:ℝ) (-4256624562084654193/5000000000000000000000000:ℝ) (3716451004630729741/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_456
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1369).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_456 :
    (∫ x in (57/64:ℝ)..(457/512:ℝ), x^2*thetaFirstMode x) ≤ (37092220235567/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (57/64:ℝ) (457/512:ℝ)
    (1238007/50000000000000:ℝ) (460789/20000000000000:ℝ) (3716451004630729741/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_456 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1369).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_457 :
    (8664747679721/250000000000000000000000:ℝ) ≤ ∫ x in (457/512:ℝ)..(229/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-425495981963120782550659/500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (457/512:ℝ) (229/256:ℝ)-(152842207727465608740993/171234597812449350300160:ℝ)*thetaPowerMass 2 (457/512:ℝ) (229/256:ℝ)) ≤
      thetaFirstModeFirst (152842207727465608740993/171234597812449350300160:ℝ)*(thetaPowerMass 3 (457/512:ℝ) (229/256:ℝ)-(152842207727465608740993/171234597812449350300160:ℝ)*thetaPowerMass 2 (457/512:ℝ) (229/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0690.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (457/512:ℝ) (229/256:ℝ)
    (152842207727465608740993/171234597812449350300160:ℝ) (28787/1250000000000:ℝ) (-425495981963120782550659/500000000000000000000000000000:ℝ) (435685314641347487/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_457
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1373).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_457 :
    (∫ x in (457/512:ℝ)..(229/256:ℝ), x^2*thetaFirstMode x) ≤ (6932202271179/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (457/512:ℝ) (229/256:ℝ)
    (460789/20000000000000:ℝ) (2143221/100000000000000:ℝ) (435685314641347487/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_457 (thetaFirstMode_refined_node_1369).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_458 :
    (8094629464549/250000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(459/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-11877341328394317/16000000000000000000000:ℝ)*(thetaPowerMass 3 (229/256:ℝ) (459/512:ℝ)-(459/512:ℝ)*thetaPowerMass 2 (229/256:ℝ) (459/512:ℝ)) ≤
      thetaFirstModeFirst (459/512:ℝ)*(thetaPowerMass 3 (229/256:ℝ) (459/512:ℝ)-(459/512:ℝ)*thetaPowerMass 2 (229/256:ℝ) (459/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0692.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (229/256:ℝ) (459/512:ℝ)
    (459/512:ℝ) (3189/160000000000:ℝ) (-11877341328394317/16000000000000000000000:ℝ) (26143417121733651497/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_458
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1375).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_458 :
    (∫ x in (229/256:ℝ)..(459/512:ℝ), x^2*thetaFirstMode x) ≤ (2023723630761/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (229/256:ℝ) (459/512:ℝ)
    (2143221/100000000000000:ℝ) (996569/50000000000000:ℝ) (26143417121733651497/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_458 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1375).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_459 :
    (1209501251727/40000000000000000000000:ℝ) ≤ ∫ x in (459/512:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2318882435067136478747643/3125000000000000000000000000000:ℝ)*(thetaPowerMass 3 (459/512:ℝ) (115/128:ℝ)-(158968638409273606456191/177322249882403159887360:ℝ)*thetaPowerMass 2 (459/512:ℝ) (115/128:ℝ)) ≤
      thetaFirstModeFirst (158968638409273606456191/177322249882403159887360:ℝ)*(thetaPowerMass 3 (459/512:ℝ) (115/128:ℝ)-(158968638409273606456191/177322249882403159887360:ℝ)*thetaPowerMass 2 (459/512:ℝ) (115/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0693.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (459/512:ℝ) (115/128:ℝ)
    (158968638409273606456191/177322249882403159887360:ℝ) (1992283/100000000000000:ℝ) (-2318882435067136478747643/3125000000000000000000000000000:ℝ) (24504501761032275709/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_459
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1379).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_459 :
    (∫ x in (459/512:ℝ)..(115/128:ℝ), x^2*thetaFirstMode x) ≤ (1889958507529/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (459/512:ℝ) (115/128:ℝ)
    (996569/50000000000000:ℝ) (1853031/100000000000000:ℝ) (24504501761032275709/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_459 (thetaFirstMode_refined_node_1375).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_460 :
    (28231191879423/1000000000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(461/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-32327527429382337383/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (115/128:ℝ) (461/512:ℝ)-(461/512:ℝ)*thetaPowerMass 2 (115/128:ℝ) (461/512:ℝ)) ≤
      thetaFirstModeFirst (461/512:ℝ)*(thetaPowerMass 3 (115/128:ℝ) (461/512:ℝ)-(461/512:ℝ)*thetaPowerMass 2 (115/128:ℝ) (461/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0695.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (115/128:ℝ) (461/512:ℝ)
    (461/512:ℝ) (1722263/100000000000000:ℝ) (-32327527429382337383/50000000000000000000000000:ℝ) (4592334517383534719/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_460
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1381).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_460 :
    (∫ x in (115/128:ℝ)..(461/512:ℝ), x^2*thetaFirstMode x) ≤ (14116069669047/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (115/128:ℝ) (461/512:ℝ)
    (1853031/100000000000000:ℝ) (861137/50000000000000:ℝ) (4592334517383534719/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_460 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1381).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_461 :
    (3293584250513/125000000000000000000000:ℝ) ≤ ∫ x in (461/512:ℝ)..(231/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-4039347728469461010626529/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (461/512:ℝ) (231/256:ℝ)-(165312387803273059105209/183598439372905969845760:ℝ)*thetaPowerMass 2 (461/512:ℝ) (231/256:ℝ)) ≤
      thetaFirstModeFirst (165312387803273059105209/183598439372905969845760:ℝ)*(thetaPowerMass 3 (461/512:ℝ) (231/256:ℝ)-(165312387803273059105209/183598439372905969845760:ℝ)*thetaPowerMass 2 (461/512:ℝ) (231/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0696.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (461/512:ℝ) (231/256:ℝ)
    (165312387803273059105209/183598439372905969845760:ℝ) (430383/25000000000000:ℝ) (-4039347728469461010626529/6250000000000000000000000000000:ℝ) (21509694396691431421/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_461
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1385).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_461 :
    (∫ x in (461/512:ℝ)..(231/256:ℝ), x^2*thetaFirstMode x) ≤ (26350292301027/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (461/512:ℝ) (231/256:ℝ)
    (861137/50000000000000:ℝ) (40007/2500000000000:ℝ) (21509694396691431421/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_461 (thetaFirstMode_refined_node_1381).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_462 :
    (2458566246207/100000000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(463/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-7030904549700312181/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (231/256:ℝ) (463/512:ℝ)-(463/512:ℝ)*thetaPowerMass 2 (231/256:ℝ) (463/512:ℝ)) ≤
      thetaFirstModeFirst (463/512:ℝ)*(thetaPowerMass 3 (231/256:ℝ) (463/512:ℝ)-(463/512:ℝ)*thetaPowerMass 2 (231/256:ℝ) (463/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0698.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (231/256:ℝ) (463/512:ℝ)
    (463/512:ℝ) (371621/25000000000000:ℝ) (-7030904549700312181/12500000000000000000000000:ℝ) (2517955737992315821/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_462
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1387).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_462 :
    (∫ x in (231/256:ℝ)..(463/512:ℝ), x^2*thetaFirstMode x) ≤ (3073313351159/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (231/256:ℝ) (463/512:ℝ)
    (40007/2500000000000:ℝ) (743247/50000000000000:ℝ) (2517955737992315821/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_462 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1387).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_463 :
    (5733106737121/250000000000000000000000:ℝ) ≤ ∫ x in (463/512:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x := by
  have hd : (-14056240598261792362790163/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (463/512:ℝ) (29/32:ℝ)-(171880171452079192654407/190068149254242844572160:ℝ)*thetaPowerMass 2 (463/512:ℝ) (29/32:ℝ)) ≤
      thetaFirstModeFirst (171880171452079192654407/190068149254242844572160:ℝ)*(thetaPowerMass 3 (463/512:ℝ) (29/32:ℝ)-(171880171452079192654407/190068149254242844572160:ℝ)*thetaPowerMass 2 (463/512:ℝ) (29/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0699.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (463/512:ℝ) (29/32:ℝ)
    (171880171452079192654407/190068149254242844572160:ℝ) (1485851/100000000000000:ℝ) (-14056240598261792362790163/25000000000000000000000000000000:ℝ) (589337504137818281/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_463
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1391).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_463 :
    (∫ x in (463/512:ℝ)..(29/32:ℝ), x^2*thetaFirstMode x) ≤ (4586773066757/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (463/512:ℝ) (29/32:ℝ)
    (743247/50000000000000:ℝ) (690197/50000000000000:ℝ) (589337504137818281/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_463 (thetaFirstMode_refined_node_1387).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_464 :
    (21385097169449/1000000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(465/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-4887551894124569229/10000000000000000000000000:ℝ)*(thetaPowerMass 3 (29/32:ℝ) (465/512:ℝ)-(465/512:ℝ)*thetaPowerMass 2 (29/32:ℝ) (465/512:ℝ)) ≤
      thetaFirstModeFirst (465/512:ℝ)*(thetaPowerMass 3 (29/32:ℝ) (465/512:ℝ)-(465/512:ℝ)*thetaPowerMass 2 (29/32:ℝ) (465/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0701.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (29/32:ℝ) (465/512:ℝ)
    (465/512:ℝ) (1281483/100000000000000:ℝ) (-4887551894124569229/10000000000000000000000000:ℝ) (1103169072384304323/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_464
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1393).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_464 :
    (∫ x in (29/32:ℝ)..(465/512:ℝ), x^2*thetaFirstMode x) ≤ (10692919694957/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (29/32:ℝ) (465/512:ℝ)
    (690197/50000000000000:ℝ) (1281491/100000000000000:ℝ) (1103169072384304323/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_464 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1393).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_465 :
    (19934979226479/1000000000000000000000000:ℝ) ≤ ∫ x in (465/512:ℝ)..(233/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-95422043151049020597989/195312500000000000000000000000:ℝ)*(thetaPowerMass 3 (465/512:ℝ) (233/256:ℝ)-(35735776399208126994885/39347294353086520381952:ℝ)*thetaPowerMass 2 (465/512:ℝ) (233/256:ℝ)) ≤
      thetaFirstModeFirst (35735776399208126994885/39347294353086520381952:ℝ)*(thetaPowerMass 3 (465/512:ℝ) (233/256:ℝ)-(35735776399208126994885/39347294353086520381952:ℝ)*thetaPowerMass 2 (465/512:ℝ) (233/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0702.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (465/512:ℝ) (233/256:ℝ)
    (35735776399208126994885/39347294353086520381952:ℝ) (256187/20000000000000:ℝ) (-95422043151049020597989/195312500000000000000000000000:ℝ) (8257550955968549439/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_465
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1397).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_465 :
    (∫ x in (465/512:ℝ)..(233/256:ℝ), x^2*thetaFirstMode x) ≤ (4984064954163/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (465/512:ℝ) (233/256:ℝ)
    (1281491/100000000000000:ℝ) (297331/25000000000000:ℝ) (8257550955968549439/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_465 (thetaFirstMode_refined_node_1393).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_466 :
    (18578602839843/1000000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(467/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-21209909695580947857/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (233/256:ℝ) (467/512:ℝ)-(467/512:ℝ)*thetaPowerMass 2 (233/256:ℝ) (467/512:ℝ)) ≤
      thetaFirstModeFirst (467/512:ℝ)*(thetaPowerMass 3 (233/256:ℝ) (467/512:ℝ)-(467/512:ℝ)*thetaPowerMass 2 (233/256:ℝ) (467/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0704.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (233/256:ℝ) (467/512:ℝ)
    (467/512:ℝ) (1103451/100000000000000:ℝ) (-21209909695580947857/50000000000000000000000000:ℝ) (15447963605229410411/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_466
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1399).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_466 :
    (∫ x in (233/256:ℝ)..(467/512:ℝ), x^2*thetaFirstMode x) ≤ (2322409746391/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (233/256:ℝ) (467/512:ℝ)
    (297331/25000000000000:ℝ) (1103459/100000000000000:ℝ) (15447963605229410411/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_466 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1399).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_467 :
    (17308222399623/1000000000000000000000000:ℝ) ≤ ∫ x in (467/512:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-5300364402117373609737747/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (467/512:ℝ) (117/128:ℝ)-(185715593048194171355943/203608610322761788188160:ℝ)*thetaPowerMass 2 (467/512:ℝ) (117/128:ℝ)) ≤
      thetaFirstModeFirst (185715593048194171355943/203608610322761788188160:ℝ)*(thetaPowerMass 3 (467/512:ℝ) (117/128:ℝ)-(185715593048194171355943/203608610322761788188160:ℝ)*thetaPowerMass 2 (467/512:ℝ) (117/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0705.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (467/512:ℝ) (117/128:ℝ)
    (185715593048194171355943/203608610322761788188160:ℝ) (551489/50000000000000:ℝ) (-5300364402117373609737747/12500000000000000000000000000000:ℝ) (14445480376358809353/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_467
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1403).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_467 :
    (∫ x in (467/512:ℝ)..(117/128:ℝ), x^2*thetaFirstMode x) ≤ (4327341614669/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (467/512:ℝ) (117/128:ℝ)
    (1103459/100000000000000:ℝ) (1023489/100000000000000:ℝ) (14445480376358809353/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_467 (thetaFirstMode_refined_node_1399).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_468 :
    (8060358120089/500000000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(469/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-45966380696732727/125000000000000000000000:ℝ)*(thetaPowerMass 3 (117/128:ℝ) (469/512:ℝ)-(469/512:ℝ)*thetaPowerMass 2 (117/128:ℝ) (469/512:ℝ)) ≤
      thetaFirstModeFirst (469/512:ℝ)*(thetaPowerMass 3 (117/128:ℝ) (469/512:ℝ)-(469/512:ℝ)*thetaPowerMass 2 (117/128:ℝ) (469/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0707.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (117/128:ℝ) (469/512:ℝ)
    (469/512:ℝ) (37961/4000000000000:ℝ) (-45966380696732727/125000000000000000000000:ℝ) (3376000050664325273/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_468
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1405).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_468 :
    (∫ x in (117/128:ℝ)..(469/512:ℝ), x^2*thetaFirstMode x) ≤ (16121303361437/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (117/128:ℝ) (469/512:ℝ)
    (1023489/100000000000000:ℝ) (949031/100000000000000:ℝ) (3376000050664325273/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_468 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1405).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_469 :
    (3001830004299/200000000000000000000000:ℝ) ≤ ∫ x in (469/512:ℝ)..(235/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-4594795814467300481242593/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (469/512:ℝ) (235/256:ℝ)-(192997563136753342300641/210689881453211795484160:ℝ)*thetaPowerMass 2 (469/512:ℝ) (235/256:ℝ)) ≤
      thetaFirstModeFirst (192997563136753342300641/210689881453211795484160:ℝ)*(thetaPowerMass 3 (469/512:ℝ) (235/256:ℝ)-(192997563136753342300641/210689881453211795484160:ℝ)*thetaPowerMass 2 (469/512:ℝ) (235/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0708.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (469/512:ℝ) (235/256:ℝ)
    (192997563136753342300641/210689881453211795484160:ℝ) (118577/12500000000000:ℝ) (-4594795814467300481242593/12500000000000000000000000000000:ℝ) (6310040703464386403/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_469
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1409).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_469 :
    (∫ x in (469/512:ℝ)..(235/256:ℝ), x^2*thetaFirstMode x) ≤ (1501016409309/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (469/512:ℝ) (235/256:ℝ)
    (949031/100000000000000:ℝ) (879727/100000000000000:ℝ) (6310040703464386403/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_469 (thetaFirstMode_refined_node_1405).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_470 :
    (6985384642529/500000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(471/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-15919921925517906819/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (235/256:ℝ) (471/512:ℝ)-(471/512:ℝ)*thetaPowerMass 2 (235/256:ℝ) (471/512:ℝ)) ≤
      thetaFirstModeFirst (471/512:ℝ)*(thetaPowerMass 3 (235/256:ℝ) (471/512:ℝ)-(471/512:ℝ)*thetaPowerMass 2 (235/256:ℝ) (471/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0710.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (235/256:ℝ) (471/512:ℝ)
    (471/512:ℝ) (815233/100000000000000:ℝ) (-15919921925517906819/50000000000000000000000000:ℝ) (589523037444283507/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_470
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1411).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_470 :
    (∫ x in (235/256:ℝ)..(471/512:ℝ), x^2*thetaFirstMode x) ≤ (13971296382423/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (235/256:ℝ) (471/512:ℝ)
    (879727/100000000000000:ℝ) (815239/100000000000000:ℝ) (589523037444283507/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_470 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1411).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_471 :
    (1624924309847/125000000000000000000000:ℝ) ≤ ∫ x in (471/512:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-15913526783585675278320063/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (471/512:ℝ) (59/64:ℝ)-(200532239716009818864159/217985716752994642792960:ℝ)*thetaPowerMass 2 (471/512:ℝ) (59/64:ℝ)) ≤
      thetaFirstModeFirst (200532239716009818864159/217985716752994642792960:ℝ)*(thetaPowerMass 3 (471/512:ℝ) (59/64:ℝ)-(200532239716009818864159/217985716752994642792960:ℝ)*thetaPowerMass 2 (471/512:ℝ) (59/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0711.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (471/512:ℝ) (59/64:ℝ)
    (200532239716009818864159/217985716752994642792960:ℝ) (814881/100000000000000:ℝ) (-15913526783585675278320063/50000000000000000000000000000000:ℝ) (11012034271656253791/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_471
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1415).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_471 :
    (∫ x in (471/512:ℝ)..(59/64:ℝ), x^2*thetaFirstMode x) ≤ (13000294532953/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (471/512:ℝ) (59/64:ℝ)
    (815239/100000000000000:ℝ) (3021/400000000000:ℝ) (11012034271656253791/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_471 (thetaFirstMode_refined_node_1411).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_472 :
    (12092537691467/1000000000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(473/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-172094514651577977/625000000000000000000000:ℝ)*(thetaPowerMass 3 (59/64:ℝ) (473/512:ℝ)-(473/512:ℝ)*thetaPowerMass 2 (59/64:ℝ) (473/512:ℝ)) ≤
      thetaFirstModeFirst (473/512:ℝ)*(thetaPowerMass 3 (59/64:ℝ) (473/512:ℝ)-(473/512:ℝ)*thetaPowerMass 2 (59/64:ℝ) (473/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0713.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (59/64:ℝ) (473/512:ℝ)
    (473/512:ℝ) (349729/50000000000000:ℝ) (-172094514651577977/625000000000000000000000:ℝ) (2056376216470054499/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_472
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1417).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_472 :
    (∫ x in (59/64:ℝ)..(473/512:ℝ), x^2*thetaFirstMode x) ≤ (1511625760959/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (59/64:ℝ) (473/512:ℝ)
    (3021/400000000000:ℝ) (699463/100000000000000:ℝ) (2056376216470054499/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_472 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1417).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_473 :
    (224894607611/20000000000000000000000:ℝ) ≤ ∫ x in (473/512:ℝ)..(237/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-344050173313491711150469/1250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (473/512:ℝ) (237/256:ℝ)-(208327263246534084091857/225501664871413871772160:ℝ)*thetaPowerMass 2 (473/512:ℝ) (237/256:ℝ)) ≤
      thetaFirstModeFirst (208327263246534084091857/225501664871413871772160:ℝ)*(thetaPowerMass 3 (473/512:ℝ) (237/256:ℝ)-(208327263246534084091857/225501664871413871772160:ℝ)*thetaPowerMass 2 (473/512:ℝ) (237/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0714.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (473/512:ℝ) (237/256:ℝ)
    (208327263246534084091857/225501664871413871772160:ℝ) (139831/20000000000000:ℝ) (-344050173313491711150469/1250000000000000000000000000000:ℝ) (2343066204438221/244140625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_473
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1421).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_473 :
    (∫ x in (473/512:ℝ)..(237/256:ℝ), x^2*thetaFirstMode x) ≤ (5622760946617/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (473/512:ℝ) (237/256:ℝ)
    (699463/100000000000000:ℝ) (1619/250000000000:ℝ) (2343066204438221/244140625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_473 (thetaFirstMode_refined_node_1417).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_474 :
    (326679343669/31250000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(475/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2378342159452595197/10000000000000000000000000:ℝ)*(thetaPowerMass 3 (237/256:ℝ) (475/512:ℝ)-(475/512:ℝ)*thetaPowerMass 2 (237/256:ℝ) (475/512:ℝ)) ≤
      thetaFirstModeFirst (475/512:ℝ)*(thetaPowerMass 3 (237/256:ℝ) (475/512:ℝ)-(475/512:ℝ)*thetaPowerMass 2 (237/256:ℝ) (475/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0716.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (237/256:ℝ) (475/512:ℝ)
    (475/512:ℝ) (119879/20000000000000:ℝ) (-2378342159452595197/10000000000000000000000000:ℝ) (8955372340503951647/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_474
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1423).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_474 :
    (∫ x in (237/256:ℝ)..(475/512:ℝ), x^2*thetaFirstMode x) ≤ (2613539330927/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (237/256:ℝ) (475/512:ℝ)
    (1619/250000000000:ℝ) (2997/500000000000:ℝ) (8955372340503951647/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_474 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1423).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_475 :
    (607169119331/62500000000000000000000:ℝ) ≤ ∫ x in (475/512:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-11886899664204266836359249/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (475/512:ℝ) (119/128:ℝ)-(43278094269113915002275/46648678704053587338752:ℝ)*thetaPowerMass 2 (475/512:ℝ) (119/128:ℝ)) ≤
      thetaFirstModeFirst (43278094269113915002275/46648678704053587338752:ℝ)*(thetaPowerMass 3 (475/512:ℝ) (119/128:ℝ)-(43278094269113915002275/46648678704053587338752:ℝ)*thetaPowerMass 2 (475/512:ℝ) (119/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0717.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (475/512:ℝ) (119/128:ℝ)
    (43278094269113915002275/46648678704053587338752:ℝ) (299567/50000000000000:ℝ) (-11886899664204266836359249/50000000000000000000000000000000:ℝ) (8353889591520146871/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_475
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1427).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_475 :
    (∫ x in (475/512:ℝ)..(119/128:ℝ), x^2*thetaFirstMode x) ≤ (9715416143123/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (475/512:ℝ) (119/128:ℝ)
    (2997/500000000000:ℝ) (69327/12500000000000:ℝ) (8353889591520146871/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_475 (thetaFirstMode_refined_node_1423).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_476 :
    (9025653404461/1000000000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(477/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1282355693078495357/6250000000000000000000000:ℝ)*(thetaPowerMass 3 (119/128:ℝ) (477/512:ℝ)-(477/512:ℝ)*thetaPowerMass 2 (119/128:ℝ) (477/512:ℝ)) ≤
      thetaFirstModeFirst (477/512:ℝ)*(thetaPowerMass 3 (119/128:ℝ) (477/512:ℝ)-(477/512:ℝ)*thetaPowerMass 2 (119/128:ℝ) (477/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0719.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (119/128:ℝ) (477/512:ℝ)
    (477/512:ℝ) (513017/100000000000000:ℝ) (-1282355693078495357/6250000000000000000000000:ℝ) (7790397053757855993/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_476
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1429).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_476 :
    (∫ x in (119/128:ℝ)..(477/512:ℝ), x^2*thetaFirstMode x) ≤ (1805204200017/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (119/128:ℝ) (477/512:ℝ)
    (69327/12500000000000:ℝ) (513021/100000000000000:ℝ) (7790397053757855993/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_476 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1429).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_477 :
    (8382267852493/1000000000000000000000000:ℝ) ≤ ∫ x in (477/512:ℝ)..(239/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-205093524455116597851793/1000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (477/512:ℝ) (239/256:ℝ)-(224729903008522098228393/241216691509014397212160:ℝ)*thetaPowerMass 2 (477/512:ℝ) (239/256:ℝ)) ≤
      thetaFirstModeFirst (224729903008522098228393/241216691509014397212160:ℝ)*(thetaPowerMass 3 (477/512:ℝ) (239/256:ℝ)-(224729903008522098228393/241216691509014397212160:ℝ)*thetaPowerMass 2 (477/512:ℝ) (239/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0720.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (477/512:ℝ) (239/256:ℝ)
    (224729903008522098228393/241216691509014397212160:ℝ) (512793/100000000000000:ℝ) (-205093524455116597851793/1000000000000000000000000000000:ℝ) (1452532084929160941/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_477
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1433).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_477 :
    (∫ x in (477/512:ℝ)..(239/256:ℝ), x^2*thetaFirstMode x) ≤ (4191446769661/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (477/512:ℝ) (239/256:ℝ)
    (513021/100000000000000:ℝ) (474399/100000000000000:ℝ) (1452532084929160941/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_477 (thetaFirstMode_refined_node_1429).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_478 :
    (7782787723851/1000000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(479/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1767852675261647937/10000000000000000000000000:ℝ)*(thetaPowerMass 3 (239/256:ℝ) (479/512:ℝ)-(479/512:ℝ)*thetaPowerMass 2 (239/256:ℝ) (479/512:ℝ)) ≤
      thetaFirstModeFirst (479/512:ℝ)*(thetaPowerMass 3 (239/256:ℝ) (479/512:ℝ)-(479/512:ℝ)*thetaPowerMass 2 (239/256:ℝ) (479/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0722.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (239/256:ℝ) (479/512:ℝ)
    (479/512:ℝ) (87709/20000000000000:ℝ) (-1767852675261647937/10000000000000000000000000:ℝ) (6768571694957169177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_478
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1435).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_478 :
    (∫ x in (239/256:ℝ)..(479/512:ℝ), x^2*thetaFirstMode x) ≤ (77831169929/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (239/256:ℝ) (479/512:ℝ)
    (474399/100000000000000:ℝ) (438549/100000000000000:ℝ) (6768571694957169177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_478 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1435).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_479 :
    (3611693502419/500000000000000000000000:ℝ) ≤ ∫ x in (479/512:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1767134288055586409173623/10000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (479/512:ℝ) (15/16:ℝ)-(233353802902454023413591/249427470805914151528960:ℝ)*thetaPowerMass 2 (479/512:ℝ) (15/16:ℝ)) ≤
      thetaFirstModeFirst (233353802902454023413591/249427470805914151528960:ℝ)*(thetaPowerMass 3 (479/512:ℝ) (15/16:ℝ)-(233353802902454023413591/249427470805914151528960:ℝ)*thetaPowerMass 2 (479/512:ℝ) (15/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0723.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (479/512:ℝ) (15/16:ℝ)
    (233353802902454023413591/249427470805914151528960:ℝ) (438353/100000000000000:ℝ) (-1767134288055586409173623/10000000000000000000000000000000:ℝ) (3153062464355029157/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_479
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1439).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_479 :
    (∫ x in (479/512:ℝ)..(15/16:ℝ), x^2*thetaFirstMode x) ≤ (180598511353/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (479/512:ℝ) (15/16:ℝ)
    (438549/100000000000000:ℝ) (405281/100000000000000:ℝ) (3153062464355029157/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_479 (thetaFirstMode_refined_node_1435).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

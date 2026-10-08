import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature14
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative21
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative22

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_6_448 :
    (37169209301707/1000000000000000000000000:ℝ) ≤ ∫ x in (7/8:ℝ)..(449/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-142184216259104877/97656250000000000000000:ℝ)*(thetaPowerMass 7 (7/8:ℝ) (449/512:ℝ)-(449/512:ℝ)*thetaPowerMass 6 (7/8:ℝ) (449/512:ℝ)) ≤
      thetaFirstModeFirst (449/512:ℝ)*(thetaPowerMass 7 (7/8:ℝ) (449/512:ℝ)-(449/512:ℝ)*thetaPowerMass 6 (7/8:ℝ) (449/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0677.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (7/8:ℝ) (449/512:ℝ)
    (449/512:ℝ) (254193/6250000000000:ℝ) (-142184216259104877/97656250000000000000000:ℝ) (24584581102903339971/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_448
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1345).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_448 :
    (∫ x in (7/8:ℝ)..(449/512:ℝ), x^6*thetaFirstMode x) ≤ (7434057930671/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/8:ℝ) (449/512:ℝ)
    (136283/3125000000000:ℝ) (508389/12500000000000:ℝ) (24584581102903339971/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_448 (thetaFirstMode_refined_node_1344).2 (thetaFirstMode_refined_node_1345).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_449 :
    (35124608976579/1000000000000000000000000:ℝ) ≤ ∫ x in (449/512:ℝ)..(225/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2274070919420238827123631/1562500000000000000000000000000:ℝ)*(thetaPowerMass 7 (449/512:ℝ) (225/256:ℝ)-(130381348261662627095241/148673423925516220418560:ℝ)*thetaPowerMass 6 (449/512:ℝ) (225/256:ℝ)) ≤
      thetaFirstModeFirst (130381348261662627095241/148673423925516220418560:ℝ)*(thetaPowerMass 7 (449/512:ℝ) (225/256:ℝ)-(130381348261662627095241/148673423925516220418560:ℝ)*thetaPowerMass 6 (449/512:ℝ) (225/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0678.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (449/512:ℝ) (225/256:ℝ)
    (130381348261662627095241/148673423925516220418560:ℝ) (4065399/100000000000000:ℝ) (-2274070919420238827123631/1562500000000000000000000000000:ℝ) (46218050966034724083/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_449
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1349).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_449 :
    (∫ x in (449/512:ℝ)..(225/256:ℝ), x^6*thetaFirstMode x) ≤ (35126468982393/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (449/512:ℝ) (225/256:ℝ)
    (508389/12500000000000:ℝ) (379193/10000000000000:ℝ) (46218050966034724083/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_449 (thetaFirstMode_refined_node_1345).2 (thetaFirstMode_refined_node_1350).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_450 :
    (33183836431531/1000000000000000000000000:ℝ) ≤ ∫ x in (225/256:ℝ)..(451/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-797074562701286519/625000000000000000000000:ℝ)*(thetaPowerMass 7 (225/256:ℝ) (451/512:ℝ)-(451/512:ℝ)*thetaPowerMass 6 (225/256:ℝ) (451/512:ℝ)) ≤
      thetaFirstModeFirst (451/512:ℝ)*(thetaPowerMass 7 (225/256:ℝ) (451/512:ℝ)-(451/512:ℝ)*thetaPowerMass 6 (225/256:ℝ) (451/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0680.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (225/256:ℝ) (451/512:ℝ)
    (451/512:ℝ) (1767181/50000000000000:ℝ) (-797074562701286519/625000000000000000000000:ℝ) (10857980484460440403/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_450
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1351).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_450 :
    (∫ x in (225/256:ℝ)..(451/512:ℝ), x^6*thetaFirstMode x) ≤ (8296208149193/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (225/256:ℝ) (451/512:ℝ)
    (379193/10000000000000:ℝ) (220899/6250000000000:ℝ) (10857980484460440403/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_450 (thetaFirstMode_refined_node_1350).2 (thetaFirstMode_refined_node_1351).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_451 :
    (31339163597683/1000000000000000000000000:ℝ) ≤ ∫ x in (451/512:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-398383235380354727994879/312500000000000000000000000000:ℝ)*(thetaPowerMass 7 (451/512:ℝ) (113/128:ℝ)-(135702249480635062632759/154054636064115110786560:ℝ)*thetaPowerMass 6 (451/512:ℝ) (113/128:ℝ)) ≤
      thetaFirstModeFirst (135702249480635062632759/154054636064115110786560:ℝ)*(thetaPowerMass 7 (451/512:ℝ) (113/128:ℝ)-(135702249480635062632759/154054636064115110786560:ℝ)*thetaPowerMass 6 (451/512:ℝ) (113/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0681.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (451/512:ℝ) (113/128:ℝ)
    (135702249480635062632759/154054636064115110786560:ℝ) (353289/10000000000000:ℝ) (-398383235380354727994879/312500000000000000000000000000:ℝ) (40802309277093263701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_451
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1355).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_451 :
    (∫ x in (451/512:ℝ)..(113/128:ℝ), x^6*thetaFirstMode x) ≤ (3134086245763/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (451/512:ℝ) (113/128:ℝ)
    (220899/6250000000000:ℝ) (3293411/100000000000000:ℝ) (40802309277093263701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_451 (thetaFirstMode_refined_node_1351).2 (thetaFirstMode_refined_node_1356).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_452 :
    (2958930609937/100000000000000000000000:ℝ) ≤ ∫ x in (113/128:ℝ)..(453/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-55791939676208617551/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (113/128:ℝ) (453/512:ℝ)-(453/512:ℝ)*thetaPowerMass 6 (113/128:ℝ) (453/512:ℝ)) ≤
      thetaFirstModeFirst (453/512:ℝ)*(thetaPowerMass 7 (113/128:ℝ) (453/512:ℝ)-(453/512:ℝ)*thetaPowerMass 6 (113/128:ℝ) (453/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0683.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (113/128:ℝ) (453/512:ℝ)
    (453/512:ℝ) (3067989/100000000000000:ℝ) (-55791939676208617551/50000000000000000000000000:ℝ) (9580276645360851979/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_452
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1357).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_452 :
    (∫ x in (113/128:ℝ)..(453/512:ℝ), x^6*thetaFirstMode x) ≤ (7397552481581/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (113/128:ℝ) (453/512:ℝ)
    (3293411/100000000000000:ℝ) (383501/12500000000000:ℝ) (9580276645360851979/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_452 (thetaFirstMode_refined_node_1356).2 (thetaFirstMode_refined_node_1357).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_453 :
    (27927131693991/1000000000000000000000000:ℝ) ≤ ∫ x in (453/512:ℝ)..(227/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1115405432254215581692793/1000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (453/512:ℝ) (227/256:ℝ)-(141215303034674977169457/159605509118049574428160:ℝ)*thetaPowerMass 6 (453/512:ℝ) (227/256:ℝ)) ≤
      thetaFirstModeFirst (141215303034674977169457/159605509118049574428160:ℝ)*(thetaPowerMass 7 (453/512:ℝ) (227/256:ℝ)-(141215303034674977169457/159605509118049574428160:ℝ)*thetaPowerMass 6 (453/512:ℝ) (227/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0684.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (453/512:ℝ) (227/256:ℝ)
    (141215303034674977169457/159605509118049574428160:ℝ) (1533353/50000000000000:ℝ) (-1115405432254215581692793/1000000000000000000000000000000:ℝ) (719612273135570069/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_453
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1361).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_453 :
    (∫ x in (453/512:ℝ)..(227/256:ℝ), x^6*thetaFirstMode x) ≤ (3491086004217/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (453/512:ℝ) (227/256:ℝ)
    (383501/12500000000000:ℝ) (714307/25000000000000:ℝ) (719612273135570069/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_453 (thetaFirstMode_refined_node_1357).2 (thetaFirstMode_refined_node_1362).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_454 :
    (3293929036031/125000000000000000000000:ℝ) ≤ ∫ x in (227/256:ℝ)..(455/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-76187694673310493/78125000000000000000000:ℝ)*(thetaPowerMass 7 (227/256:ℝ) (455/512:ℝ)-(455/512:ℝ)*thetaPowerMass 6 (227/256:ℝ) (455/512:ℝ)) ≤
      thetaFirstModeFirst (455/512:ℝ)*(thetaPowerMass 7 (227/256:ℝ) (455/512:ℝ)-(455/512:ℝ)*thetaPowerMass 6 (227/256:ℝ) (455/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0686.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (227/256:ℝ) (455/512:ℝ)
    (455/512:ℝ) (8313/312500000000:ℝ) (-76187694673310493/78125000000000000000000:ℝ) (33773470833088802241/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_454
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1363).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_454 :
    (∫ x in (227/256:ℝ)..(455/512:ℝ), x^6*thetaFirstMode x) ≤ (3294032774181/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (227/256:ℝ) (455/512:ℝ)
    (714307/25000000000000:ℝ) (2660177/100000000000000:ℝ) (33773470833088802241/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_454 (thetaFirstMode_refined_node_1362).2 (thetaFirstMode_refined_node_1363).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_455 :
    (6213910647543/250000000000000000000000:ℝ) ≤ ∫ x in (455/512:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-609264086806244446373891/625000000000000000000000000000:ℝ)*(thetaPowerMass 7 (455/512:ℝ) (57/64:ℝ)-(29385310700934990796995/33066121515527560919552:ℝ)*thetaPowerMass 6 (455/512:ℝ) (57/64:ℝ)) ≤
      thetaFirstModeFirst (29385310700934990796995/33066121515527560919552:ℝ)*(thetaPowerMass 7 (455/512:ℝ) (57/64:ℝ)-(29385310700934990796995/33066121515527560919552:ℝ)*thetaPowerMass 6 (455/512:ℝ) (57/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0687.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (455/512:ℝ) (57/64:ℝ)
    (29385310700934990796995/33066121515527560919552:ℝ) (664761/25000000000000:ℝ) (-609264086806244446373891/625000000000000000000000000000:ℝ) (7923176181761866589/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_455
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1367).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_455 :
    (∫ x in (455/512:ℝ)..(57/64:ℝ), x^6*thetaFirstMode x) ≤ (24857058583337/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (455/512:ℝ) (57/64:ℝ)
    (2660177/100000000000000:ℝ) (1238007/50000000000000:ℝ) (7923176181761866589/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_455 (thetaFirstMode_refined_node_1363).2 (thetaFirstMode_refined_node_1368).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_456 :
    (23438604573269/1000000000000000000000000:ℝ) ≤ ∫ x in (57/64:ℝ)..(457/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4256624562084654193/5000000000000000000000000:ℝ)*(thetaPowerMass 7 (57/64:ℝ) (457/512:ℝ)-(457/512:ℝ)*thetaPowerMass 6 (57/64:ℝ) (457/512:ℝ)) ≤
      thetaFirstModeFirst (457/512:ℝ)*(thetaPowerMass 7 (57/64:ℝ) (457/512:ℝ)-(457/512:ℝ)*thetaPowerMass 6 (57/64:ℝ) (457/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0689.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (57/64:ℝ) (457/512:ℝ)
    (457/512:ℝ) (230393/10000000000000:ℝ) (-4256624562084654193/5000000000000000000000000:ℝ) (3716451004630729741/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_456
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1369).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_456 :
    (∫ x in (57/64:ℝ)..(457/512:ℝ), x^6*thetaFirstMode x) ≤ (4687871507051/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (57/64:ℝ) (457/512:ℝ)
    (1238007/50000000000000:ℝ) (460789/20000000000000:ℝ) (3716451004630729741/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_456 (thetaFirstMode_refined_node_1368).2 (thetaFirstMode_refined_node_1369).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_457 :
    (1104714287933/50000000000000000000000:ℝ) ≤ ∫ x in (457/512:ℝ)..(229/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-425495981963120782550659/500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (457/512:ℝ) (229/256:ℝ)-(152842207727465608740993/171234597812449350300160:ℝ)*thetaPowerMass 6 (457/512:ℝ) (229/256:ℝ)) ≤
      thetaFirstModeFirst (152842207727465608740993/171234597812449350300160:ℝ)*(thetaPowerMass 7 (457/512:ℝ) (229/256:ℝ)-(152842207727465608740993/171234597812449350300160:ℝ)*thetaPowerMass 6 (457/512:ℝ) (229/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0690.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (457/512:ℝ) (229/256:ℝ)
    (152842207727465608740993/171234597812449350300160:ℝ) (28787/1250000000000:ℝ) (-425495981963120782550659/500000000000000000000000000000:ℝ) (435685314641347487/15625000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_457
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1373).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_457 :
    (∫ x in (457/512:ℝ)..(229/256:ℝ), x^6*thetaFirstMode x) ≤ (22095575593687/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (457/512:ℝ) (229/256:ℝ)
    (460789/20000000000000:ℝ) (2143221/100000000000000:ℝ) (435685314641347487/15625000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_457 (thetaFirstMode_refined_node_1369).2 (thetaFirstMode_refined_node_1374).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_458 :
    (166572756247/8000000000000000000000:ℝ) ≤ ∫ x in (229/256:ℝ)..(459/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-11877341328394317/16000000000000000000000:ℝ)*(thetaPowerMass 7 (229/256:ℝ) (459/512:ℝ)-(459/512:ℝ)*thetaPowerMass 6 (229/256:ℝ) (459/512:ℝ)) ≤
      thetaFirstModeFirst (459/512:ℝ)*(thetaPowerMass 7 (229/256:ℝ) (459/512:ℝ)-(459/512:ℝ)*thetaPowerMass 6 (229/256:ℝ) (459/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0692.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (229/256:ℝ) (459/512:ℝ)
    (459/512:ℝ) (3189/160000000000:ℝ) (-11877341328394317/16000000000000000000000:ℝ) (26143417121733651497/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_458
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1375).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_458 :
    (∫ x in (229/256:ℝ)..(459/512:ℝ), x^6*thetaFirstMode x) ≤ (10411137783993/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (229/256:ℝ) (459/512:ℝ)
    (2143221/100000000000000:ℝ) (996569/50000000000000:ℝ) (26143417121733651497/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_458 (thetaFirstMode_refined_node_1374).2 (thetaFirstMode_refined_node_1375).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_459 :
    (19614983710283/1000000000000000000000000:ℝ) ≤ ∫ x in (459/512:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2318882435067136478747643/3125000000000000000000000000000:ℝ)*(thetaPowerMass 7 (459/512:ℝ) (115/128:ℝ)-(158968638409273606456191/177322249882403159887360:ℝ)*thetaPowerMass 6 (459/512:ℝ) (115/128:ℝ)) ≤
      thetaFirstModeFirst (158968638409273606456191/177322249882403159887360:ℝ)*(thetaPowerMass 7 (459/512:ℝ) (115/128:ℝ)-(158968638409273606456191/177322249882403159887360:ℝ)*thetaPowerMass 6 (459/512:ℝ) (115/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0693.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (459/512:ℝ) (115/128:ℝ)
    (158968638409273606456191/177322249882403159887360:ℝ) (1992283/100000000000000:ℝ) (-2318882435067136478747643/3125000000000000000000000000000:ℝ) (24504501761032275709/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_459
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1379).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_459 :
    (∫ x in (459/512:ℝ)..(115/128:ℝ), x^6*thetaFirstMode x) ≤ (980807803243/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (459/512:ℝ) (115/128:ℝ)
    (996569/50000000000000:ℝ) (1853031/100000000000000:ℝ) (24504501761032275709/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_459 (thetaFirstMode_refined_node_1375).2 (thetaFirstMode_refined_node_1380).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_460 :
    (9236710116437/500000000000000000000000:ℝ) ≤ ∫ x in (115/128:ℝ)..(461/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-32327527429382337383/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (115/128:ℝ) (461/512:ℝ)-(461/512:ℝ)*thetaPowerMass 6 (115/128:ℝ) (461/512:ℝ)) ≤
      thetaFirstModeFirst (461/512:ℝ)*(thetaPowerMass 7 (115/128:ℝ) (461/512:ℝ)-(461/512:ℝ)*thetaPowerMass 6 (115/128:ℝ) (461/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0695.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (115/128:ℝ) (461/512:ℝ)
    (461/512:ℝ) (1722263/100000000000000:ℝ) (-32327527429382337383/50000000000000000000000000:ℝ) (4592334517383534719/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_460
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1381).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_460 :
    (∫ x in (115/128:ℝ)..(461/512:ℝ), x^6*thetaFirstMode x) ≤ (9237019756603/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (115/128:ℝ) (461/512:ℝ)
    (1853031/100000000000000:ℝ) (861137/50000000000000:ℝ) (4592334517383534719/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_460 (thetaFirstMode_refined_node_1380).2 (thetaFirstMode_refined_node_1381).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_461 :
    (17391820325171/1000000000000000000000000:ℝ) ≤ ∫ x in (461/512:ℝ)..(231/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4039347728469461010626529/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (461/512:ℝ) (231/256:ℝ)-(165312387803273059105209/183598439372905969845760:ℝ)*thetaPowerMass 6 (461/512:ℝ) (231/256:ℝ)) ≤
      thetaFirstModeFirst (165312387803273059105209/183598439372905969845760:ℝ)*(thetaPowerMass 7 (461/512:ℝ) (231/256:ℝ)-(165312387803273059105209/183598439372905969845760:ℝ)*thetaPowerMass 6 (461/512:ℝ) (231/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0696.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (461/512:ℝ) (231/256:ℝ)
    (165312387803273059105209/183598439372905969845760:ℝ) (430383/25000000000000:ℝ) (-4039347728469461010626529/6250000000000000000000000000000:ℝ) (21509694396691431421/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_461
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1385).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_461 :
    (∫ x in (461/512:ℝ)..(231/256:ℝ), x^6*thetaFirstMode x) ≤ (4348222481781/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (461/512:ℝ) (231/256:ℝ)
    (861137/50000000000000:ℝ) (40007/2500000000000:ℝ) (21509694396691431421/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_461 (thetaFirstMode_refined_node_1381).2 (thetaFirstMode_refined_node_1386).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_462 :
    (16369232531211/1000000000000000000000000:ℝ) ≤ ∫ x in (231/256:ℝ)..(463/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-7030904549700312181/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (231/256:ℝ) (463/512:ℝ)-(463/512:ℝ)*thetaPowerMass 6 (231/256:ℝ) (463/512:ℝ)) ≤
      thetaFirstModeFirst (463/512:ℝ)*(thetaPowerMass 7 (231/256:ℝ) (463/512:ℝ)-(463/512:ℝ)*thetaPowerMass 6 (231/256:ℝ) (463/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0698.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (231/256:ℝ) (463/512:ℝ)
    (463/512:ℝ) (371621/25000000000000:ℝ) (-7030904549700312181/12500000000000000000000000:ℝ) (2517955737992315821/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_462
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1387).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_462 :
    (∫ x in (231/256:ℝ)..(463/512:ℝ), x^6*thetaFirstMode x) ≤ (2046224259117/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (231/256:ℝ) (463/512:ℝ)
    (40007/2500000000000:ℝ) (743247/50000000000000:ℝ) (2517955737992315821/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_462 (thetaFirstMode_refined_node_1386).2 (thetaFirstMode_refined_node_1387).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_463 :
    (15400978794477/1000000000000000000000000:ℝ) ≤ ∫ x in (463/512:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x := by
  have hd : (-14056240598261792362790163/25000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (463/512:ℝ) (29/32:ℝ)-(171880171452079192654407/190068149254242844572160:ℝ)*thetaPowerMass 6 (463/512:ℝ) (29/32:ℝ)) ≤
      thetaFirstModeFirst (171880171452079192654407/190068149254242844572160:ℝ)*(thetaPowerMass 7 (463/512:ℝ) (29/32:ℝ)-(171880171452079192654407/190068149254242844572160:ℝ)*thetaPowerMass 6 (463/512:ℝ) (29/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0699.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (463/512:ℝ) (29/32:ℝ)
    (171880171452079192654407/190068149254242844572160:ℝ) (1485851/100000000000000:ℝ) (-14056240598261792362790163/25000000000000000000000000000000:ℝ) (589337504137818281/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_463
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1391).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_463 :
    (∫ x in (463/512:ℝ)..(29/32:ℝ), x^6*thetaFirstMode x) ≤ (770097303279/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (463/512:ℝ) (29/32:ℝ)
    (743247/50000000000000:ℝ) (690197/50000000000000:ℝ) (589337504137818281/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_463 (thetaFirstMode_refined_node_1387).2 (thetaFirstMode_refined_node_1392).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_464 :
    (3621541460909/250000000000000000000000:ℝ) ≤ ∫ x in (29/32:ℝ)..(465/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4887551894124569229/10000000000000000000000000:ℝ)*(thetaPowerMass 7 (29/32:ℝ) (465/512:ℝ)-(465/512:ℝ)*thetaPowerMass 6 (29/32:ℝ) (465/512:ℝ)) ≤
      thetaFirstModeFirst (465/512:ℝ)*(thetaPowerMass 7 (29/32:ℝ) (465/512:ℝ)-(465/512:ℝ)*thetaPowerMass 6 (29/32:ℝ) (465/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0701.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (29/32:ℝ) (465/512:ℝ)
    (465/512:ℝ) (1281483/100000000000000:ℝ) (-4887551894124569229/10000000000000000000000000:ℝ) (1103169072384304323/62500000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_464
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1393).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_464 :
    (∫ x in (29/32:ℝ)..(465/512:ℝ), x^6*thetaFirstMode x) ≤ (362166701253/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (29/32:ℝ) (465/512:ℝ)
    (690197/50000000000000:ℝ) (1281491/100000000000000:ℝ) (1103169072384304323/62500000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_464 (thetaFirstMode_refined_node_1392).2 (thetaFirstMode_refined_node_1393).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_465 :
    (6810261349513/500000000000000000000000:ℝ) ≤ ∫ x in (465/512:ℝ)..(233/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-95422043151049020597989/195312500000000000000000000000:ℝ)*(thetaPowerMass 7 (465/512:ℝ) (233/256:ℝ)-(35735776399208126994885/39347294353086520381952:ℝ)*thetaPowerMass 6 (465/512:ℝ) (233/256:ℝ)) ≤
      thetaFirstModeFirst (35735776399208126994885/39347294353086520381952:ℝ)*(thetaPowerMass 7 (465/512:ℝ) (233/256:ℝ)-(35735776399208126994885/39347294353086520381952:ℝ)*thetaPowerMass 6 (465/512:ℝ) (233/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0702.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (465/512:ℝ) (233/256:ℝ)
    (35735776399208126994885/39347294353086520381952:ℝ) (256187/20000000000000:ℝ) (-95422043151049020597989/195312500000000000000000000000:ℝ) (8257550955968549439/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_465
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1397).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_465 :
    (∫ x in (465/512:ℝ)..(233/256:ℝ), x^6*thetaFirstMode x) ≤ (6810699410439/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (465/512:ℝ) (233/256:ℝ)
    (1281491/100000000000000:ℝ) (297331/25000000000000:ℝ) (8257550955968549439/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_465 (thetaFirstMode_refined_node_1393).2 (thetaFirstMode_refined_node_1398).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_466 :
    (12803210651887/1000000000000000000000000:ℝ) ≤ ∫ x in (233/256:ℝ)..(467/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-21209909695580947857/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (233/256:ℝ) (467/512:ℝ)-(467/512:ℝ)*thetaPowerMass 6 (233/256:ℝ) (467/512:ℝ)) ≤
      thetaFirstModeFirst (467/512:ℝ)*(thetaPowerMass 7 (233/256:ℝ) (467/512:ℝ)-(467/512:ℝ)*thetaPowerMass 6 (233/256:ℝ) (467/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0704.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (233/256:ℝ) (467/512:ℝ)
    (467/512:ℝ) (1103451/100000000000000:ℝ) (-21209909695580947857/50000000000000000000000000:ℝ) (15447963605229410411/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_466
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1399).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_466 :
    (∫ x in (233/256:ℝ)..(467/512:ℝ), x^6*thetaFirstMode x) ≤ (1600459424683/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (233/256:ℝ) (467/512:ℝ)
    (297331/25000000000000:ℝ) (1103459/100000000000000:ℝ) (15447963605229410411/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_466 (thetaFirstMode_refined_node_1398).2 (thetaFirstMode_refined_node_1399).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_467 :
    (1203034462129/100000000000000000000000:ℝ) ≤ ∫ x in (467/512:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-5300364402117373609737747/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (467/512:ℝ) (117/128:ℝ)-(185715593048194171355943/203608610322761788188160:ℝ)*thetaPowerMass 6 (467/512:ℝ) (117/128:ℝ)) ≤
      thetaFirstModeFirst (185715593048194171355943/203608610322761788188160:ℝ)*(thetaPowerMass 7 (467/512:ℝ) (117/128:ℝ)-(185715593048194171355943/203608610322761788188160:ℝ)*thetaPowerMass 6 (467/512:ℝ) (117/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0705.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (467/512:ℝ) (117/128:ℝ)
    (185715593048194171355943/203608610322761788188160:ℝ) (551489/50000000000000:ℝ) (-5300364402117373609737747/12500000000000000000000000000000:ℝ) (14445480376358809353/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_467
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1403).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_467 :
    (∫ x in (467/512:ℝ)..(117/128:ℝ), x^6*thetaFirstMode x) ≤ (6015570431869/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (467/512:ℝ) (117/128:ℝ)
    (1103459/100000000000000:ℝ) (1023489/100000000000000:ℝ) (14445480376358809353/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_467 (thetaFirstMode_refined_node_1399).2 (thetaFirstMode_refined_node_1404).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_468 :
    (11301129671613/1000000000000000000000000:ℝ) ≤ ∫ x in (117/128:ℝ)..(469/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-45966380696732727/125000000000000000000000:ℝ)*(thetaPowerMass 7 (117/128:ℝ) (469/512:ℝ)-(469/512:ℝ)*thetaPowerMass 6 (117/128:ℝ) (469/512:ℝ)) ≤
      thetaFirstModeFirst (469/512:ℝ)*(thetaPowerMass 7 (117/128:ℝ) (469/512:ℝ)-(469/512:ℝ)*thetaPowerMass 6 (117/128:ℝ) (469/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0707.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (117/128:ℝ) (469/512:ℝ)
    (469/512:ℝ) (37961/4000000000000:ℝ) (-45966380696732727/125000000000000000000000:ℝ) (3376000050664325273/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_468
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1405).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_468 :
    (∫ x in (117/128:ℝ)..(469/512:ℝ), x^6*thetaFirstMode x) ≤ (2825385199007/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (117/128:ℝ) (469/512:ℝ)
    (1023489/100000000000000:ℝ) (949031/100000000000000:ℝ) (3376000050664325273/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_468 (thetaFirstMode_refined_node_1404).2 (thetaFirstMode_refined_node_1405).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_469 :
    (5306003403679/500000000000000000000000:ℝ) ≤ ∫ x in (469/512:ℝ)..(235/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4594795814467300481242593/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (469/512:ℝ) (235/256:ℝ)-(192997563136753342300641/210689881453211795484160:ℝ)*thetaPowerMass 6 (469/512:ℝ) (235/256:ℝ)) ≤
      thetaFirstModeFirst (192997563136753342300641/210689881453211795484160:ℝ)*(thetaPowerMass 7 (469/512:ℝ) (235/256:ℝ)-(192997563136753342300641/210689881453211795484160:ℝ)*thetaPowerMass 6 (469/512:ℝ) (235/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0708.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (469/512:ℝ) (235/256:ℝ)
    (192997563136753342300641/210689881453211795484160:ℝ) (118577/12500000000000:ℝ) (-4594795814467300481242593/12500000000000000000000000000000:ℝ) (6310040703464386403/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_469
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1409).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_469 :
    (∫ x in (469/512:ℝ)..(235/256:ℝ), x^6*thetaFirstMode x) ≤ (2653181184401/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (469/512:ℝ) (235/256:ℝ)
    (949031/100000000000000:ℝ) (879727/100000000000000:ℝ) (6310040703464386403/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_469 (thetaFirstMode_refined_node_1405).2 (thetaFirstMode_refined_node_1410).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_470 :
    (498112998743/50000000000000000000000:ℝ) ≤ ∫ x in (235/256:ℝ)..(471/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-15919921925517906819/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (235/256:ℝ) (471/512:ℝ)-(471/512:ℝ)*thetaPowerMass 6 (235/256:ℝ) (471/512:ℝ)) ≤
      thetaFirstModeFirst (471/512:ℝ)*(thetaPowerMass 7 (235/256:ℝ) (471/512:ℝ)-(471/512:ℝ)*thetaPowerMass 6 (235/256:ℝ) (471/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0710.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (235/256:ℝ) (471/512:ℝ)
    (471/512:ℝ) (815233/100000000000000:ℝ) (-15919921925517906819/50000000000000000000000000:ℝ) (589523037444283507/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_470
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1411).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_470 :
    (∫ x in (235/256:ℝ)..(471/512:ℝ), x^6*thetaFirstMode x) ≤ (1992527084837/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (235/256:ℝ) (471/512:ℝ)
    (879727/100000000000000:ℝ) (815239/100000000000000:ℝ) (589523037444283507/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_470 (thetaFirstMode_refined_node_1410).2 (thetaFirstMode_refined_node_1411).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_471 :
    (116858108719/12500000000000000000000:ℝ) ≤ ∫ x in (471/512:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-15913526783585675278320063/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (471/512:ℝ) (59/64:ℝ)-(200532239716009818864159/217985716752994642792960:ℝ)*thetaPowerMass 6 (471/512:ℝ) (59/64:ℝ)) ≤
      thetaFirstModeFirst (200532239716009818864159/217985716752994642792960:ℝ)*(thetaPowerMass 7 (471/512:ℝ) (59/64:ℝ)-(200532239716009818864159/217985716752994642792960:ℝ)*thetaPowerMass 6 (471/512:ℝ) (59/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0711.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (471/512:ℝ) (59/64:ℝ)
    (200532239716009818864159/217985716752994642792960:ℝ) (814881/100000000000000:ℝ) (-15913526783585675278320063/50000000000000000000000000000000:ℝ) (11012034271656253791/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_471
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1415).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_471 :
    (∫ x in (471/512:ℝ)..(59/64:ℝ), x^6*thetaFirstMode x) ≤ (9349296829491/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (471/512:ℝ) (59/64:ℝ)
    (815239/100000000000000:ℝ) (3021/400000000000:ℝ) (11012034271656253791/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_471 (thetaFirstMode_refined_node_1411).2 (thetaFirstMode_refined_node_1416).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_472 :
    (1754097100961/200000000000000000000000:ℝ) ≤ ∫ x in (59/64:ℝ)..(473/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-172094514651577977/625000000000000000000000:ℝ)*(thetaPowerMass 7 (59/64:ℝ) (473/512:ℝ)-(473/512:ℝ)*thetaPowerMass 6 (59/64:ℝ) (473/512:ℝ)) ≤
      thetaFirstModeFirst (473/512:ℝ)*(thetaPowerMass 7 (59/64:ℝ) (473/512:ℝ)-(473/512:ℝ)*thetaPowerMass 6 (59/64:ℝ) (473/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0713.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (59/64:ℝ) (473/512:ℝ)
    (473/512:ℝ) (349729/50000000000000:ℝ) (-172094514651577977/625000000000000000000000:ℝ) (2056376216470054499/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_472
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1417).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_472 :
    (∫ x in (59/64:ℝ)..(473/512:ℝ), x^6*thetaFirstMode x) ≤ (175416496949/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (59/64:ℝ) (473/512:ℝ)
    (3021/400000000000:ℝ) (699463/100000000000000:ℝ) (2056376216470054499/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_472 (thetaFirstMode_refined_node_1416).2 (thetaFirstMode_refined_node_1417).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_473 :
    (4112423258393/500000000000000000000000:ℝ) ≤ ∫ x in (473/512:ℝ)..(237/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-344050173313491711150469/1250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (473/512:ℝ) (237/256:ℝ)-(208327263246534084091857/225501664871413871772160:ℝ)*thetaPowerMass 6 (473/512:ℝ) (237/256:ℝ)) ≤
      thetaFirstModeFirst (208327263246534084091857/225501664871413871772160:ℝ)*(thetaPowerMass 7 (473/512:ℝ) (237/256:ℝ)-(208327263246534084091857/225501664871413871772160:ℝ)*thetaPowerMass 6 (473/512:ℝ) (237/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0714.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (473/512:ℝ) (237/256:ℝ)
    (208327263246534084091857/225501664871413871772160:ℝ) (139831/20000000000000:ℝ) (-344050173313491711150469/1250000000000000000000000000000:ℝ) (2343066204438221/244140625000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_473
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1421).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_473 :
    (∫ x in (473/512:ℝ)..(237/256:ℝ), x^6*thetaFirstMode x) ≤ (411271311157/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (473/512:ℝ) (237/256:ℝ)
    (699463/100000000000000:ℝ) (1619/250000000000:ℝ) (2343066204438221/244140625000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_473 (thetaFirstMode_refined_node_1417).2 (thetaFirstMode_refined_node_1422).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_474 :
    (192777061877/25000000000000000000000:ℝ) ≤ ∫ x in (237/256:ℝ)..(475/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2378342159452595197/10000000000000000000000000:ℝ)*(thetaPowerMass 7 (237/256:ℝ) (475/512:ℝ)-(475/512:ℝ)*thetaPowerMass 6 (237/256:ℝ) (475/512:ℝ)) ≤
      thetaFirstModeFirst (475/512:ℝ)*(thetaPowerMass 7 (237/256:ℝ) (475/512:ℝ)-(475/512:ℝ)*thetaPowerMass 6 (237/256:ℝ) (475/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0716.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (237/256:ℝ) (475/512:ℝ)
    (475/512:ℝ) (119879/20000000000000:ℝ) (-2378342159452595197/10000000000000000000000000:ℝ) (8955372340503951647/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_474
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1423).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_474 :
    (∫ x in (237/256:ℝ)..(475/512:ℝ), x^6*thetaFirstMode x) ≤ (3855695359313/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (237/256:ℝ) (475/512:ℝ)
    (1619/250000000000:ℝ) (2997/500000000000:ℝ) (8955372340503951647/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_474 (thetaFirstMode_refined_node_1422).2 (thetaFirstMode_refined_node_1423).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_475 :
    (7226540787649/1000000000000000000000000:ℝ) ≤ ∫ x in (475/512:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-11886899664204266836359249/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (475/512:ℝ) (119/128:ℝ)-(43278094269113915002275/46648678704053587338752:ℝ)*thetaPowerMass 6 (475/512:ℝ) (119/128:ℝ)) ≤
      thetaFirstModeFirst (43278094269113915002275/46648678704053587338752:ℝ)*(thetaPowerMass 7 (475/512:ℝ) (119/128:ℝ)-(43278094269113915002275/46648678704053587338752:ℝ)*thetaPowerMass 6 (475/512:ℝ) (119/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0717.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (475/512:ℝ) (119/128:ℝ)
    (43278094269113915002275/46648678704053587338752:ℝ) (299567/50000000000000:ℝ) (-11886899664204266836359249/50000000000000000000000000000000:ℝ) (8353889591520146871/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_475
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1427).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_475 :
    (∫ x in (475/512:ℝ)..(119/128:ℝ), x^6*thetaFirstMode x) ≤ (7227069790243/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (475/512:ℝ) (119/128:ℝ)
    (2997/500000000000:ℝ) (69327/12500000000000:ℝ) (8353889591520146871/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_475 (thetaFirstMode_refined_node_1423).2 (thetaFirstMode_refined_node_1428).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_476 :
    (6770628647/1000000000000000000000:ℝ) ≤ ∫ x in (119/128:ℝ)..(477/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1282355693078495357/6250000000000000000000000:ℝ)*(thetaPowerMass 7 (119/128:ℝ) (477/512:ℝ)-(477/512:ℝ)*thetaPowerMass 6 (119/128:ℝ) (477/512:ℝ)) ≤
      thetaFirstModeFirst (477/512:ℝ)*(thetaPowerMass 7 (119/128:ℝ) (477/512:ℝ)-(477/512:ℝ)*thetaPowerMass 6 (119/128:ℝ) (477/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0719.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (119/128:ℝ) (477/512:ℝ)
    (477/512:ℝ) (513017/100000000000000:ℝ) (-1282355693078495357/6250000000000000000000000:ℝ) (7790397053757855993/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_476
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1429).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_476 :
    (∫ x in (119/128:ℝ)..(477/512:ℝ), x^6*thetaFirstMode x) ≤ (3385452050139/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (119/128:ℝ) (477/512:ℝ)
    (69327/12500000000000:ℝ) (513021/100000000000000:ℝ) (7790397053757855993/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_476 (thetaFirstMode_refined_node_1428).2 (thetaFirstMode_refined_node_1429).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_477 :
    (634094003099/100000000000000000000000:ℝ) ≤ ∫ x in (477/512:ℝ)..(239/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-205093524455116597851793/1000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (477/512:ℝ) (239/256:ℝ)-(224729903008522098228393/241216691509014397212160:ℝ)*thetaPowerMass 6 (477/512:ℝ) (239/256:ℝ)) ≤
      thetaFirstModeFirst (224729903008522098228393/241216691509014397212160:ℝ)*(thetaPowerMass 7 (477/512:ℝ) (239/256:ℝ)-(224729903008522098228393/241216691509014397212160:ℝ)*thetaPowerMass 6 (477/512:ℝ) (239/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0720.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (477/512:ℝ) (239/256:ℝ)
    (224729903008522098228393/241216691509014397212160:ℝ) (512793/100000000000000:ℝ) (-205093524455116597851793/1000000000000000000000000000000:ℝ) (1452532084929160941/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_477
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1433).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_477 :
    (∫ x in (477/512:ℝ)..(239/256:ℝ), x^6*thetaFirstMode x) ≤ (317070697947/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (477/512:ℝ) (239/256:ℝ)
    (513021/100000000000000:ℝ) (474399/100000000000000:ℝ) (1452532084929160941/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_477 (thetaFirstMode_refined_node_1429).2 (thetaFirstMode_refined_node_1434).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_478 :
    (1484231273791/250000000000000000000000:ℝ) ≤ ∫ x in (239/256:ℝ)..(479/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1767852675261647937/10000000000000000000000000:ℝ)*(thetaPowerMass 7 (239/256:ℝ) (479/512:ℝ)-(479/512:ℝ)*thetaPowerMass 6 (239/256:ℝ) (479/512:ℝ)) ≤
      thetaFirstModeFirst (479/512:ℝ)*(thetaPowerMass 7 (239/256:ℝ) (479/512:ℝ)-(479/512:ℝ)*thetaPowerMass 6 (239/256:ℝ) (479/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0722.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (239/256:ℝ) (479/512:ℝ)
    (479/512:ℝ) (87709/20000000000000:ℝ) (-1767852675261647937/10000000000000000000000000:ℝ) (6768571694957169177/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_478
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1435).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_478 :
    (∫ x in (239/256:ℝ)..(479/512:ℝ), x^6*thetaFirstMode x) ≤ (5937176006779/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (239/256:ℝ) (479/512:ℝ)
    (474399/100000000000000:ℝ) (438549/100000000000000:ℝ) (6768571694957169177/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_478 (thetaFirstMode_refined_node_1434).2 (thetaFirstMode_refined_node_1435).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_479 :
    (5556404178399/1000000000000000000000000:ℝ) ≤ ∫ x in (479/512:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1767134288055586409173623/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (479/512:ℝ) (15/16:ℝ)-(233353802902454023413591/249427470805914151528960:ℝ)*thetaPowerMass 6 (479/512:ℝ) (15/16:ℝ)) ≤
      thetaFirstModeFirst (233353802902454023413591/249427470805914151528960:ℝ)*(thetaPowerMass 7 (479/512:ℝ) (15/16:ℝ)-(233353802902454023413591/249427470805914151528960:ℝ)*thetaPowerMass 6 (479/512:ℝ) (15/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0723.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (479/512:ℝ) (15/16:ℝ)
    (233353802902454023413591/249427470805914151528960:ℝ) (438353/100000000000000:ℝ) (-1767134288055586409173623/10000000000000000000000000000000:ℝ) (3153062464355029157/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_479
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1439).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_479 :
    (∫ x in (479/512:ℝ)..(15/16:ℝ), x^6*thetaFirstMode x) ≤ (5556830449953/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (479/512:ℝ) (15/16:ℝ)
    (438549/100000000000000:ℝ) (405281/100000000000000:ℝ) (3153062464355029157/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_479 (thetaFirstMode_refined_node_1435).2 (thetaFirstMode_refined_node_1440).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

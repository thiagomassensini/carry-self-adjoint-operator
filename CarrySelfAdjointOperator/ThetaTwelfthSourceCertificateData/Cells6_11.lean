import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature11
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative16
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative17
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative18

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_6_352 :
    (2300612410146857/1000000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(353/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-412541448973948607661/1562500000000000000000000:ℝ)*(thetaPowerMass 7 (11/16:ℝ) (353/512:ℝ)-(353/512:ℝ)*thetaPowerMass 6 (11/16:ℝ) (353/512:ℝ)) ≤
      thetaFirstModeFirst (353/512:ℝ)*(thetaPowerMass 7 (11/16:ℝ) (353/512:ℝ)-(353/512:ℝ)*thetaPowerMass 6 (11/16:ℝ) (353/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0533.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (11/16:ℝ) (353/512:ℝ)
    (353/512:ℝ) (134995383/12500000000000:ℝ) (-412541448973948607661/1562500000000000000000000:ℝ) (5915998361410316176869/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_352
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1057).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_352 :
    (∫ x in (11/16:ℝ)..(353/512:ℝ), x^6*thetaFirstMode x) ≤ (143789815878077/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (11/16:ℝ) (353/512:ℝ)
    (566339291/50000000000000:ℝ) (1079967353/100000000000000:ℝ) (5915998361410316176869/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_352 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1057).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_353 :
    (557731531251399/250000000000000000000000:ℝ) ≤ ∫ x in (353/512:ℝ)..(177/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-26394039053179386408577491/100000000000000000000000000000:ℝ)*(thetaPowerMass 7 (353/512:ℝ) (177/256:ℝ)-(14961899000581170932457/21700646917646714268160:ℝ)*thetaPowerMass 6 (353/512:ℝ) (177/256:ℝ)) ≤
      thetaFirstModeFirst (14961899000581170932457/21700646917646714268160:ℝ)*(thetaPowerMass 7 (353/512:ℝ) (177/256:ℝ)-(14961899000581170932457/21700646917646714268160:ℝ)*thetaPowerMass 6 (353/512:ℝ) (177/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0534.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (353/512:ℝ) (177/256:ℝ)
    (14961899000581170932457/21700646917646714268160:ℝ) (1079573587/100000000000000:ℝ) (-26394039053179386408577491/100000000000000000000000000000:ℝ) (2843426264996510417569/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_353
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1061).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_353 :
    (∫ x in (353/512:ℝ)..(177/256:ℝ), x^6*thetaFirstMode x) ≤ (17847722413063/8000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (353/512:ℝ) (177/256:ℝ)
    (1079967353/100000000000000:ℝ) (257378291/25000000000000:ℝ) (2843426264996510417569/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_353 (thetaFirstMode_refined_node_1057).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_354 :
    (27035793271663/12500000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(355/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-6045179042581997119453/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (177/256:ℝ) (355/512:ℝ)-(355/512:ℝ)*thetaPowerMass 6 (177/256:ℝ) (355/512:ℝ)) ≤
      thetaFirstModeFirst (355/512:ℝ)*(thetaPowerMass 7 (177/256:ℝ) (355/512:ℝ)-(355/512:ℝ)*thetaPowerMass 6 (177/256:ℝ) (355/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0536.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (177/256:ℝ) (355/512:ℝ)
    (355/512:ℝ) (490612333/50000000000000:ℝ) (-6045179042581997119453/25000000000000000000000000:ℝ) (1366381270650438608911/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_354
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1063).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_354 :
    (∫ x in (177/256:ℝ)..(355/512:ℝ), x^6*thetaFirstMode x) ≤ (2162887087602273/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (177/256:ℝ) (355/512:ℝ)
    (257378291/25000000000000:ℝ) (490614297/50000000000000:ℝ) (1366381270650438608911/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_354 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1063).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_355 :
    (2096347148674389/1000000000000000000000000:ℝ) ≤ ∫ x in (355/512:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-6043200912031275833817705091/25000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (355/512:ℝ) (89/128:ℝ)-(3148466476744436255595/4540790783819398487552:ℝ)*thetaPowerMass 6 (355/512:ℝ) (89/128:ℝ)) ≤
      thetaFirstModeFirst (3148466476744436255595/4540790783819398487552:ℝ)*(thetaPowerMass 7 (355/512:ℝ) (89/128:ℝ)-(3148466476744436255595/4540790783819398487552:ℝ)*thetaPowerMass 6 (355/512:ℝ) (89/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0537.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (355/512:ℝ) (89/128:ℝ)
    (3148466476744436255595/4540790783819398487552:ℝ) (122608747/12500000000000:ℝ) (-6043200912031275833817705091/25000000000000000000000000000000:ℝ) (1312947952616355036517/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_355
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1067).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_355 :
    (∫ x in (355/512:ℝ)..(89/128:ℝ), x^6*thetaFirstMode x) ≤ (524096197336299/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (355/512:ℝ) (89/128:ℝ)
    (490614297/50000000000000:ℝ) (467514603/50000000000000:ℝ) (1312947952616355036517/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_355 (thetaFirstMode_refined_node_1063).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_356 :
    (1015708834642881/500000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(357/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-5532188542016024121987/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (89/128:ℝ) (357/512:ℝ)-(357/512:ℝ)*thetaPowerMass 6 (89/128:ℝ) (357/512:ℝ)) ≤
      thetaFirstModeFirst (357/512:ℝ)*(thetaPowerMass 7 (89/128:ℝ) (357/512:ℝ)-(357/512:ℝ)*thetaPowerMass 6 (89/128:ℝ) (357/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0539.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (89/128:ℝ) (357/512:ℝ)
    (357/512:ℝ) (890829867/100000000000000:ℝ) (-5532188542016024121987/25000000000000000000000000:ℝ) (2522716680051828661583/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_356
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1069).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_356 :
    (∫ x in (89/128:ℝ)..(357/512:ℝ), x^6*thetaFirstMode x) ≤ (253930037001627/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (89/128:ℝ) (357/512:ℝ)
    (467514603/50000000000000:ℝ) (44541673/5000000000000:ℝ) (2522716680051828661583/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_356 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1069).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_357 :
    (983999451891671/500000000000000000000000:ℝ) ≤ ∫ x in (357/512:ℝ)..(179/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2765186390685839135396358809/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (357/512:ℝ) (179/256:ℝ)-(16558743671981150478993/23747617312889180700160:ℝ)*thetaPowerMass 6 (357/512:ℝ) (179/256:ℝ)) ≤
      thetaFirstModeFirst (16558743671981150478993/23747617312889180700160:ℝ)*(thetaPowerMass 7 (357/512:ℝ) (179/256:ℝ)-(16558743671981150478993/23747617312889180700160:ℝ)*thetaPowerMass 6 (357/512:ℝ) (179/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0540.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (357/512:ℝ) (179/256:ℝ)
    (16558743671981150478993/23747617312889180700160:ℝ) (890507093/100000000000000:ℝ) (-2765186390685839135396358809/12500000000000000000000000000000:ℝ) (4846235194980276675629/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_357
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1073).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_357 :
    (∫ x in (357/512:ℝ)..(179/256:ℝ), x^6*thetaFirstMode x) ≤ (49200875920231/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (357/512:ℝ) (179/256:ℝ)
    (44541673/5000000000000:ℝ) (84856263/10000000000000:ℝ) (4846235194980276675629/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_357 (thetaFirstMode_refined_node_1069).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_358 :
    (1906128353314477/1000000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(359/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2529405044801052267629/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (179/256:ℝ) (359/512:ℝ)-(359/512:ℝ)*thetaPowerMass 6 (179/256:ℝ) (359/512:ℝ)) ≤
      thetaFirstModeFirst (359/512:ℝ)*(thetaPowerMass 7 (179/256:ℝ) (359/512:ℝ)-(359/512:ℝ)*thetaPowerMass 6 (179/256:ℝ) (359/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0542.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (179/256:ℝ) (359/512:ℝ)
    (359/512:ℝ) (404068717/50000000000000:ℝ) (-2529405044801052267629/12500000000000000000000000:ℝ) (930797510392505598467/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_358
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1075).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_358 :
    (∫ x in (179/256:ℝ)..(359/512:ℝ), x^6*thetaFirstMode x) ≤ (1906150008028179/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (179/256:ℝ) (359/512:ℝ)
    (84856263/10000000000000:ℝ) (10101759/1250000000000:ℝ) (930797510392505598467/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_358 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1075).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_359 :
    (369146229811339/200000000000000000000000:ℝ) ≤ ∫ x in (359/512:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-316071539289992232798263901/1562500000000000000000000000000:ℝ)*(thetaPowerMass 7 (359/512:ℝ) (45/64:ℝ)-(17412575849610501454191/24833020561715806159360:ℝ)*thetaPowerMass 6 (359/512:ℝ) (45/64:ℝ)) ≤
      thetaFirstModeFirst (17412575849610501454191/24833020561715806159360:ℝ)*(thetaPowerMass 7 (359/512:ℝ) (45/64:ℝ)-(17412575849610501454191/24833020561715806159360:ℝ)*thetaPowerMass 6 (359/512:ℝ) (45/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0543.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (359/512:ℝ) (45/64:ℝ)
    (17412575849610501454191/24833020561715806159360:ℝ) (201960981/25000000000000:ℝ) (-316071539289992232798263901/1562500000000000000000000000000:ℝ) (4468485357641962583949/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_359
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1079).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_359 :
    (∫ x in (359/512:ℝ)..(45/64:ℝ), x^6*thetaFirstMode x) ≤ (1845765802323179/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (359/512:ℝ) (45/64:ℝ)
    (10101759/1250000000000:ℝ) (769494387/100000000000000:ℝ) (4468485357641962583949/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_359 (thetaFirstMode_refined_node_1075).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_360 :
    (223355241828987/125000000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(361/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-9244655774106136325599/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (45/64:ℝ) (361/512:ℝ)-(361/512:ℝ)*thetaPowerMass 6 (45/64:ℝ) (361/512:ℝ)) ≤
      thetaFirstModeFirst (361/512:ℝ)*(thetaPowerMass 7 (45/64:ℝ) (361/512:ℝ)-(361/512:ℝ)*thetaPowerMass 6 (45/64:ℝ) (361/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0545.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (45/64:ℝ) (361/512:ℝ)
    (361/512:ℝ) (732549859/100000000000000:ℝ) (-9244655774106136325599/50000000000000000000000000:ℝ) (4289528190266634707247/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_360
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1081).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_360 :
    (∫ x in (45/64:ℝ)..(361/512:ℝ), x^6*thetaFirstMode x) ≤ (1786862638103099/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (45/64:ℝ) (361/512:ℝ)
    (769494387/100000000000000:ℝ) (732552861/100000000000000:ℝ) (4289528190266634707247/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_360 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1081).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_361 :
    (432346796024059/250000000000000000000000:ℝ) ≤ ∫ x in (361/512:ℝ)..(181/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-115520035896194767097871389/625000000000000000000000000000:ℝ)*(thetaPowerMass 7 (361/512:ℝ) (181/256:ℝ)-(18305321226441340498209/25961586427017257013760:ℝ)*thetaPowerMass 6 (361/512:ℝ) (181/256:ℝ)) ≤
      thetaFirstModeFirst (18305321226441340498209/25961586427017257013760:ℝ)*(thetaPowerMass 7 (361/512:ℝ) (181/256:ℝ)-(18305321226441340498209/25961586427017257013760:ℝ)*thetaPowerMass 6 (361/512:ℝ) (181/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0546.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (361/512:ℝ) (181/256:ℝ)
    (18305321226441340498209/25961586427017257013760:ℝ) (18307079/2500000000000:ℝ) (-115520035896194767097871389/625000000000000000000000000000:ℝ) (4116920219374762590193/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_361
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1085).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_361 :
    (∫ x in (361/512:ℝ)..(181/256:ℝ), x^6*thetaFirstMode x) ≤ (1729420385574917/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (361/512:ℝ) (181/256:ℝ)
    (732552861/100000000000000:ℝ) (697247869/100000000000000:ℝ) (4116920219374762590193/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_361 (thetaFirstMode_refined_node_1081).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_362 :
    (418349704314051/250000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(363/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-422018453361300320859/2500000000000000000000000:ℝ)*(thetaPowerMass 7 (181/256:ℝ) (363/512:ℝ)-(363/512:ℝ)*thetaPowerMass 6 (181/256:ℝ) (363/512:ℝ)) ≤
      thetaFirstModeFirst (363/512:ℝ)*(thetaPowerMass 7 (181/256:ℝ) (363/512:ℝ)-(363/512:ℝ)*thetaPowerMass 6 (181/256:ℝ) (363/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0548.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (181/256:ℝ) (363/512:ℝ)
    (363/512:ℝ) (663510819/100000000000000:ℝ) (-422018453361300320859/2500000000000000000000000:ℝ) (3950470151824047310243/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_362
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1087).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_362 :
    (∫ x in (181/256:ℝ)..(363/512:ℝ), x^6*thetaFirstMode x) ≤ (1673418592762007/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (181/256:ℝ) (363/512:ℝ)
    (697247869/100000000000000:ℝ) (663513559/100000000000000:ℝ) (3950470151824047310243/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_362 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1087).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_363 :
    (1618804732578261/1000000000000000000000000:ℝ) ≤ ∫ x in (363/512:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1687514623963206965911636817/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (363/512:ℝ) (91/128:ℝ)-(19238522835046489117407/27134777857019009052160:ℝ)*thetaPowerMass 6 (363/512:ℝ) (91/128:ℝ)) ≤
      thetaFirstModeFirst (19238522835046489117407/27134777857019009052160:ℝ)*(thetaPowerMass 7 (363/512:ℝ) (91/128:ℝ)-(19238522835046489117407/27134777857019009052160:ℝ)*thetaPowerMass 6 (363/512:ℝ) (91/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0549.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (363/512:ℝ) (91/128:ℝ)
    (19238522835046489117407/27134777857019009052160:ℝ) (82908583/12500000000000:ℝ) (-1687514623963206965911636817/10000000000000000000000000000000:ℝ) (3789991154824592371277/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_363
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1091).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_363 :
    (∫ x in (363/512:ℝ)..(91/128:ℝ), x^6*thetaFirstMode x) ≤ (404709128532689/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (363/512:ℝ) (91/128:ℝ)
    (663513559/100000000000000:ℝ) (63128643/10000000000000:ℝ) (3789991154824592371277/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_363 (thetaFirstMode_refined_node_1087).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_364 :
    (195704283203507/125000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(365/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-7699947731979790036411/50000000000000000000000000:ℝ)*(thetaPowerMass 7 (91/128:ℝ) (365/512:ℝ)-(365/512:ℝ)*thetaPowerMass 6 (91/128:ℝ) (365/512:ℝ)) ≤
      thetaFirstModeFirst (365/512:ℝ)*(thetaPowerMass 7 (91/128:ℝ) (365/512:ℝ)-(365/512:ℝ)*thetaPowerMass 6 (91/128:ℝ) (365/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0551.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (91/128:ℝ) (365/512:ℝ)
    (365/512:ℝ) (600502759/100000000000000:ℝ) (-7699947731979790036411/50000000000000000000000000:ℝ) (908825205366282139397/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_364
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1093).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_364 :
    (∫ x in (91/128:ℝ)..(365/512:ℝ), x^6*thetaFirstMode x) ≤ (156565313708111/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (91/128:ℝ) (365/512:ℝ)
    (63128643/10000000000000:ℝ) (300252629/50000000000000:ℝ) (908825205366282139397/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_364 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1093).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_365 :
    (302763362221377/200000000000000000000000:ℝ) ≤ ∫ x in (365/512:ℝ)..(183/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1924347272336788455977872753/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (365/512:ℝ) (183/256:ℝ)-(4042755171877232548485/5670819777946998205952:ℝ)*thetaPowerMass 6 (365/512:ℝ) (183/256:ℝ)) ≤
      thetaFirstModeFirst (4042755171877232548485/5670819777946998205952:ℝ)*(thetaPowerMass 7 (365/512:ℝ) (183/256:ℝ)-(4042755171877232548485/5670819777946998205952:ℝ)*thetaPowerMass 6 (365/512:ℝ) (183/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0552.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (365/512:ℝ) (183/256:ℝ)
    (4042755171877232548485/5670819777946998205952:ℝ) (600283057/100000000000000:ℝ) (-1924347272336788455977872753/12500000000000000000000000000000:ℝ) (435777636239628610867/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_365
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1097).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_365 :
    (∫ x in (365/512:ℝ)..(183/256:ℝ), x^6*thetaFirstMode x) ≤ (5913465649277/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (365/512:ℝ) (183/256:ℝ)
    (300252629/50000000000000:ℝ) (142777757/25000000000000:ℝ) (435777636239628610867/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_365 (thetaFirstMode_refined_node_1093).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_366 :
    (731689625796617/500000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(367/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1403773591111714391013/10000000000000000000000000:ℝ)*(thetaPowerMass 7 (183/256:ℝ) (367/512:ℝ)-(367/512:ℝ)*thetaPowerMass 6 (183/256:ℝ) (367/512:ℝ)) ≤
      thetaFirstModeFirst (367/512:ℝ)*(thetaPowerMass 7 (183/256:ℝ) (367/512:ℝ)-(367/512:ℝ)*thetaPowerMass 6 (183/256:ℝ) (367/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0554.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (183/256:ℝ) (367/512:ℝ)
    (367/512:ℝ) (108608917/20000000000000:ℝ) (-1403773591111714391013/10000000000000000000000000:ℝ) (3342578199994124527397/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_366
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1099).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_366 :
    (∫ x in (183/256:ℝ)..(367/512:ℝ), x^6*thetaFirstMode x) ≤ (292679449292451/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (183/256:ℝ) (367/512:ℝ)
    (142777757/25000000000000:ℝ) (543046863/100000000000000:ℝ) (3342578199994124527397/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_366 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1099).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_367 :
    (56570102065709/40000000000000000000000:ℝ) ≤ ∫ x in (367/512:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1403305657409059003242985869/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (367/512:ℝ) (23/32:ℝ)-(21232729095465386243943/29621095571104304028160:ℝ)*thetaPowerMass 6 (367/512:ℝ) (23/32:ℝ)) ≤
      thetaFirstModeFirst (21232729095465386243943/29621095571104304028160:ℝ)*(thetaPowerMass 7 (367/512:ℝ) (23/32:ℝ)-(21232729095465386243943/29621095571104304028160:ℝ)*thetaPowerMass 6 (367/512:ℝ) (23/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0555.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (367/512:ℝ) (23/32:ℝ)
    (21232729095465386243943/29621095571104304028160:ℝ) (16963919/3125000000000:ℝ) (-1403305657409059003242985869/10000000000000000000000000000000:ℝ) (640840523008283373147/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_367
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1103).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_367 :
    (∫ x in (367/512:ℝ)..(23/32:ℝ), x^6*thetaFirstMode x) ≤ (707140795908589/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (367/512:ℝ) (23/32:ℝ)
    (543046863/100000000000000:ℝ) (129064491/25000000000000:ℝ) (640840523008283373147/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_367 (thetaFirstMode_refined_node_1099).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_368 :
    (68323063274067/50000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(369/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-3196440415720571437187/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (23/32:ℝ) (369/512:ℝ)-(369/512:ℝ)*thetaPowerMass 6 (23/32:ℝ) (369/512:ℝ)) ≤
      thetaFirstModeFirst (369/512:ℝ)*(thetaPowerMass 7 (23/32:ℝ) (369/512:ℝ)-(369/512:ℝ)*thetaPowerMass 6 (23/32:ℝ) (369/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0557.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (23/32:ℝ) (369/512:ℝ)
    (369/512:ℝ) (490689463/100000000000000:ℝ) (-3196440415720571437187/25000000000000000000000000:ℝ) (614185791481402863651/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_368
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1105).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_368 :
    (∫ x in (23/32:ℝ)..(369/512:ℝ), x^6*thetaFirstMode x) ≤ (1366478408093667/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (23/32:ℝ) (369/512:ℝ)
    (129064491/25000000000000:ℝ) (245345769/50000000000000:ℝ) (614185791481402863651/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_368 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1105).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_369 :
    (659968996691247/500000000000000000000000:ℝ) ≤ ∫ x in (369/512:ℝ)..(185/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1278148615429148365234817053/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (369/512:ℝ) (185/256:ℝ)-(22297086444538131163641/30937356888429438876160:ℝ)*thetaPowerMass 6 (369/512:ℝ) (185/256:ℝ)) ≤
      thetaFirstModeFirst (22297086444538131163641/30937356888429438876160:ℝ)*(thetaPowerMass 7 (369/512:ℝ) (185/256:ℝ)-(22297086444538131163641/30937356888429438876160:ℝ)*thetaPowerMass 6 (369/512:ℝ) (185/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0558.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (369/512:ℝ) (185/256:ℝ)
    (22297086444538131163641/30937356888429438876160:ℝ) (490509033/100000000000000:ℝ) (-1278148615429148365234817053/10000000000000000000000000000000:ℝ) (735648995948273803559/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_369
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1109).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_369 :
    (∫ x in (369/512:ℝ)..(185/256:ℝ), x^6*thetaFirstMode x) ≤ (659982857403583/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (369/512:ℝ) (185/256:ℝ)
    (245345769/50000000000000:ℝ) (466296741/100000000000000:ℝ) (735648995948273803559/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_369 (thetaFirstMode_refined_node_1105).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_370 :
    (1274705096754001/1000000000000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(371/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1454499787813466918559/12500000000000000000000000:ℝ)*(thetaPowerMass 7 (185/256:ℝ) (371/512:ℝ)-(371/512:ℝ)*thetaPowerMass 6 (185/256:ℝ) (371/512:ℝ)) ≤
      thetaFirstModeFirst (371/512:ℝ)*(thetaPowerMass 7 (185/256:ℝ) (371/512:ℝ)-(371/512:ℝ)*thetaPowerMass 6 (185/256:ℝ) (371/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0560.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (185/256:ℝ) (371/512:ℝ)
    (371/512:ℝ) (110755681/25000000000000:ℝ) (-1454499787813466918559/12500000000000000000000000:ℝ) (140952322835148533423/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_370
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1111).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_370 :
    (∫ x in (185/256:ℝ)..(371/512:ℝ), x^6*thetaFirstMode x) ≤ (637360705116781/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (185/256:ℝ) (371/512:ℝ)
    (466296741/100000000000000:ℝ) (110756153/25000000000000:ℝ) (140952322835148533423/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_370 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1111).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_371 :
    (615348427368937/500000000000000000000000:ℝ) ≤ ∫ x in (371/512:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1454011857400306647204846291/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (371/512:ℝ) (93/128:ℝ)-(23408608439399087217159/32304515719285064680960:ℝ)*thetaPowerMass 6 (371/512:ℝ) (93/128:ℝ)) ≤
      thetaFirstModeFirst (23408608439399087217159/32304515719285064680960:ℝ)*(thetaPowerMass 7 (371/512:ℝ) (93/128:ℝ)-(23408608439399087217159/32304515719285064680960:ℝ)*thetaPowerMass 6 (371/512:ℝ) (93/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0561.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (371/512:ℝ) (93/128:ℝ)
    (23408608439399087217159/32304515719285064680960:ℝ) (110714851/25000000000000:ℝ) (-1454011857400306647204846291/12500000000000000000000000000000:ℝ) (2700127143493966204823/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_371
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1115).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_371 :
    (∫ x in (371/512:ℝ)..(93/128:ℝ), x^6*thetaFirstMode x) ≤ (1230723291732869/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (371/512:ℝ) (93/128:ℝ)
    (110756153/25000000000000:ℝ) (26301751/6250000000000:ℝ) (2700127143493966204823/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_371 (thetaFirstMode_refined_node_1111).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_372 :
    (593966782768341/500000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(373/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2645242262110336608681/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (93/128:ℝ) (373/512:ℝ)-(373/512:ℝ)*thetaPowerMass 6 (93/128:ℝ) (373/512:ℝ)) ≤
      thetaFirstModeFirst (373/512:ℝ)*(thetaPowerMass 7 (93/128:ℝ) (373/512:ℝ)-(373/512:ℝ)*thetaPowerMass 6 (93/128:ℝ) (373/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0563.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (93/128:ℝ) (373/512:ℝ)
    (373/512:ℝ) (199829933/50000000000000:ℝ) (-2645242262110336608681/25000000000000000000000000:ℝ) (517137743580598619471/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_372
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1117).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_372 :
    (∫ x in (93/128:ℝ)..(373/512:ℝ), x^6*thetaFirstMode x) ≤ (593974539025367/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (93/128:ℝ) (373/512:ℝ)
    (26301751/6250000000000:ℝ) (399661583/100000000000000:ℝ) (517137743580598619471/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_372 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1117).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_373 :
    (573175622858827/500000000000000000000000:ℝ) ≤ ∫ x in (373/512:ℝ)..(187/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-264435203008256743296270249/2500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (373/512:ℝ) (187/256:ℝ)-(24569113804309940929857/33724249796067390492160:ℝ)*thetaPowerMass 6 (373/512:ℝ) (187/256:ℝ)) ≤
      thetaFirstModeFirst (24569113804309940929857/33724249796067390492160:ℝ)*(thetaPowerMass 7 (373/512:ℝ) (187/256:ℝ)-(24569113804309940929857/33724249796067390492160:ℝ)*thetaPowerMass 6 (373/512:ℝ) (187/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0564.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (373/512:ℝ) (187/256:ℝ)
    (24569113804309940929857/33724249796067390492160:ℝ) (399512151/100000000000000:ℝ) (-264435203008256743296270249/2500000000000000000000000000000:ℝ) (24755857020076652059/10000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_373
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1121).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_373 :
    (∫ x in (373/512:ℝ)..(187/256:ℝ), x^6*thetaFirstMode x) ≤ (573188215552167/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (373/512:ℝ) (187/256:ℝ)
    (399661583/100000000000000:ℝ) (189740827/50000000000000:ℝ) (24755857020076652059/10000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_373 (thetaFirstMode_refined_node_1117).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_374 :
    (552984121794377/500000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(375/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-300427188343343444591/3125000000000000000000000:ℝ)*(thetaPowerMass 7 (187/256:ℝ) (375/512:ℝ)-(375/512:ℝ)*thetaPowerMass 6 (187/256:ℝ) (375/512:ℝ)) ≤
      thetaFirstModeFirst (375/512:ℝ)*(thetaPowerMass 7 (187/256:ℝ) (375/512:ℝ)-(375/512:ℝ)*thetaPowerMass 6 (187/256:ℝ) (375/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0566.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (187/256:ℝ) (375/512:ℝ)
    (375/512:ℝ) (45030583/12500000000000:ℝ) (-300427188343343444591/3125000000000000000000000:ℝ) (592419104592830041533/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_374
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1123).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_374 :
    (∫ x in (187/256:ℝ)..(375/512:ℝ), x^6*thetaFirstMode x) ≤ (552991488618841/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (187/256:ℝ) (375/512:ℝ)
    (189740827/50000000000000:ℝ) (360246223/100000000000000:ℝ) (592419104592830041533/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_374 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1123).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_375 :
    (213344471183941/200000000000000000000000:ℝ) ≤ ∫ x in (375/512:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x := by
  have hd : (-4805212075176561956723846719/50000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (375/512:ℝ) (47/64:ℝ)-(5156096209822605445875/7039656537271006218752:ℝ)*thetaPowerMass 6 (375/512:ℝ) (47/64:ℝ)) ≤
      thetaFirstModeFirst (5156096209822605445875/7039656537271006218752:ℝ)*(thetaPowerMass 7 (375/512:ℝ) (47/64:ℝ)-(5156096209822605445875/7039656537271006218752:ℝ)*thetaPowerMass 6 (375/512:ℝ) (47/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0567.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (375/512:ℝ) (47/64:ℝ)
    (5156096209822605445875/7039656537271006218752:ℝ) (5626737/1562500000000:ℝ) (-4805212075176561956723846719/50000000000000000000000000000000:ℝ) (2267822886854552488229/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_375
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1127).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_375 :
    (∫ x in (375/512:ℝ)..(47/64:ℝ), x^6*thetaFirstMode x) ≤ (53337316405727/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (375/512:ℝ) (47/64:ℝ)
    (360246223/100000000000000:ℝ) (170957443/50000000000000:ℝ) (2267822886854552488229/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_375 (thetaFirstMode_refined_node_1123).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_376 :
    (32144690936573/31250000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(377/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-2181886522884488384691/25000000000000000000000000:ℝ)*(thetaPowerMass 7 (47/64:ℝ) (377/512:ℝ)-(377/512:ℝ)*thetaPowerMass 6 (47/64:ℝ) (377/512:ℝ)) ≤
      thetaFirstModeFirst (377/512:ℝ)*(thetaPowerMass 7 (47/64:ℝ) (377/512:ℝ)-(377/512:ℝ)*thetaPowerMass 6 (47/64:ℝ) (377/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0569.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (47/64:ℝ) (377/512:ℝ)
    (377/512:ℝ) (162223683/50000000000000:ℝ) (-2181886522884488384691/25000000000000000000000000:ℝ) (2169890816883034985239/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_376
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1129).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_376 :
    (∫ x in (47/64:ℝ)..(377/512:ℝ), x^6*thetaFirstMode x) ≤ (205728819008811/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (47/64:ℝ) (377/512:ℝ)
    (170957443/50000000000000:ℝ) (162224391/50000000000000:ℝ) (2169890816883034985239/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_376 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1129).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_377 :
    (7933048925691/8000000000000000000000:ℝ) ≤ ∫ x in (377/512:ℝ)..(189/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-545286864636167868801445357/6250000000000000000000000000000:ℝ)*(thetaPowerMass 7 (377/512:ℝ) (189/256:ℝ)-(27044650098091245441393/36728384789253236892160:ℝ)*thetaPowerMass 6 (377/512:ℝ) (189/256:ℝ)) ≤
      thetaFirstModeFirst (27044650098091245441393/36728384789253236892160:ℝ)*(thetaPowerMass 7 (377/512:ℝ) (189/256:ℝ)-(27044650098091245441393/36728384789253236892160:ℝ)*thetaPowerMass 6 (377/512:ℝ) (189/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0570.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (377/512:ℝ) (189/256:ℝ)
    (27044650098091245441393/36728384789253236892160:ℝ) (162163409/50000000000000:ℝ) (-545286864636167868801445357/6250000000000000000000000000000:ℝ) (259468686495719689509/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_377
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1133).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_377 :
    (∫ x in (377/512:ℝ)..(189/256:ℝ), x^6*thetaFirstMode x) ≤ (991653910440911/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (377/512:ℝ) (189/256:ℝ)
    (162224391/50000000000000:ℝ) (6156211/2000000000000:ℝ) (259468686495719689509/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_377 (thetaFirstMode_refined_node_1129).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_378 :
    (47787009662247/50000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(379/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-395823383523071450089/5000000000000000000000000:ℝ)*(thetaPowerMass 7 (189/256:ℝ) (379/512:ℝ)-(379/512:ℝ)*thetaPowerMass 6 (189/256:ℝ) (379/512:ℝ)) ≤
      thetaFirstModeFirst (379/512:ℝ)*(thetaPowerMass 7 (189/256:ℝ) (379/512:ℝ)-(379/512:ℝ)*thetaPowerMass 6 (189/256:ℝ) (379/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0572.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (189/256:ℝ) (379/512:ℝ)
    (379/512:ℝ) (29196299/10000000000000:ℝ) (-395823383523071450089/5000000000000000000000000:ℝ) (397054344780609058479/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_378
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1135).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_378 :
    (∫ x in (189/256:ℝ)..(379/512:ℝ), x^6*thetaFirstMode x) ≤ (238938362695127/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (189/256:ℝ) (379/512:ℝ)
    (6156211/2000000000000:ℝ) (145982137/50000000000000:ℝ) (397054344780609058479/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_378 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1135).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_379 :
    (23022469841751/25000000000000000000000:ℝ) ≤ ∫ x in (379/512:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x := by
  have hd : (-791377732703526067616334143/10000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (379/512:ℝ) (95/128:ℝ)-(28363623954139189416591/38316374347894276840960:ℝ)*thetaPowerMass 6 (379/512:ℝ) (95/128:ℝ)) ≤
      thetaFirstModeFirst (28363623954139189416591/38316374347894276840960:ℝ)*(thetaPowerMass 7 (379/512:ℝ) (95/128:ℝ)-(28363623954139189416591/38316374347894276840960:ℝ)*thetaPowerMass 6 (379/512:ℝ) (95/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0573.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (379/512:ℝ) (95/128:ℝ)
    (28363623954139189416591/38316374347894276840960:ℝ) (145927111/50000000000000:ℝ) (-791377732703526067616334143/10000000000000000000000000000000:ℝ) (379666759753091419853/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_379
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1139).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_379 :
    (∫ x in (379/512:ℝ)..(95/128:ℝ), x^6*thetaFirstMode x) ≤ (57557527834847/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (379/512:ℝ) (95/128:ℝ)
    (145982137/50000000000000:ℝ) (138437717/50000000000000:ℝ) (379666759753091419853/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_379 (thetaFirstMode_refined_node_1135).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_380 :
    (887120141948981/1000000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(381/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-35873540716517305463/500000000000000000000000:ℝ)*(thetaPowerMass 7 (95/128:ℝ) (381/512:ℝ)-(381/512:ℝ)*thetaPowerMass 6 (95/128:ℝ) (381/512:ℝ)) ≤
      thetaFirstModeFirst (381/512:ℝ)*(thetaPowerMass 7 (95/128:ℝ) (381/512:ℝ)-(381/512:ℝ)*thetaPowerMass 6 (95/128:ℝ) (381/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0575.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (95/128:ℝ) (381/512:ℝ)
    (381/512:ℝ) (2625097/1000000000000:ℝ) (-35873540716517305463/500000000000000000000000:ℝ) (1814815400513528103253/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_380
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1141).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_380 :
    (∫ x in (95/128:ℝ)..(381/512:ℝ), x^6*thetaFirstMode x) ≤ (887132700569969/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (95/128:ℝ) (381/512:ℝ)
    (138437717/50000000000000:ℝ) (16406929/6250000000000:ℝ) (1814815400513528103253/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_380 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1141).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_381 :
    (106793445372099/125000000000000000000000:ℝ) ≤ ∫ x in (381/512:ℝ)..(191/256:ℝ), x^6*thetaFirstMode x := by
  have hd : (-896532731548993082115411401/12500000000000000000000000000000:ℝ)*(thetaPowerMass 7 (381/512:ℝ) (191/256:ℝ)-(29739470398816532457609/39964118478267692316160:ℝ)*thetaPowerMass 6 (381/512:ℝ) (191/256:ℝ)) ≤
      thetaFirstModeFirst (29739470398816532457609/39964118478267692316160:ℝ)*(thetaPowerMass 7 (381/512:ℝ) (191/256:ℝ)-(29739470398816532457609/39964118478267692316160:ℝ)*thetaPowerMass 6 (381/512:ℝ) (191/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0576.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (381/512:ℝ) (191/256:ℝ)
    (29739470398816532457609/39964118478267692316160:ℝ) (262411641/100000000000000:ℝ) (-896532731548993082115411401/12500000000000000000000000000000:ℝ) (1734599552978536839827/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_381
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1145).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_381 :
    (∫ x in (381/512:ℝ)..(191/256:ℝ), x^6*thetaFirstMode x) ≤ (170873622296777/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (381/512:ℝ) (191/256:ℝ)
    (16406929/6250000000000:ℝ) (124419349/50000000000000:ℝ) (1734599552978536839827/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_381 (thetaFirstMode_refined_node_1141).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_382 :
    (822592792598447/1000000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(383/512:ℝ), x^6*thetaFirstMode x := by
  have hd : (-40605764623404394999/625000000000000000000000:ℝ)*(thetaPowerMass 7 (191/256:ℝ) (383/512:ℝ)-(383/512:ℝ)*thetaPowerMass 6 (191/256:ℝ) (383/512:ℝ)) ≤
      thetaFirstModeFirst (383/512:ℝ)*(thetaPowerMass 7 (191/256:ℝ) (383/512:ℝ)-(383/512:ℝ)*thetaPowerMass 6 (191/256:ℝ) (383/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0578.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (191/256:ℝ) (383/512:ℝ)
    (383/512:ℝ) (2947841/1250000000000:ℝ) (-40605764623404394999/625000000000000000000000:ℝ) (207196567415648073727/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_382
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1147).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_382 :
    (∫ x in (191/256:ℝ)..(383/512:ℝ), x^6*thetaFirstMode x) ≤ (822604678275079/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (191/256:ℝ) (383/512:ℝ)
    (124419349/50000000000000:ℝ) (117914167/50000000000000:ℝ) (207196567415648073727/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_382 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1147).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_6_383 :
    (395900522809711/500000000000000000000000:ℝ) ≤ ∫ x in (383/512:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x := by
  have hd : (-1623674954201119793003664367/25000000000000000000000000000000:ℝ)*(thetaPowerMass 7 (383/512:ℝ) (3/4:ℝ)-(31174323728860831314807/41673534214555068828160:ℝ)*thetaPowerMass 6 (383/512:ℝ) (3/4:ℝ)) ≤
      thetaFirstModeFirst (31174323728860831314807/41673534214555068828160:ℝ)*(thetaPowerMass 7 (383/512:ℝ) (3/4:ℝ)-(31174323728860831314807/41673534214555068828160:ℝ)*thetaPowerMass 6 (383/512:ℝ) (3/4:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0579.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 6 (383/512:ℝ) (3/4:ℝ)
    (31174323728860831314807/41673534214555068828160:ℝ) (235738949/100000000000000:ℝ) (-1623674954201119793003664367/25000000000000000000000000000000:ℝ) (158362387583252580279/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_383
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1151).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_6_383 :
    (∫ x in (383/512:ℝ)..(3/4:ℝ), x^6*thetaFirstMode x) ≤ (395910263130003/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (383/512:ℝ) (3/4:ℝ)
    (117914167/50000000000000:ℝ) (44690077/20000000000000:ℝ) (158362387583252580279/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_383 (thetaFirstMode_refined_node_1147).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

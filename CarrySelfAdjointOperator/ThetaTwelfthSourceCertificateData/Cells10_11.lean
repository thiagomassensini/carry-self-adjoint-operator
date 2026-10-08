import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature11
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative16
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative17
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative18

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_10_352 :
    (516879457034701/1000000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(353/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-412541448973948607661/1562500000000000000000000:ℝ)*(thetaPowerMass 11 (11/16:ℝ) (353/512:ℝ)-(353/512:ℝ)*thetaPowerMass 10 (11/16:ℝ) (353/512:ℝ)) ≤
      thetaFirstModeFirst (353/512:ℝ)*(thetaPowerMass 11 (11/16:ℝ) (353/512:ℝ)-(353/512:ℝ)*thetaPowerMass 10 (11/16:ℝ) (353/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0533.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (11/16:ℝ) (353/512:ℝ)
    (353/512:ℝ) (134995383/12500000000000:ℝ) (-412541448973948607661/1562500000000000000000000:ℝ) (5915998361410316176869/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_352
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1057).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_352 :
    (∫ x in (11/16:ℝ)..(353/512:ℝ), x^10*thetaFirstMode x) ≤ (516884987339181/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/16:ℝ) (353/512:ℝ)
    (566339291/50000000000000:ℝ) (1079967353/100000000000000:ℝ) (5915998361410316176869/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_352 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1057).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_353 :
    (63366849382879/125000000000000000000000:ℝ) ≤ ∫ x in (353/512:ℝ)..(177/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-26394039053179386408577491/100000000000000000000000000000:ℝ)*(thetaPowerMass 11 (353/512:ℝ) (177/256:ℝ)-(14961899000581170932457/21700646917646714268160:ℝ)*thetaPowerMass 10 (353/512:ℝ) (177/256:ℝ)) ≤
      thetaFirstModeFirst (14961899000581170932457/21700646917646714268160:ℝ)*(thetaPowerMass 11 (353/512:ℝ) (177/256:ℝ)-(14961899000581170932457/21700646917646714268160:ℝ)*thetaPowerMass 10 (353/512:ℝ) (177/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0534.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (353/512:ℝ) (177/256:ℝ)
    (14961899000581170932457/21700646917646714268160:ℝ) (1079573587/100000000000000:ℝ) (-26394039053179386408577491/100000000000000000000000000000:ℝ) (2843426264996510417569/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_353
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1061).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_353 :
    (∫ x in (353/512:ℝ)..(177/256:ℝ), x^10*thetaFirstMode x) ≤ (10138874209171/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (353/512:ℝ) (177/256:ℝ)
    (1079967353/100000000000000:ℝ) (257378291/25000000000000:ℝ) (2843426264996510417569/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_353 (thetaFirstMode_refined_node_1057).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_354 :
    (497053626581493/1000000000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(355/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-6045179042581997119453/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (177/256:ℝ) (355/512:ℝ)-(355/512:ℝ)*thetaPowerMass 10 (177/256:ℝ) (355/512:ℝ)) ≤
      thetaFirstModeFirst (355/512:ℝ)*(thetaPowerMass 11 (177/256:ℝ) (355/512:ℝ)-(355/512:ℝ)*thetaPowerMass 10 (177/256:ℝ) (355/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0536.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (177/256:ℝ) (355/512:ℝ)
    (355/512:ℝ) (490612333/50000000000000:ℝ) (-6045179042581997119453/25000000000000000000000000:ℝ) (1366381270650438608911/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_354
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1063).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_354 :
    (∫ x in (177/256:ℝ)..(355/512:ℝ), x^10*thetaFirstMode x) ≤ (497059049776619/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (177/256:ℝ) (355/512:ℝ)
    (257378291/25000000000000:ℝ) (490614297/50000000000000:ℝ) (1366381270650438608911/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_354 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1063).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_355 :
    (487226294950389/1000000000000000000000000:ℝ) ≤ ∫ x in (355/512:ℝ)..(89/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-6043200912031275833817705091/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (355/512:ℝ) (89/128:ℝ)-(3148466476744436255595/4540790783819398487552:ℝ)*thetaPowerMass 10 (355/512:ℝ) (89/128:ℝ)) ≤
      thetaFirstModeFirst (3148466476744436255595/4540790783819398487552:ℝ)*(thetaPowerMass 11 (355/512:ℝ) (89/128:ℝ)-(3148466476744436255595/4540790783819398487552:ℝ)*thetaPowerMass 10 (355/512:ℝ) (89/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0537.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (355/512:ℝ) (89/128:ℝ)
    (3148466476744436255595/4540790783819398487552:ℝ) (122608747/12500000000000:ℝ) (-6043200912031275833817705091/25000000000000000000000000000000:ℝ) (1312947952616355036517/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_355
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1067).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_355 :
    (∫ x in (355/512:ℝ)..(89/128:ℝ), x^10*thetaFirstMode x) ≤ (97447011258811/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (355/512:ℝ) (89/128:ℝ)
    (490614297/50000000000000:ℝ) (467514603/50000000000000:ℝ) (1312947952616355036517/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_355 (thetaFirstMode_refined_node_1063).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_356 :
    (95494069268431/200000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(357/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-5532188542016024121987/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (89/128:ℝ) (357/512:ℝ)-(357/512:ℝ)*thetaPowerMass 10 (89/128:ℝ) (357/512:ℝ)) ≤
      thetaFirstModeFirst (357/512:ℝ)*(thetaPowerMass 11 (89/128:ℝ) (357/512:ℝ)-(357/512:ℝ)*thetaPowerMass 10 (89/128:ℝ) (357/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0539.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (89/128:ℝ) (357/512:ℝ)
    (357/512:ℝ) (890829867/100000000000000:ℝ) (-5532188542016024121987/25000000000000000000000000:ℝ) (2522716680051828661583/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_356
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1069).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_356 :
    (∫ x in (89/128:ℝ)..(357/512:ℝ), x^10*thetaFirstMode x) ≤ (477475658386483/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (89/128:ℝ) (357/512:ℝ)
    (467514603/50000000000000:ℝ) (44541673/5000000000000:ℝ) (2522716680051828661583/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_356 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1069).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_357 :
    (4677760587451/10000000000000000000000:ℝ) ≤ ∫ x in (357/512:ℝ)..(179/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2765186390685839135396358809/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (357/512:ℝ) (179/256:ℝ)-(16558743671981150478993/23747617312889180700160:ℝ)*thetaPowerMass 10 (357/512:ℝ) (179/256:ℝ)) ≤
      thetaFirstModeFirst (16558743671981150478993/23747617312889180700160:ℝ)*(thetaPowerMass 11 (357/512:ℝ) (179/256:ℝ)-(16558743671981150478993/23747617312889180700160:ℝ)*thetaPowerMass 10 (357/512:ℝ) (179/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0540.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (357/512:ℝ) (179/256:ℝ)
    (16558743671981150478993/23747617312889180700160:ℝ) (890507093/100000000000000:ℝ) (-2765186390685839135396358809/12500000000000000000000000000000:ℝ) (4846235194980276675629/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_357
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1073).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_357 :
    (∫ x in (357/512:ℝ)..(179/256:ℝ), x^10*thetaFirstMode x) ≤ (23389233000653/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (357/512:ℝ) (179/256:ℝ)
    (44541673/5000000000000:ℝ) (84856263/10000000000000:ℝ) (4846235194980276675629/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_357 (thetaFirstMode_refined_node_1069).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_358 :
    (229080269994721/500000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(359/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2529405044801052267629/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (179/256:ℝ) (359/512:ℝ)-(359/512:ℝ)*thetaPowerMass 10 (179/256:ℝ) (359/512:ℝ)) ≤
      thetaFirstModeFirst (359/512:ℝ)*(thetaPowerMass 11 (179/256:ℝ) (359/512:ℝ)-(359/512:ℝ)*thetaPowerMass 10 (179/256:ℝ) (359/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0542.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (179/256:ℝ) (359/512:ℝ)
    (359/512:ℝ) (404068717/50000000000000:ℝ) (-2529405044801052267629/12500000000000000000000000:ℝ) (930797510392505598467/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_358
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1075).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_358 :
    (∫ x in (179/256:ℝ)..(359/512:ℝ), x^10*thetaFirstMode x) ≤ (458165738876453/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (179/256:ℝ) (359/512:ℝ)
    (84856263/10000000000000:ℝ) (10101759/1250000000000:ℝ) (930797510392505598467/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_358 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1075).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_359 :
    (448614010225939/1000000000000000000000000:ℝ) ≤ ∫ x in (359/512:ℝ)..(45/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-316071539289992232798263901/1562500000000000000000000000000:ℝ)*(thetaPowerMass 11 (359/512:ℝ) (45/64:ℝ)-(17412575849610501454191/24833020561715806159360:ℝ)*thetaPowerMass 10 (359/512:ℝ) (45/64:ℝ)) ≤
      thetaFirstModeFirst (17412575849610501454191/24833020561715806159360:ℝ)*(thetaPowerMass 11 (359/512:ℝ) (45/64:ℝ)-(17412575849610501454191/24833020561715806159360:ℝ)*thetaPowerMass 10 (359/512:ℝ) (45/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0543.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (359/512:ℝ) (45/64:ℝ)
    (17412575849610501454191/24833020561715806159360:ℝ) (201960981/25000000000000:ℝ) (-316071539289992232798263901/1562500000000000000000000000000:ℝ) (4468485357641962583949/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_359
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1079).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_359 :
    (∫ x in (359/512:ℝ)..(45/64:ℝ), x^10*thetaFirstMode x) ≤ (448622445373819/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (359/512:ℝ) (45/64:ℝ)
    (10101759/1250000000000:ℝ) (769494387/100000000000000:ℝ) (4468485357641962583949/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_359 (thetaFirstMode_refined_node_1075).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_360 :
    (87830623902261/200000000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(361/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-9244655774106136325599/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (45/64:ℝ) (361/512:ℝ)-(361/512:ℝ)*thetaPowerMass 10 (45/64:ℝ) (361/512:ℝ)) ≤
      thetaFirstModeFirst (361/512:ℝ)*(thetaPowerMass 11 (45/64:ℝ) (361/512:ℝ)-(361/512:ℝ)*thetaPowerMass 10 (45/64:ℝ) (361/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0545.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (45/64:ℝ) (361/512:ℝ)
    (361/512:ℝ) (732549859/100000000000000:ℝ) (-9244655774106136325599/50000000000000000000000000:ℝ) (4289528190266634707247/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_360
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1081).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_360 :
    (∫ x in (45/64:ℝ)..(361/512:ℝ), x^10*thetaFirstMode x) ≤ (219579100933127/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (45/64:ℝ) (361/512:ℝ)
    (769494387/100000000000000:ℝ) (732552861/100000000000000:ℝ) (4289528190266634707247/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_360 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1081).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_361 :
    (429768038332001/1000000000000000000000000:ℝ) ≤ ∫ x in (361/512:ℝ)..(181/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-115520035896194767097871389/625000000000000000000000000000:ℝ)*(thetaPowerMass 11 (361/512:ℝ) (181/256:ℝ)-(18305321226441340498209/25961586427017257013760:ℝ)*thetaPowerMass 10 (361/512:ℝ) (181/256:ℝ)) ≤
      thetaFirstModeFirst (18305321226441340498209/25961586427017257013760:ℝ)*(thetaPowerMass 11 (361/512:ℝ) (181/256:ℝ)-(18305321226441340498209/25961586427017257013760:ℝ)*thetaPowerMass 10 (361/512:ℝ) (181/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0546.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (361/512:ℝ) (181/256:ℝ)
    (18305321226441340498209/25961586427017257013760:ℝ) (18307079/2500000000000:ℝ) (-115520035896194767097871389/625000000000000000000000000000:ℝ) (4116920219374762590193/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_361
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1085).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_361 :
    (∫ x in (361/512:ℝ)..(181/256:ℝ), x^10*thetaFirstMode x) ≤ (429776301424129/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (361/512:ℝ) (181/256:ℝ)
    (732552861/100000000000000:ℝ) (697247869/100000000000000:ℝ) (4116920219374762590193/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_361 (thetaFirstMode_refined_node_1081).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_362 :
    (420474943648629/1000000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(363/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-422018453361300320859/2500000000000000000000000:ℝ)*(thetaPowerMass 11 (181/256:ℝ) (363/512:ℝ)-(363/512:ℝ)*thetaPowerMass 10 (181/256:ℝ) (363/512:ℝ)) ≤
      thetaFirstModeFirst (363/512:ℝ)*(thetaPowerMass 11 (181/256:ℝ) (363/512:ℝ)-(363/512:ℝ)*thetaPowerMass 10 (181/256:ℝ) (363/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0548.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (181/256:ℝ) (363/512:ℝ)
    (363/512:ℝ) (663510819/100000000000000:ℝ) (-422018453361300320859/2500000000000000000000000:ℝ) (3950470151824047310243/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_362
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1087).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_362 :
    (∫ x in (181/256:ℝ)..(363/512:ℝ), x^10*thetaFirstMode x) ≤ (42047990682661/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (181/256:ℝ) (363/512:ℝ)
    (697247869/100000000000000:ℝ) (663513559/100000000000000:ℝ) (3950470151824047310243/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_362 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1087).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_363 :
    (411263964314517/1000000000000000000000000:ℝ) ≤ ∫ x in (363/512:ℝ)..(91/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1687514623963206965911636817/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (363/512:ℝ) (91/128:ℝ)-(19238522835046489117407/27134777857019009052160:ℝ)*thetaPowerMass 10 (363/512:ℝ) (91/128:ℝ)) ≤
      thetaFirstModeFirst (19238522835046489117407/27134777857019009052160:ℝ)*(thetaPowerMass 11 (363/512:ℝ) (91/128:ℝ)-(19238522835046489117407/27134777857019009052160:ℝ)*thetaPowerMass 10 (363/512:ℝ) (91/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0549.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (363/512:ℝ) (91/128:ℝ)
    (19238522835046489117407/27134777857019009052160:ℝ) (82908583/12500000000000:ℝ) (-1687514623963206965911636817/10000000000000000000000000000000:ℝ) (3789991154824592371277/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_363
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1091).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_363 :
    (∫ x in (363/512:ℝ)..(91/128:ℝ), x^10*thetaFirstMode x) ≤ (411272050499859/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (363/512:ℝ) (91/128:ℝ)
    (663513559/100000000000000:ℝ) (63128643/10000000000000:ℝ) (3789991154824592371277/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_363 (thetaFirstMode_refined_node_1087).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_364 :
    (402150792558373/1000000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(365/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-7699947731979790036411/50000000000000000000000000:ℝ)*(thetaPowerMass 11 (91/128:ℝ) (365/512:ℝ)-(365/512:ℝ)*thetaPowerMass 10 (91/128:ℝ) (365/512:ℝ)) ≤
      thetaFirstModeFirst (365/512:ℝ)*(thetaPowerMass 11 (91/128:ℝ) (365/512:ℝ)-(365/512:ℝ)*thetaPowerMass 10 (91/128:ℝ) (365/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0551.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (91/128:ℝ) (365/512:ℝ)
    (365/512:ℝ) (600502759/100000000000000:ℝ) (-7699947731979790036411/50000000000000000000000000:ℝ) (908825205366282139397/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_364
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1093).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_364 :
    (∫ x in (91/128:ℝ)..(365/512:ℝ), x^10*thetaFirstMode x) ≤ (201077817114167/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (91/128:ℝ) (365/512:ℝ)
    (63128643/10000000000000:ℝ) (300252629/50000000000000:ℝ) (908825205366282139397/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_364 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1093).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_365 :
    (39312552357581/100000000000000000000000:ℝ) ≤ ∫ x in (365/512:ℝ)..(183/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1924347272336788455977872753/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (365/512:ℝ) (183/256:ℝ)-(4042755171877232548485/5670819777946998205952:ℝ)*thetaPowerMass 10 (365/512:ℝ) (183/256:ℝ)) ≤
      thetaFirstModeFirst (4042755171877232548485/5670819777946998205952:ℝ)*(thetaPowerMass 11 (365/512:ℝ) (183/256:ℝ)-(4042755171877232548485/5670819777946998205952:ℝ)*thetaPowerMass 10 (365/512:ℝ) (183/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0552.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (365/512:ℝ) (183/256:ℝ)
    (4042755171877232548485/5670819777946998205952:ℝ) (600283057/100000000000000:ℝ) (-1924347272336788455977872753/12500000000000000000000000000000:ℝ) (435777636239628610867/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_365
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1097).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_365 :
    (∫ x in (365/512:ℝ)..(183/256:ℝ), x^10*thetaFirstMode x) ≤ (393133428597981/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (365/512:ℝ) (183/256:ℝ)
    (300252629/50000000000000:ℝ) (142777757/25000000000000:ℝ) (435777636239628610867/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_365 (thetaFirstMode_refined_node_1093).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_366 :
    (384203353477301/1000000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(367/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1403773591111714391013/10000000000000000000000000:ℝ)*(thetaPowerMass 11 (183/256:ℝ) (367/512:ℝ)-(367/512:ℝ)*thetaPowerMass 10 (183/256:ℝ) (367/512:ℝ)) ≤
      thetaFirstModeFirst (367/512:ℝ)*(thetaPowerMass 11 (183/256:ℝ) (367/512:ℝ)-(367/512:ℝ)*thetaPowerMass 10 (183/256:ℝ) (367/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0554.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (183/256:ℝ) (367/512:ℝ)
    (367/512:ℝ) (108608917/20000000000000:ℝ) (-1403773591111714391013/10000000000000000000000000:ℝ) (3342578199994124527397/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_366
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1099).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_366 :
    (∫ x in (183/256:ℝ)..(367/512:ℝ), x^10*thetaFirstMode x) ≤ (38420807241109/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (183/256:ℝ) (367/512:ℝ)
    (142777757/25000000000000:ℝ) (543046863/100000000000000:ℝ) (3342578199994124527397/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_366 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1099).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_367 :
    (375374354575437/1000000000000000000000000:ℝ) ≤ ∫ x in (367/512:ℝ)..(23/32:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1403305657409059003242985869/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (367/512:ℝ) (23/32:ℝ)-(21232729095465386243943/29621095571104304028160:ℝ)*thetaPowerMass 10 (367/512:ℝ) (23/32:ℝ)) ≤
      thetaFirstModeFirst (21232729095465386243943/29621095571104304028160:ℝ)*(thetaPowerMass 11 (367/512:ℝ) (23/32:ℝ)-(21232729095465386243943/29621095571104304028160:ℝ)*thetaPowerMass 10 (367/512:ℝ) (23/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0555.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (367/512:ℝ) (23/32:ℝ)
    (21232729095465386243943/29621095571104304028160:ℝ) (16963919/3125000000000:ℝ) (-1403305657409059003242985869/10000000000000000000000000000000:ℝ) (640840523008283373147/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_367
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1103).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_367 :
    (∫ x in (367/512:ℝ)..(23/32:ℝ), x^10*thetaFirstMode x) ≤ (75076414773237/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (367/512:ℝ) (23/32:ℝ)
    (543046863/100000000000000:ℝ) (129064491/25000000000000:ℝ) (640840523008283373147/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_367 (thetaFirstMode_refined_node_1099).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_368 :
    (366653216125379/1000000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(369/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-3196440415720571437187/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (23/32:ℝ) (369/512:ℝ)-(369/512:ℝ)*thetaPowerMass 10 (23/32:ℝ) (369/512:ℝ)) ≤
      thetaFirstModeFirst (369/512:ℝ)*(thetaPowerMass 11 (23/32:ℝ) (369/512:ℝ)-(369/512:ℝ)*thetaPowerMass 10 (23/32:ℝ) (369/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0557.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (23/32:ℝ) (369/512:ℝ)
    (369/512:ℝ) (490689463/100000000000000:ℝ) (-3196440415720571437187/25000000000000000000000000:ℝ) (614185791481402863651/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_368
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1105).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_368 :
    (∫ x in (23/32:ℝ)..(369/512:ℝ), x^10*thetaFirstMode x) ≤ (366657810494361/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (23/32:ℝ) (369/512:ℝ)
    (129064491/25000000000000:ℝ) (245345769/50000000000000:ℝ) (614185791481402863651/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_368 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1105).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_369 :
    (89507499676907/250000000000000000000000:ℝ) ≤ ∫ x in (369/512:ℝ)..(185/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1278148615429148365234817053/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (369/512:ℝ) (185/256:ℝ)-(22297086444538131163641/30937356888429438876160:ℝ)*thetaPowerMass 10 (369/512:ℝ) (185/256:ℝ)) ≤
      thetaFirstModeFirst (22297086444538131163641/30937356888429438876160:ℝ)*(thetaPowerMass 11 (369/512:ℝ) (185/256:ℝ)-(22297086444538131163641/30937356888429438876160:ℝ)*thetaPowerMass 10 (369/512:ℝ) (185/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0558.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (369/512:ℝ) (185/256:ℝ)
    (22297086444538131163641/30937356888429438876160:ℝ) (490509033/100000000000000:ℝ) (-1278148615429148365234817053/10000000000000000000000000000000:ℝ) (735648995948273803559/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_369
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1109).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_369 :
    (∫ x in (369/512:ℝ)..(185/256:ℝ), x^10*thetaFirstMode x) ≤ (89509382289691/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (369/512:ℝ) (185/256:ℝ)
    (245345769/50000000000000:ℝ) (466296741/100000000000000:ℝ) (735648995948273803559/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_369 (thetaFirstMode_refined_node_1105).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_370 :
    (174759439672369/500000000000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(371/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1454499787813466918559/12500000000000000000000000:ℝ)*(thetaPowerMass 11 (185/256:ℝ) (371/512:ℝ)-(371/512:ℝ)*thetaPowerMass 10 (185/256:ℝ) (371/512:ℝ)) ≤
      thetaFirstModeFirst (371/512:ℝ)*(thetaPowerMass 11 (185/256:ℝ) (371/512:ℝ)-(371/512:ℝ)*thetaPowerMass 10 (185/256:ℝ) (371/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0560.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (185/256:ℝ) (371/512:ℝ)
    (371/512:ℝ) (110755681/25000000000000:ℝ) (-1454499787813466918559/12500000000000000000000000:ℝ) (140952322835148533423/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_370
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1111).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_370 :
    (∫ x in (185/256:ℝ)..(371/512:ℝ), x^10*thetaFirstMode x) ≤ (174761673594141/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (185/256:ℝ) (371/512:ℝ)
    (466296741/100000000000000:ℝ) (110756153/25000000000000:ℝ) (140952322835148533423/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_370 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1111).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_371 :
    (341109914281387/1000000000000000000000000:ℝ) ≤ ∫ x in (371/512:ℝ)..(93/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1454011857400306647204846291/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (371/512:ℝ) (93/128:ℝ)-(23408608439399087217159/32304515719285064680960:ℝ)*thetaPowerMass 10 (371/512:ℝ) (93/128:ℝ)) ≤
      thetaFirstModeFirst (23408608439399087217159/32304515719285064680960:ℝ)*(thetaPowerMass 11 (371/512:ℝ) (93/128:ℝ)-(23408608439399087217159/32304515719285064680960:ℝ)*thetaPowerMass 10 (371/512:ℝ) (93/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0561.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (371/512:ℝ) (93/128:ℝ)
    (23408608439399087217159/32304515719285064680960:ℝ) (110714851/25000000000000:ℝ) (-1454011857400306647204846291/12500000000000000000000000000000:ℝ) (2700127143493966204823/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_371
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1115).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_371 :
    (∫ x in (371/512:ℝ)..(93/128:ℝ), x^10*thetaFirstMode x) ≤ (341117252555287/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (371/512:ℝ) (93/128:ℝ)
    (110756153/25000000000000:ℝ) (26301751/6250000000000:ℝ) (2700127143493966204823/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_371 (thetaFirstMode_refined_node_1111).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_372 :
    (332816763913437/1000000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(373/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2645242262110336608681/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (93/128:ℝ) (373/512:ℝ)-(373/512:ℝ)*thetaPowerMass 10 (93/128:ℝ) (373/512:ℝ)) ≤
      thetaFirstModeFirst (373/512:ℝ)*(thetaPowerMass 11 (93/128:ℝ) (373/512:ℝ)-(373/512:ℝ)*thetaPowerMass 10 (93/128:ℝ) (373/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0563.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (93/128:ℝ) (373/512:ℝ)
    (373/512:ℝ) (199829933/50000000000000:ℝ) (-2645242262110336608681/25000000000000000000000000:ℝ) (517137743580598619471/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_372
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1117).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_372 :
    (∫ x in (93/128:ℝ)..(373/512:ℝ), x^10*thetaFirstMode x) ≤ (332821104870337/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (93/128:ℝ) (373/512:ℝ)
    (26301751/6250000000000:ℝ) (399661583/100000000000000:ℝ) (517137743580598619471/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_372 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1117).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_373 :
    (40578686744091/125000000000000000000000:ℝ) ≤ ∫ x in (373/512:ℝ)..(187/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-264435203008256743296270249/2500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (373/512:ℝ) (187/256:ℝ)-(24569113804309940929857/33724249796067390492160:ℝ)*thetaPowerMass 10 (373/512:ℝ) (187/256:ℝ)) ≤
      thetaFirstModeFirst (24569113804309940929857/33724249796067390492160:ℝ)*(thetaPowerMass 11 (373/512:ℝ) (187/256:ℝ)-(24569113804309940929857/33724249796067390492160:ℝ)*thetaPowerMass 10 (373/512:ℝ) (187/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0564.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (373/512:ℝ) (187/256:ℝ)
    (24569113804309940929857/33724249796067390492160:ℝ) (399512151/100000000000000:ℝ) (-264435203008256743296270249/2500000000000000000000000000000:ℝ) (24755857020076652059/10000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_373
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1121).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_373 :
    (∫ x in (373/512:ℝ)..(187/256:ℝ), x^10*thetaFirstMode x) ≤ (324636636555329/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (373/512:ℝ) (187/256:ℝ)
    (399661583/100000000000000:ℝ) (189740827/50000000000000:ℝ) (24755857020076652059/10000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_373 (thetaFirstMode_refined_node_1117).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_374 :
    (158280620956677/500000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(375/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-300427188343343444591/3125000000000000000000000:ℝ)*(thetaPowerMass 11 (187/256:ℝ) (375/512:ℝ)-(375/512:ℝ)*thetaPowerMass 10 (187/256:ℝ) (375/512:ℝ)) ≤
      thetaFirstModeFirst (375/512:ℝ)*(thetaPowerMass 11 (187/256:ℝ) (375/512:ℝ)-(375/512:ℝ)*thetaPowerMass 10 (187/256:ℝ) (375/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0566.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (187/256:ℝ) (375/512:ℝ)
    (375/512:ℝ) (45030583/12500000000000:ℝ) (-300427188343343444591/3125000000000000000000000:ℝ) (592419104592830041533/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_374
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1123).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_374 :
    (∫ x in (187/256:ℝ)..(375/512:ℝ), x^10*thetaFirstMode x) ≤ (31656545417511/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (187/256:ℝ) (375/512:ℝ)
    (189740827/50000000000000:ℝ) (360246223/100000000000000:ℝ) (592419104592830041533/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_374 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1123).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_375 :
    (30860209467717/100000000000000000000000:ℝ) ≤ ∫ x in (375/512:ℝ)..(47/64:ℝ), x^10*thetaFirstMode x := by
  have hd : (-4805212075176561956723846719/50000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (375/512:ℝ) (47/64:ℝ)-(5156096209822605445875/7039656537271006218752:ℝ)*thetaPowerMass 10 (375/512:ℝ) (47/64:ℝ)) ≤
      thetaFirstModeFirst (5156096209822605445875/7039656537271006218752:ℝ)*(thetaPowerMass 11 (375/512:ℝ) (47/64:ℝ)-(5156096209822605445875/7039656537271006218752:ℝ)*thetaPowerMass 10 (375/512:ℝ) (47/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0567.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (375/512:ℝ) (47/64:ℝ)
    (5156096209822605445875/7039656537271006218752:ℝ) (5626737/1562500000000:ℝ) (-4805212075176561956723846719/50000000000000000000000000000000:ℝ) (2267822886854552488229/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_375
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1127).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_375 :
    (∫ x in (375/512:ℝ)..(47/64:ℝ), x^10*thetaFirstMode x) ≤ (154304519995577/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (375/512:ℝ) (47/64:ℝ)
    (360246223/100000000000000:ℝ) (170957443/50000000000000:ℝ) (2267822886854552488229/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_375 (thetaFirstMode_refined_node_1123).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_376 :
    (60152933512597/200000000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(377/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-2181886522884488384691/25000000000000000000000000:ℝ)*(thetaPowerMass 11 (47/64:ℝ) (377/512:ℝ)-(377/512:ℝ)*thetaPowerMass 10 (47/64:ℝ) (377/512:ℝ)) ≤
      thetaFirstModeFirst (377/512:ℝ)*(thetaPowerMass 11 (47/64:ℝ) (377/512:ℝ)-(377/512:ℝ)*thetaPowerMass 10 (47/64:ℝ) (377/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0569.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (47/64:ℝ) (377/512:ℝ)
    (377/512:ℝ) (162223683/50000000000000:ℝ) (-2181886522884488384691/25000000000000000000000000:ℝ) (2169890816883034985239/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_376
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1129).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_376 :
    (∫ x in (47/64:ℝ)..(377/512:ℝ), x^10*thetaFirstMode x) ≤ (30076875190621/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (47/64:ℝ) (377/512:ℝ)
    (170957443/50000000000000:ℝ) (162224391/50000000000000:ℝ) (2169890816883034985239/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_376 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1129).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_377 :
    (146519539880533/500000000000000000000000:ℝ) ≤ ∫ x in (377/512:ℝ)..(189/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-545286864636167868801445357/6250000000000000000000000000000:ℝ)*(thetaPowerMass 11 (377/512:ℝ) (189/256:ℝ)-(27044650098091245441393/36728384789253236892160:ℝ)*thetaPowerMass 10 (377/512:ℝ) (189/256:ℝ)) ≤
      thetaFirstModeFirst (27044650098091245441393/36728384789253236892160:ℝ)*(thetaPowerMass 11 (377/512:ℝ) (189/256:ℝ)-(27044650098091245441393/36728384789253236892160:ℝ)*thetaPowerMass 10 (377/512:ℝ) (189/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0570.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (377/512:ℝ) (189/256:ℝ)
    (27044650098091245441393/36728384789253236892160:ℝ) (162163409/50000000000000:ℝ) (-545286864636167868801445357/6250000000000000000000000000000:ℝ) (259468686495719689509/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_377
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1133).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_377 :
    (∫ x in (377/512:ℝ)..(189/256:ℝ), x^10*thetaFirstMode x) ≤ (293045825746149/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (377/512:ℝ) (189/256:ℝ)
    (162224391/50000000000000:ℝ) (6156211/2000000000000:ℝ) (259468686495719689509/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_377 (thetaFirstMode_refined_node_1129).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_378 :
    (285437423526879/1000000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(379/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-395823383523071450089/5000000000000000000000000:ℝ)*(thetaPowerMass 11 (189/256:ℝ) (379/512:ℝ)-(379/512:ℝ)*thetaPowerMass 10 (189/256:ℝ) (379/512:ℝ)) ≤
      thetaFirstModeFirst (379/512:ℝ)*(thetaPowerMass 11 (189/256:ℝ) (379/512:ℝ)-(379/512:ℝ)*thetaPowerMass 10 (189/256:ℝ) (379/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0572.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (189/256:ℝ) (379/512:ℝ)
    (379/512:ℝ) (29196299/10000000000000:ℝ) (-395823383523071450089/5000000000000000000000000:ℝ) (397054344780609058479/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_378
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1135).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_378 :
    (∫ x in (189/256:ℝ)..(379/512:ℝ), x^10*thetaFirstMode x) ≤ (71360344579609/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (189/256:ℝ) (379/512:ℝ)
    (6156211/2000000000000:ℝ) (145982137/50000000000000:ℝ) (397054344780609058479/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_378 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1135).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_379 :
    (8685933188281/31250000000000000000000:ℝ) ≤ ∫ x in (379/512:ℝ)..(95/128:ℝ), x^10*thetaFirstMode x := by
  have hd : (-791377732703526067616334143/10000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (379/512:ℝ) (95/128:ℝ)-(28363623954139189416591/38316374347894276840960:ℝ)*thetaPowerMass 10 (379/512:ℝ) (95/128:ℝ)) ≤
      thetaFirstModeFirst (28363623954139189416591/38316374347894276840960:ℝ)*(thetaPowerMass 11 (379/512:ℝ) (95/128:ℝ)-(28363623954139189416591/38316374347894276840960:ℝ)*thetaPowerMass 10 (379/512:ℝ) (95/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0573.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (379/512:ℝ) (95/128:ℝ)
    (28363623954139189416591/38316374347894276840960:ℝ) (145927111/50000000000000:ℝ) (-791377732703526067616334143/10000000000000000000000000000000:ℝ) (379666759753091419853/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_379
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1139).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_379 :
    (∫ x in (379/512:ℝ)..(95/128:ℝ), x^10*thetaFirstMode x) ≤ (277956406590767/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (379/512:ℝ) (95/128:ℝ)
    (145982137/50000000000000:ℝ) (138437717/50000000000000:ℝ) (379666759753091419853/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_379 (thetaFirstMode_refined_node_1135).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_380 :
    (270587965625991/1000000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(381/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-35873540716517305463/500000000000000000000000:ℝ)*(thetaPowerMass 11 (95/128:ℝ) (381/512:ℝ)-(381/512:ℝ)*thetaPowerMass 10 (95/128:ℝ) (381/512:ℝ)) ≤
      thetaFirstModeFirst (381/512:ℝ)*(thetaPowerMass 11 (95/128:ℝ) (381/512:ℝ)-(381/512:ℝ)*thetaPowerMass 10 (95/128:ℝ) (381/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0575.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (95/128:ℝ) (381/512:ℝ)
    (381/512:ℝ) (2625097/1000000000000:ℝ) (-35873540716517305463/500000000000000000000000:ℝ) (1814815400513528103253/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_380
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1141).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_380 :
    (∫ x in (95/128:ℝ)..(381/512:ℝ), x^10*thetaFirstMode x) ≤ (54118358347611/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (95/128:ℝ) (381/512:ℝ)
    (138437717/50000000000000:ℝ) (16406929/6250000000000:ℝ) (1814815400513528103253/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_380 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1141).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_381 :
    (1645887228891/6250000000000000000000:ℝ) ≤ ∫ x in (381/512:ℝ)..(191/256:ℝ), x^10*thetaFirstMode x := by
  have hd : (-896532731548993082115411401/12500000000000000000000000000000:ℝ)*(thetaPowerMass 11 (381/512:ℝ) (191/256:ℝ)-(29739470398816532457609/39964118478267692316160:ℝ)*thetaPowerMass 10 (381/512:ℝ) (191/256:ℝ)) ≤
      thetaFirstModeFirst (29739470398816532457609/39964118478267692316160:ℝ)*(thetaPowerMass 11 (381/512:ℝ) (191/256:ℝ)-(29739470398816532457609/39964118478267692316160:ℝ)*thetaPowerMass 10 (381/512:ℝ) (191/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0576.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (381/512:ℝ) (191/256:ℝ)
    (29739470398816532457609/39964118478267692316160:ℝ) (262411641/100000000000000:ℝ) (-896532731548993082115411401/12500000000000000000000000000000:ℝ) (1734599552978536839827/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_381
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1145).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_381 :
    (∫ x in (381/512:ℝ)..(191/256:ℝ), x^10*thetaFirstMode x) ≤ (52669659937617/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (381/512:ℝ) (191/256:ℝ)
    (16406929/6250000000000:ℝ) (124419349/50000000000000:ℝ) (1734599552978536839827/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_381 (thetaFirstMode_refined_node_1141).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_382 :
    (64055721396667/250000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(383/512:ℝ), x^10*thetaFirstMode x := by
  have hd : (-40605764623404394999/625000000000000000000000:ℝ)*(thetaPowerMass 11 (191/256:ℝ) (383/512:ℝ)-(383/512:ℝ)*thetaPowerMass 10 (191/256:ℝ) (383/512:ℝ)) ≤
      thetaFirstModeFirst (383/512:ℝ)*(thetaPowerMass 11 (191/256:ℝ) (383/512:ℝ)-(383/512:ℝ)*thetaPowerMass 10 (191/256:ℝ) (383/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0578.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (191/256:ℝ) (383/512:ℝ)
    (383/512:ℝ) (2947841/1250000000000:ℝ) (-40605764623404394999/625000000000000000000000:ℝ) (207196567415648073727/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_382
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1147).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_382 :
    (∫ x in (191/256:ℝ)..(383/512:ℝ), x^10*thetaFirstMode x) ≤ (256226583413141/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (191/256:ℝ) (383/512:ℝ)
    (124419349/50000000000000:ℝ) (117914167/50000000000000:ℝ) (207196567415648073727/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_382 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1147).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_10_383 :
    (249221046118639/1000000000000000000000000:ℝ) ≤ ∫ x in (383/512:ℝ)..(3/4:ℝ), x^10*thetaFirstMode x := by
  have hd : (-1623674954201119793003664367/25000000000000000000000000000000:ℝ)*(thetaPowerMass 11 (383/512:ℝ) (3/4:ℝ)-(31174323728860831314807/41673534214555068828160:ℝ)*thetaPowerMass 10 (383/512:ℝ) (3/4:ℝ)) ≤
      thetaFirstModeFirst (31174323728860831314807/41673534214555068828160:ℝ)*(thetaPowerMass 11 (383/512:ℝ) (3/4:ℝ)-(31174323728860831314807/41673534214555068828160:ℝ)*thetaPowerMass 10 (383/512:ℝ) (3/4:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0579.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 10 (383/512:ℝ) (3/4:ℝ)
    (31174323728860831314807/41673534214555068828160:ℝ) (235738949/100000000000000:ℝ) (-1623674954201119793003664367/25000000000000000000000000000000:ℝ) (158362387583252580279/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_383
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1151).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_10_383 :
    (∫ x in (383/512:ℝ)..(3/4:ℝ), x^10*thetaFirstMode x) ≤ (62306796656847/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (383/512:ℝ) (3/4:ℝ)
    (117914167/50000000000000:ℝ) (44690077/20000000000000:ℝ) (158362387583252580279/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_383 (thetaFirstMode_refined_node_1147).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

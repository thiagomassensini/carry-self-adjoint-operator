import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature11
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative16
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative17
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative18

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_352 :
    (21603816325340873/1000000000000000000000000:ℝ) ≤ ∫ x in (11/16:ℝ)..(353/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6895317552322349053858834523/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (11/16:ℝ) (353/512:ℝ)-(11/16:ℝ)*thetaPowerMass 0 (11/16:ℝ) (353/512:ℝ)) ≤
      thetaFirstModeFirst (11/16:ℝ)*(thetaPowerMass 1 (11/16:ℝ) (353/512:ℝ)-(11/16:ℝ)*thetaPowerMass 0 (11/16:ℝ) (353/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0532.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (11/16:ℝ) (353/512:ℝ)
    (11/16:ℝ) (1132674101/100000000000000:ℝ) (-6895317552322349053858834523/25000000000000000000000000000000:ℝ) (5915998361410316176869/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_352
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1056).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_352 :
    (∫ x in (11/16:ℝ)..(353/512:ℝ), x^0*thetaFirstMode x) ≤ (10802098661883731/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (11/16:ℝ) (353/512:ℝ)
    (566339291/50000000000000:ℝ) (1079967353/100000000000000:ℝ) (5915998361410316176869/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_352 (thetaFirstMode_refined_node_1056).2 (thetaFirstMode_refined_node_1057).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_353 :
    (20596503930369733/1000000000000000000000000:ℝ) ≤ ∫ x in (353/512:ℝ)..(177/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-26394039053179386408577491/100000000000000000000000000000:ℝ)*(thetaPowerMass 1 (353/512:ℝ) (177/256:ℝ)-(14961899000581170932457/21700646917646714268160:ℝ)*thetaPowerMass 0 (353/512:ℝ) (177/256:ℝ)) ≤
      thetaFirstModeFirst (14961899000581170932457/21700646917646714268160:ℝ)*(thetaPowerMass 1 (353/512:ℝ) (177/256:ℝ)-(14961899000581170932457/21700646917646714268160:ℝ)*thetaPowerMass 0 (353/512:ℝ) (177/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0534.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (353/512:ℝ) (177/256:ℝ)
    (14961899000581170932457/21700646917646714268160:ℝ) (1079573587/100000000000000:ℝ) (-26394039053179386408577491/100000000000000000000000000000:ℝ) (2843426264996510417569/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_353
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1061).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_353 :
    (∫ x in (353/512:ℝ)..(177/256:ℝ), x^0*thetaFirstMode x) ≤ (20596864811068331/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (353/512:ℝ) (177/256:ℝ)
    (1079967353/100000000000000:ℝ) (257378291/25000000000000:ℝ) (2843426264996510417569/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_353 (thetaFirstMode_refined_node_1057).2 (thetaFirstMode_refined_node_1062).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_354 :
    (9816201261339037/500000000000000000000000:ℝ) ≤ ∫ x in (177/256:ℝ)..(355/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1579362468182145371804977217/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (177/256:ℝ) (355/512:ℝ)-(177/256:ℝ)*thetaPowerMass 0 (177/256:ℝ) (355/512:ℝ)) ≤
      thetaFirstModeFirst (177/256:ℝ)*(thetaPowerMass 1 (177/256:ℝ) (355/512:ℝ)-(177/256:ℝ)*thetaPowerMass 0 (177/256:ℝ) (355/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0535.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (177/256:ℝ) (355/512:ℝ)
    (177/256:ℝ) (1029509059/100000000000000:ℝ) (-1579362468182145371804977217/6250000000000000000000000000000:ℝ) (1366381270650438608911/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_354
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1062).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_354 :
    (∫ x in (177/256:ℝ)..(355/512:ℝ), x^0*thetaFirstMode x) ≤ (19632756535874381/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (177/256:ℝ) (355/512:ℝ)
    (257378291/25000000000000:ℝ) (490614297/50000000000000:ℝ) (1366381270650438608911/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_354 (thetaFirstMode_refined_node_1062).2 (thetaFirstMode_refined_node_1063).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_355 :
    (18709859144194731/1000000000000000000000000:ℝ) ≤ ∫ x in (355/512:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6043200912031275833817705091/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (355/512:ℝ) (89/128:ℝ)-(3148466476744436255595/4540790783819398487552:ℝ)*thetaPowerMass 0 (355/512:ℝ) (89/128:ℝ)) ≤
      thetaFirstModeFirst (3148466476744436255595/4540790783819398487552:ℝ)*(thetaPowerMass 1 (355/512:ℝ) (89/128:ℝ)-(3148466476744436255595/4540790783819398487552:ℝ)*thetaPowerMass 0 (355/512:ℝ) (89/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0537.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (355/512:ℝ) (89/128:ℝ)
    (3148466476744436255595/4540790783819398487552:ℝ) (122608747/12500000000000:ℝ) (-6043200912031275833817705091/25000000000000000000000000000000:ℝ) (1312947952616355036517/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_355
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1067).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_355 :
    (∫ x in (355/512:ℝ)..(89/128:ℝ), x^0*thetaFirstMode x) ≤ (18710194336611489/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (355/512:ℝ) (89/128:ℝ)
    (490614297/50000000000000:ℝ) (467514603/50000000000000:ℝ) (1312947952616355036517/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_355 (thetaFirstMode_refined_node_1063).2 (thetaFirstMode_refined_node_1068).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_356 :
    (8913614400884461/500000000000000000000000:ℝ) ≤ ∫ x in (89/128:ℝ)..(357/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-90368457453903301604068887/390625000000000000000000000000:ℝ)*(thetaPowerMass 1 (89/128:ℝ) (357/512:ℝ)-(89/128:ℝ)*thetaPowerMass 0 (89/128:ℝ) (357/512:ℝ)) ≤
      thetaFirstModeFirst (89/128:ℝ)*(thetaPowerMass 1 (89/128:ℝ) (357/512:ℝ)-(89/128:ℝ)*thetaPowerMass 0 (89/128:ℝ) (357/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0538.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (89/128:ℝ) (357/512:ℝ)
    (89/128:ℝ) (935025449/100000000000000:ℝ) (-90368457453903301604068887/390625000000000000000000000000:ℝ) (2522716680051828661583/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_356
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1068).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_356 :
    (∫ x in (89/128:ℝ)..(357/512:ℝ), x^0*thetaFirstMode x) ≤ (3565511496066319/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (89/128:ℝ) (357/512:ℝ)
    (467514603/50000000000000:ℝ) (44541673/5000000000000:ℝ) (2522716680051828661583/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_356 (thetaFirstMode_refined_node_1068).2 (thetaFirstMode_refined_node_1069).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_357 :
    (16982969885470297/1000000000000000000000000:ℝ) ≤ ∫ x in (357/512:ℝ)..(179/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2765186390685839135396358809/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (357/512:ℝ) (179/256:ℝ)-(16558743671981150478993/23747617312889180700160:ℝ)*thetaPowerMass 0 (357/512:ℝ) (179/256:ℝ)) ≤
      thetaFirstModeFirst (16558743671981150478993/23747617312889180700160:ℝ)*(thetaPowerMass 1 (357/512:ℝ) (179/256:ℝ)-(16558743671981150478993/23747617312889180700160:ℝ)*thetaPowerMass 0 (357/512:ℝ) (179/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0540.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (357/512:ℝ) (179/256:ℝ)
    (16558743671981150478993/23747617312889180700160:ℝ) (890507093/100000000000000:ℝ) (-2765186390685839135396358809/12500000000000000000000000000000:ℝ) (4846235194980276675629/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_357
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1073).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_357 :
    (∫ x in (357/512:ℝ)..(179/256:ℝ), x^0*thetaFirstMode x) ≤ (16983281002580263/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (357/512:ℝ) (179/256:ℝ)
    (44541673/5000000000000:ℝ) (84856263/10000000000000:ℝ) (4846235194980276675629/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_357 (thetaFirstMode_refined_node_1069).2 (thetaFirstMode_refined_node_1074).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_358 :
    (8087774559534493/500000000000000000000000:ℝ) ≤ ∫ x in (179/256:ℝ)..(359/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-211629779594034971468791977/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (179/256:ℝ) (359/512:ℝ)-(179/256:ℝ)*thetaPowerMass 0 (179/256:ℝ) (359/512:ℝ)) ≤
      thetaFirstModeFirst (179/256:ℝ)*(thetaPowerMass 1 (179/256:ℝ) (359/512:ℝ)-(179/256:ℝ)*thetaPowerMass 0 (179/256:ℝ) (359/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0541.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (179/256:ℝ) (359/512:ℝ)
    (179/256:ℝ) (848559193/100000000000000:ℝ) (-211629779594034971468791977/1000000000000000000000000000000:ℝ) (930797510392505598467/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_358
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1074).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_358 :
    (∫ x in (179/256:ℝ)..(359/512:ℝ), x^0*thetaFirstMode x) ≤ (1010990879785271/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (179/256:ℝ) (359/512:ℝ)
    (84856263/10000000000000:ℝ) (10101759/1250000000000:ℝ) (930797510392505598467/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_358 (thetaFirstMode_refined_node_1074).2 (thetaFirstMode_refined_node_1075).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_359 :
    (7701764943140831/500000000000000000000000:ℝ) ≤ ∫ x in (359/512:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-316071539289992232798263901/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (359/512:ℝ) (45/64:ℝ)-(17412575849610501454191/24833020561715806159360:ℝ)*thetaPowerMass 0 (359/512:ℝ) (45/64:ℝ)) ≤
      thetaFirstModeFirst (17412575849610501454191/24833020561715806159360:ℝ)*(thetaPowerMass 1 (359/512:ℝ) (45/64:ℝ)-(17412575849610501454191/24833020561715806159360:ℝ)*thetaPowerMass 0 (359/512:ℝ) (45/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0543.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (359/512:ℝ) (45/64:ℝ)
    (17412575849610501454191/24833020561715806159360:ℝ) (201960981/25000000000000:ℝ) (-316071539289992232798263901/1562500000000000000000000000000:ℝ) (4468485357641962583949/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_359
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1079).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_359 :
    (∫ x in (359/512:ℝ)..(45/64:ℝ), x^0*thetaFirstMode x) ≤ (3850954610234567/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (359/512:ℝ) (45/64:ℝ)
    (10101759/1250000000000:ℝ) (769494387/100000000000000:ℝ) (4468485357641962583949/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_359 (thetaFirstMode_refined_node_1075).2 (thetaFirstMode_refined_node_1080).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_360 :
    (7332742072357101/500000000000000000000000:ℝ) ≤ ∫ x in (45/64:ℝ)..(361/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-9672283467914261141631424257/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (45/64:ℝ) (361/512:ℝ)-(45/64:ℝ)*thetaPowerMass 0 (45/64:ℝ) (361/512:ℝ)) ≤
      thetaFirstModeFirst (45/64:ℝ)*(thetaPowerMass 1 (45/64:ℝ) (361/512:ℝ)-(45/64:ℝ)*thetaPowerMass 0 (45/64:ℝ) (361/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0544.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (45/64:ℝ) (361/512:ℝ)
    (45/64:ℝ) (384745623/50000000000000:ℝ) (-9672283467914261141631424257/50000000000000000000000000000000:ℝ) (4289528190266634707247/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_360
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1080).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_360 :
    (∫ x in (45/64:ℝ)..(361/512:ℝ), x^0*thetaFirstMode x) ≤ (14665766866624637/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (45/64:ℝ) (361/512:ℝ)
    (769494387/100000000000000:ℝ) (732552861/100000000000000:ℝ) (4289528190266634707247/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_360 (thetaFirstMode_refined_node_1080).2 (thetaFirstMode_refined_node_1081).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_361 :
    (13960074218097803/1000000000000000000000000:ℝ) ≤ ∫ x in (361/512:ℝ)..(181/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-115520035896194767097871389/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (361/512:ℝ) (181/256:ℝ)-(18305321226441340498209/25961586427017257013760:ℝ)*thetaPowerMass 0 (361/512:ℝ) (181/256:ℝ)) ≤
      thetaFirstModeFirst (18305321226441340498209/25961586427017257013760:ℝ)*(thetaPowerMass 1 (361/512:ℝ) (181/256:ℝ)-(18305321226441340498209/25961586427017257013760:ℝ)*thetaPowerMass 0 (361/512:ℝ) (181/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0546.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (361/512:ℝ) (181/256:ℝ)
    (18305321226441340498209/25961586427017257013760:ℝ) (18307079/2500000000000:ℝ) (-115520035896194767097871389/625000000000000000000000000000:ℝ) (4116920219374762590193/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_361
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1085).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_361 :
    (∫ x in (361/512:ℝ)..(181/256:ℝ), x^0*thetaFirstMode x) ≤ (13960341633414121/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (361/512:ℝ) (181/256:ℝ)
    (732552861/100000000000000:ℝ) (697247869/100000000000000:ℝ) (4116920219374762590193/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_361 (thetaFirstMode_refined_node_1081).2 (thetaFirstMode_refined_node_1086).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_362 :
    (13285971123401491/1000000000000000000000000:ℝ) ≤ ∫ x in (181/256:ℝ)..(363/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-176685492325839229280298339/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (181/256:ℝ) (363/512:ℝ)-(181/256:ℝ)*thetaPowerMass 0 (181/256:ℝ) (363/512:ℝ)) ≤
      thetaFirstModeFirst (181/256:ℝ)*(thetaPowerMass 1 (181/256:ℝ) (363/512:ℝ)-(181/256:ℝ)*thetaPowerMass 0 (181/256:ℝ) (363/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0547.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (181/256:ℝ) (363/512:ℝ)
    (181/256:ℝ) (139449/20000000000:ℝ) (-176685492325839229280298339/1000000000000000000000000000000:ℝ) (3950470151824047310243/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_362
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1086).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_362 :
    (∫ x in (181/256:ℝ)..(363/512:ℝ), x^0*thetaFirstMode x) ≤ (1660779130703001/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (181/256:ℝ) (363/512:ℝ)
    (697247869/100000000000000:ℝ) (663513559/100000000000000:ℝ) (3950470151824047310243/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_362 (thetaFirstMode_refined_node_1086).2 (thetaFirstMode_refined_node_1087).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_363 :
    (12641930361827429/1000000000000000000000000:ℝ) ≤ ∫ x in (363/512:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1687514623963206965911636817/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (363/512:ℝ) (91/128:ℝ)-(19238522835046489117407/27134777857019009052160:ℝ)*thetaPowerMass 0 (363/512:ℝ) (91/128:ℝ)) ≤
      thetaFirstModeFirst (19238522835046489117407/27134777857019009052160:ℝ)*(thetaPowerMass 1 (363/512:ℝ) (91/128:ℝ)-(19238522835046489117407/27134777857019009052160:ℝ)*thetaPowerMass 0 (363/512:ℝ) (91/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0549.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (363/512:ℝ) (91/128:ℝ)
    (19238522835046489117407/27134777857019009052160:ℝ) (82908583/12500000000000:ℝ) (-1687514623963206965911636817/10000000000000000000000000000000:ℝ) (3789991154824592371277/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_363
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1091).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_363 :
    (∫ x in (363/512:ℝ)..(91/128:ℝ), x^0*thetaFirstMode x) ≤ (6321089003182369/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (363/512:ℝ) (91/128:ℝ)
    (663513559/100000000000000:ℝ) (63128643/10000000000000:ℝ) (3789991154824592371277/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_363 (thetaFirstMode_refined_node_1087).2 (thetaFirstMode_refined_node_1092).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_364 :
    (120267161661487/10000000000000000000000:ℝ) ≤ ∫ x in (91/128:ℝ)..(365/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-806250060539356585250390193/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (91/128:ℝ) (365/512:ℝ)-(91/128:ℝ)*thetaPowerMass 0 (91/128:ℝ) (365/512:ℝ)) ≤
      thetaFirstModeFirst (91/128:ℝ)*(thetaPowerMass 1 (91/128:ℝ) (365/512:ℝ)-(91/128:ℝ)*thetaPowerMass 0 (91/128:ℝ) (365/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0550.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (91/128:ℝ) (365/512:ℝ)
    (91/128:ℝ) (631283813/100000000000000:ℝ) (-806250060539356585250390193/5000000000000000000000000000000:ℝ) (908825205366282139397/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_364
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1092).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_364 :
    (∫ x in (91/128:ℝ)..(365/512:ℝ), x^0*thetaFirstMode x) ≤ (12026958611311301/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (91/128:ℝ) (365/512:ℝ)
    (63128643/10000000000000:ℝ) (300252629/50000000000000:ℝ) (908825205366282139397/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_364 (thetaFirstMode_refined_node_1092).2 (thetaFirstMode_refined_node_1093).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_365 :
    (11439171590314477/1000000000000000000000000:ℝ) ≤ ∫ x in (365/512:ℝ)..(183/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1924347272336788455977872753/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (365/512:ℝ) (183/256:ℝ)-(4042755171877232548485/5670819777946998205952:ℝ)*thetaPowerMass 0 (365/512:ℝ) (183/256:ℝ)) ≤
      thetaFirstModeFirst (4042755171877232548485/5670819777946998205952:ℝ)*(thetaPowerMass 1 (365/512:ℝ) (183/256:ℝ)-(4042755171877232548485/5670819777946998205952:ℝ)*thetaPowerMass 0 (365/512:ℝ) (183/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0552.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (365/512:ℝ) (183/256:ℝ)
    (4042755171877232548485/5670819777946998205952:ℝ) (600283057/100000000000000:ℝ) (-1924347272336788455977872753/12500000000000000000000000000000:ℝ) (435777636239628610867/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_365
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1097).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_365 :
    (∫ x in (365/512:ℝ)..(183/256:ℝ), x^0*thetaFirstMode x) ≤ (11439400762034657/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (365/512:ℝ) (183/256:ℝ)
    (300252629/50000000000000:ℝ) (142777757/25000000000000:ℝ) (435777636239628610867/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_365 (thetaFirstMode_refined_node_1093).2 (thetaFirstMode_refined_node_1098).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_366 :
    (87025188285101/8000000000000000000000:ℝ) ≤ ∫ x in (183/256:ℝ)..(367/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1838073775873858357444829143/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (183/256:ℝ) (367/512:ℝ)-(183/256:ℝ)*thetaPowerMass 0 (183/256:ℝ) (367/512:ℝ)) ≤
      thetaFirstModeFirst (183/256:ℝ)*(thetaPowerMass 1 (183/256:ℝ) (367/512:ℝ)-(183/256:ℝ)*thetaPowerMass 0 (183/256:ℝ) (367/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0553.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (183/256:ℝ) (367/512:ℝ)
    (183/256:ℝ) (571108641/100000000000000:ℝ) (-1838073775873858357444829143/12500000000000000000000000000000:ℝ) (3342578199994124527397/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_366
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1098).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_366 :
    (∫ x in (183/256:ℝ)..(367/512:ℝ), x^0*thetaFirstMode x) ≤ (10878372808606827/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (183/256:ℝ) (367/512:ℝ)
    (142777757/25000000000000:ℝ) (543046863/100000000000000:ℝ) (3342578199994124527397/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_366 (thetaFirstMode_refined_node_1098).2 (thetaFirstMode_refined_node_1099).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_367 :
    (10342572366766507/1000000000000000000000000:ℝ) ≤ ∫ x in (367/512:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1403305657409059003242985869/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (367/512:ℝ) (23/32:ℝ)-(21232729095465386243943/29621095571104304028160:ℝ)*thetaPowerMass 0 (367/512:ℝ) (23/32:ℝ)) ≤
      thetaFirstModeFirst (21232729095465386243943/29621095571104304028160:ℝ)*(thetaPowerMass 1 (367/512:ℝ) (23/32:ℝ)-(21232729095465386243943/29621095571104304028160:ℝ)*thetaPowerMass 0 (367/512:ℝ) (23/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0555.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (367/512:ℝ) (23/32:ℝ)
    (21232729095465386243943/29621095571104304028160:ℝ) (16963919/3125000000000:ℝ) (-1403305657409059003242985869/10000000000000000000000000000000:ℝ) (640840523008283373147/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_367
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1103).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_367 :
    (∫ x in (367/512:ℝ)..(23/32:ℝ), x^0*thetaFirstMode x) ≤ (5171392135176261/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (367/512:ℝ) (23/32:ℝ)
    (543046863/100000000000000:ℝ) (129064491/25000000000000:ℝ) (640840523008283373147/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_367 (thetaFirstMode_refined_node_1099).2 (thetaFirstMode_refined_node_1104).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_368 :
    (4915688633501181/500000000000000000000000:ℝ) ≤ ∫ x in (23/32:ℝ)..(369/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-104676146675398691099312967/781250000000000000000000000000:ℝ)*(thetaPowerMass 1 (23/32:ℝ) (369/512:ℝ)-(23/32:ℝ)*thetaPowerMass 0 (23/32:ℝ) (369/512:ℝ)) ≤
      thetaFirstModeFirst (23/32:ℝ)*(thetaPowerMass 1 (23/32:ℝ) (369/512:ℝ)-(23/32:ℝ)*thetaPowerMass 0 (23/32:ℝ) (369/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0556.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (23/32:ℝ) (369/512:ℝ)
    (23/32:ℝ) (51625579/10000000000000:ℝ) (-104676146675398691099312967/781250000000000000000000000000:ℝ) (614185791481402863651/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_368
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1104).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_368 :
    (∫ x in (23/32:ℝ)..(369/512:ℝ), x^0*thetaFirstMode x) ≤ (9831584546826701/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (23/32:ℝ) (369/512:ℝ)
    (129064491/25000000000000:ℝ) (245345769/50000000000000:ℝ) (614185791481402863651/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_368 (thetaFirstMode_refined_node_1104).2 (thetaFirstMode_refined_node_1105).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_369 :
    (4671782928816477/500000000000000000000000:ℝ) ≤ ∫ x in (369/512:ℝ)..(185/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1278148615429148365234817053/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (369/512:ℝ) (185/256:ℝ)-(22297086444538131163641/30937356888429438876160:ℝ)*thetaPowerMass 0 (369/512:ℝ) (185/256:ℝ)) ≤
      thetaFirstModeFirst (22297086444538131163641/30937356888429438876160:ℝ)*(thetaPowerMass 1 (369/512:ℝ) (185/256:ℝ)-(22297086444538131163641/30937356888429438876160:ℝ)*thetaPowerMass 0 (369/512:ℝ) (185/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0558.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (369/512:ℝ) (185/256:ℝ)
    (22297086444538131163641/30937356888429438876160:ℝ) (490509033/100000000000000:ℝ) (-1278148615429148365234817053/10000000000000000000000000000000:ℝ) (735648995948273803559/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_369
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1109).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_369 :
    (∫ x in (369/512:ℝ)..(185/256:ℝ), x^0*thetaFirstMode x) ≤ (72998137953627/7812500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (369/512:ℝ) (185/256:ℝ)
    (245345769/50000000000000:ℝ) (466296741/100000000000000:ℝ) (735648995948273803559/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_369 (thetaFirstMode_refined_node_1105).2 (thetaFirstMode_refined_node_1110).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_370 :
    (1109768700417913/125000000000000000000000:ℝ) ≤ ∫ x in (185/256:ℝ)..(371/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-6099319017296422764511609467/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (185/256:ℝ) (371/512:ℝ)-(185/256:ℝ)*thetaPowerMass 0 (185/256:ℝ) (371/512:ℝ)) ≤
      thetaFirstModeFirst (185/256:ℝ)*(thetaPowerMass 1 (185/256:ℝ) (371/512:ℝ)-(185/256:ℝ)*thetaPowerMass 0 (185/256:ℝ) (371/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0559.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (185/256:ℝ) (371/512:ℝ)
    (185/256:ℝ) (233147381/50000000000000:ℝ) (-6099319017296422764511609467/50000000000000000000000000000000:ℝ) (140952322835148533423/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_370
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1110).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_370 :
    (∫ x in (185/256:ℝ)..(371/512:ℝ), x^0*thetaFirstMode x) ≤ (8878341043487947/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (185/256:ℝ) (371/512:ℝ)
    (466296741/100000000000000:ℝ) (110756153/25000000000000:ℝ) (140952322835148533423/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_370 (thetaFirstMode_refined_node_1110).2 (thetaFirstMode_refined_node_1111).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_371 :
    (8434203582753809/1000000000000000000000000:ℝ) ≤ ∫ x in (371/512:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1454011857400306647204846291/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (371/512:ℝ) (93/128:ℝ)-(23408608439399087217159/32304515719285064680960:ℝ)*thetaPowerMass 0 (371/512:ℝ) (93/128:ℝ)) ≤
      thetaFirstModeFirst (23408608439399087217159/32304515719285064680960:ℝ)*(thetaPowerMass 1 (371/512:ℝ) (93/128:ℝ)-(23408608439399087217159/32304515719285064680960:ℝ)*thetaPowerMass 0 (371/512:ℝ) (93/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0561.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (371/512:ℝ) (93/128:ℝ)
    (23408608439399087217159/32304515719285064680960:ℝ) (110714851/25000000000000:ℝ) (-1454011857400306647204846291/12500000000000000000000000000000:ℝ) (2700127143493966204823/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_371
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1115).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_371 :
    (∫ x in (371/512:ℝ)..(93/128:ℝ), x^0*thetaFirstMode x) ≤ (4217192180368561/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (371/512:ℝ) (93/128:ℝ)
    (110756153/25000000000000:ℝ) (26301751/6250000000000:ℝ) (2700127143493966204823/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_371 (thetaFirstMode_refined_node_1111).2 (thetaFirstMode_refined_node_1116).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_372 :
    (8010811647973361/1000000000000000000000000:ℝ) ≤ ∫ x in (93/128:ℝ)..(373/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-173392836562073364920061637/1562500000000000000000000000000:ℝ)*(thetaPowerMass 1 (93/128:ℝ) (373/512:ℝ)-(93/128:ℝ)*thetaPowerMass 0 (93/128:ℝ) (373/512:ℝ)) ≤
      thetaFirstModeFirst (93/128:ℝ)*(thetaPowerMass 1 (93/128:ℝ) (373/512:ℝ)-(93/128:ℝ)*thetaPowerMass 0 (93/128:ℝ) (373/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0562.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (93/128:ℝ) (373/512:ℝ)
    (93/128:ℝ) (84165243/20000000000000:ℝ) (-173392836562073364920061637/1562500000000000000000000000000:ℝ) (517137743580598619471/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_372
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1116).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_372 :
    (∫ x in (93/128:ℝ)..(373/512:ℝ), x^0*thetaFirstMode x) ≤ (8010988333385101/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (93/128:ℝ) (373/512:ℝ)
    (26301751/6250000000000:ℝ) (399661583/100000000000000:ℝ) (517137743580598619471/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_372 (thetaFirstMode_refined_node_1116).2 (thetaFirstMode_refined_node_1117).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_373 :
    (1901779216880961/250000000000000000000000:ℝ) ≤ ∫ x in (373/512:ℝ)..(187/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-264435203008256743296270249/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (373/512:ℝ) (187/256:ℝ)-(24569113804309940929857/33724249796067390492160:ℝ)*thetaPowerMass 0 (373/512:ℝ) (187/256:ℝ)) ≤
      thetaFirstModeFirst (24569113804309940929857/33724249796067390492160:ℝ)*(thetaPowerMass 1 (373/512:ℝ) (187/256:ℝ)-(24569113804309940929857/33724249796067390492160:ℝ)*thetaPowerMass 0 (373/512:ℝ) (187/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0564.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (373/512:ℝ) (187/256:ℝ)
    (24569113804309940929857/33724249796067390492160:ℝ) (399512151/100000000000000:ℝ) (-264435203008256743296270249/2500000000000000000000000000000:ℝ) (24755857020076652059/10000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_373
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1121).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_373 :
    (∫ x in (373/512:ℝ)..(187/256:ℝ), x^0*thetaFirstMode x) ≤ (3803641813964171/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (373/512:ℝ) (187/256:ℝ)
    (399661583/100000000000000:ℝ) (189740827/50000000000000:ℝ) (24755857020076652059/10000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_373 (thetaFirstMode_refined_node_1117).2 (thetaFirstMode_refined_node_1122).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_374 :
    (1444454167369351/200000000000000000000000:ℝ) ≤ ∫ x in (187/256:ℝ)..(375/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1260852495702064930398199841/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (187/256:ℝ) (375/512:ℝ)-(187/256:ℝ)*thetaPowerMass 0 (187/256:ℝ) (375/512:ℝ)) ≤
      thetaFirstModeFirst (187/256:ℝ)*(thetaPowerMass 1 (187/256:ℝ) (375/512:ℝ)-(187/256:ℝ)*thetaPowerMass 0 (187/256:ℝ) (375/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0565.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (187/256:ℝ) (375/512:ℝ)
    (187/256:ℝ) (379480017/100000000000000:ℝ) (-1260852495702064930398199841/12500000000000000000000000000000:ℝ) (592419104592830041533/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_374
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1122).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_374 :
    (∫ x in (187/256:ℝ)..(375/512:ℝ), x^0*thetaFirstMode x) ≤ (144448675201323/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (187/256:ℝ) (375/512:ℝ)
    (189740827/50000000000000:ℝ) (360246223/100000000000000:ℝ) (592419104592830041533/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_374 (thetaFirstMode_refined_node_1122).2 (thetaFirstMode_refined_node_1123).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_375 :
    (6855480307716523/1000000000000000000000000:ℝ) ≤ ∫ x in (375/512:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-4805212075176561956723846719/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (375/512:ℝ) (47/64:ℝ)-(5156096209822605445875/7039656537271006218752:ℝ)*thetaPowerMass 0 (375/512:ℝ) (47/64:ℝ)) ≤
      thetaFirstModeFirst (5156096209822605445875/7039656537271006218752:ℝ)*(thetaPowerMass 1 (375/512:ℝ) (47/64:ℝ)-(5156096209822605445875/7039656537271006218752:ℝ)*thetaPowerMass 0 (375/512:ℝ) (47/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0567.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (375/512:ℝ) (47/64:ℝ)
    (5156096209822605445875/7039656537271006218752:ℝ) (5626737/1562500000000:ℝ) (-4805212075176561956723846719/50000000000000000000000000000000:ℝ) (2267822886854552488229/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_375
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1127).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_375 :
    (∫ x in (375/512:ℝ)..(47/64:ℝ), x^0*thetaFirstMode x) ≤ (6855634030311621/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (375/512:ℝ) (47/64:ℝ)
    (360246223/100000000000000:ℝ) (170957443/50000000000000:ℝ) (2267822886854552488229/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_375 (thetaFirstMode_refined_node_1123).2 (thetaFirstMode_refined_node_1128).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_376 :
    (6505960325873601/1000000000000000000000000:ℝ) ≤ ∫ x in (47/64:ℝ)..(377/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1145112097028617429455255919/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (47/64:ℝ) (377/512:ℝ)-(47/64:ℝ)*thetaPowerMass 0 (47/64:ℝ) (377/512:ℝ)) ≤
      thetaFirstModeFirst (47/64:ℝ)*(thetaPowerMass 1 (47/64:ℝ) (377/512:ℝ)-(47/64:ℝ)*thetaPowerMass 0 (47/64:ℝ) (377/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0568.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (47/64:ℝ) (377/512:ℝ)
    (47/64:ℝ) (341913399/100000000000000:ℝ) (-1145112097028617429455255919/12500000000000000000000000000000:ℝ) (2169890816883034985239/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_376
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1128).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_376 :
    (∫ x in (47/64:ℝ)..(377/512:ℝ), x^0*thetaFirstMode x) ≤ (6506110449777691/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (47/64:ℝ) (377/512:ℝ)
    (170957443/50000000000000:ℝ) (162224391/50000000000000:ℝ) (2169890816883034985239/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_376 (thetaFirstMode_refined_node_1128).2 (thetaFirstMode_refined_node_1129).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_377 :
    (6172977156951043/1000000000000000000000000:ℝ) ≤ ∫ x in (377/512:ℝ)..(189/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-545286864636167868801445357/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (377/512:ℝ) (189/256:ℝ)-(27044650098091245441393/36728384789253236892160:ℝ)*thetaPowerMass 0 (377/512:ℝ) (189/256:ℝ)) ≤
      thetaFirstModeFirst (27044650098091245441393/36728384789253236892160:ℝ)*(thetaPowerMass 1 (377/512:ℝ) (189/256:ℝ)-(27044650098091245441393/36728384789253236892160:ℝ)*thetaPowerMass 0 (377/512:ℝ) (189/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0570.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (377/512:ℝ) (189/256:ℝ)
    (27044650098091245441393/36728384789253236892160:ℝ) (162163409/50000000000000:ℝ) (-545286864636167868801445357/6250000000000000000000000000000:ℝ) (259468686495719689509/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_377
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1133).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_377 :
    (∫ x in (377/512:ℝ)..(189/256:ℝ), x^0*thetaFirstMode x) ≤ (6173118744155091/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (377/512:ℝ) (189/256:ℝ)
    (162224391/50000000000000:ℝ) (6156211/2000000000000:ℝ) (259468686495719689509/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_377 (thetaFirstMode_refined_node_1129).2 (thetaFirstMode_refined_node_1134).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_378 :
    (1463951301129111/250000000000000000000000:ℝ) ≤ ∫ x in (189/256:ℝ)..(379/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-83130324026398652861857689/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (189/256:ℝ) (379/512:ℝ)-(189/256:ℝ)*thetaPowerMass 0 (189/256:ℝ) (379/512:ℝ)) ≤
      thetaFirstModeFirst (189/256:ℝ)*(thetaPowerMass 1 (189/256:ℝ) (379/512:ℝ)-(189/256:ℝ)*thetaPowerMass 0 (189/256:ℝ) (379/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0571.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (189/256:ℝ) (379/512:ℝ)
    (189/256:ℝ) (153904601/50000000000000:ℝ) (-83130324026398652861857689/1000000000000000000000000000000:ℝ) (397054344780609058479/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_378
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1134).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_378 :
    (∫ x in (189/256:ℝ)..(379/512:ℝ), x^0*thetaFirstMode x) ≤ (5855943396709523/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (189/256:ℝ) (379/512:ℝ)
    (6156211/2000000000000:ℝ) (145982137/50000000000000:ℝ) (397054344780609058479/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_378 (thetaFirstMode_refined_node_1134).2 (thetaFirstMode_refined_node_1135).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_379 :
    (5553766341812931/1000000000000000000000000:ℝ) ≤ ∫ x in (379/512:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-791377732703526067616334143/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (379/512:ℝ) (95/128:ℝ)-(28363623954139189416591/38316374347894276840960:ℝ)*thetaPowerMass 0 (379/512:ℝ) (95/128:ℝ)) ≤
      thetaFirstModeFirst (28363623954139189416591/38316374347894276840960:ℝ)*(thetaPowerMass 1 (379/512:ℝ) (95/128:ℝ)-(28363623954139189416591/38316374347894276840960:ℝ)*thetaPowerMass 0 (379/512:ℝ) (95/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0573.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (379/512:ℝ) (95/128:ℝ)
    (28363623954139189416591/38316374347894276840960:ℝ) (145927111/50000000000000:ℝ) (-791377732703526067616334143/10000000000000000000000000000000:ℝ) (379666759753091419853/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_379
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1139).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_379 :
    (∫ x in (379/512:ℝ)..(95/128:ℝ), x^0*thetaFirstMode x) ≤ (5553896632690203/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (379/512:ℝ) (95/128:ℝ)
    (145982137/50000000000000:ℝ) (138437717/50000000000000:ℝ) (379666759753091419853/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_379 (thetaFirstMode_refined_node_1135).2 (thetaFirstMode_refined_node_1140).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_380 :
    (5266190407088743/1000000000000000000000000:ℝ) ≤ ∫ x in (95/128:ℝ)..(381/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-942162689641245045442288017/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (95/128:ℝ) (381/512:ℝ)-(95/128:ℝ)*thetaPowerMass 0 (95/128:ℝ) (381/512:ℝ)) ≤
      thetaFirstModeFirst (95/128:ℝ)*(thetaPowerMass 1 (95/128:ℝ) (381/512:ℝ)-(95/128:ℝ)*thetaPowerMass 0 (95/128:ℝ) (381/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0574.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (95/128:ℝ) (381/512:ℝ)
    (95/128:ℝ) (69218553/25000000000000:ℝ) (-942162689641245045442288017/12500000000000000000000000000000:ℝ) (1814815400513528103253/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_380
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1140).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_380 :
    (∫ x in (95/128:ℝ)..(381/512:ℝ), x^0*thetaFirstMode x) ≤ (1316579382676353/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (95/128:ℝ) (381/512:ℝ)
    (138437717/50000000000000:ℝ) (16406929/6250000000000:ℝ) (1814815400513528103253/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_380 (thetaFirstMode_refined_node_1140).2 (thetaFirstMode_refined_node_1141).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_381 :
    (1248112817805151/250000000000000000000000:ℝ) ≤ ∫ x in (381/512:ℝ)..(191/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-896532731548993082115411401/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (381/512:ℝ) (191/256:ℝ)-(29739470398816532457609/39964118478267692316160:ℝ)*thetaPowerMass 0 (381/512:ℝ) (191/256:ℝ)) ≤
      thetaFirstModeFirst (29739470398816532457609/39964118478267692316160:ℝ)*(thetaPowerMass 1 (381/512:ℝ) (191/256:ℝ)-(29739470398816532457609/39964118478267692316160:ℝ)*thetaPowerMass 0 (381/512:ℝ) (191/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0576.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (381/512:ℝ) (191/256:ℝ)
    (29739470398816532457609/39964118478267692316160:ℝ) (262411641/100000000000000:ℝ) (-896532731548993082115411401/12500000000000000000000000000000:ℝ) (1734599552978536839827/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_381
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1145).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_381 :
    (∫ x in (381/512:ℝ)..(191/256:ℝ), x^0*thetaFirstMode x) ≤ (4992571085258513/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (381/512:ℝ) (191/256:ℝ)
    (16406929/6250000000000:ℝ) (124419349/50000000000000:ℝ) (1734599552978536839827/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_381 (thetaFirstMode_refined_node_1141).2 (thetaFirstMode_refined_node_1146).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_382 :
    (236596524412413/50000000000000000000000:ℝ) ≤ ∫ x in (191/256:ℝ)..(383/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-341408544029594829048809063/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (191/256:ℝ) (383/512:ℝ)-(191/256:ℝ)*thetaPowerMass 0 (191/256:ℝ) (383/512:ℝ)) ≤
      thetaFirstModeFirst (191/256:ℝ)*(thetaPowerMass 1 (191/256:ℝ) (383/512:ℝ)-(191/256:ℝ)*thetaPowerMass 0 (191/256:ℝ) (383/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0577.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (191/256:ℝ) (383/512:ℝ)
    (191/256:ℝ) (248837591/100000000000000:ℝ) (-341408544029594829048809063/5000000000000000000000000000000:ℝ) (207196567415648073727/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_382
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1146).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_382 :
    (∫ x in (191/256:ℝ)..(383/512:ℝ), x^0*thetaFirstMode x) ≤ (473204732789171/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (191/256:ℝ) (383/512:ℝ)
    (124419349/50000000000000:ℝ) (117914167/50000000000000:ℝ) (207196567415648073727/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_382 (thetaFirstMode_refined_node_1146).2 (thetaFirstMode_refined_node_1147).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_383 :
    (28025315108809/6250000000000000000000:ℝ) ≤ ∫ x in (383/512:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1623674954201119793003664367/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (383/512:ℝ) (3/4:ℝ)-(31174323728860831314807/41673534214555068828160:ℝ)*thetaPowerMass 0 (383/512:ℝ) (3/4:ℝ)) ≤
      thetaFirstModeFirst (31174323728860831314807/41673534214555068828160:ℝ)*(thetaPowerMass 1 (383/512:ℝ) (3/4:ℝ)-(31174323728860831314807/41673534214555068828160:ℝ)*thetaPowerMass 0 (383/512:ℝ) (3/4:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0579.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (383/512:ℝ) (3/4:ℝ)
    (31174323728860831314807/41673534214555068828160:ℝ) (235738949/100000000000000:ℝ) (-1623674954201119793003664367/25000000000000000000000000000000:ℝ) (158362387583252580279/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_383
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1151).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_383 :
    (∫ x in (383/512:ℝ)..(3/4:ℝ), x^0*thetaFirstMode x) ≤ (22420802485621/5000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (383/512:ℝ) (3/4:ℝ)
    (117914167/50000000000000:ℝ) (44690077/20000000000000:ℝ) (158362387583252580279/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_383 (thetaFirstMode_refined_node_1147).2 (thetaFirstMode_refined_node_1152).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator

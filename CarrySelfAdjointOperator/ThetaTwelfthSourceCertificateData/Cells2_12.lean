import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature12
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative18
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative19

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_2_384 :
    (1197916405057941/500000000000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(385/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2939062812782684309853/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (3/4:ℝ) (385/512:ℝ)-(385/512:ℝ)*thetaPowerMass 2 (3/4:ℝ) (385/512:ℝ)) ≤
      thetaFirstModeFirst (385/512:ℝ)*(thetaPowerMass 3 (3/4:ℝ) (385/512:ℝ)-(385/512:ℝ)*thetaPowerMass 2 (3/4:ℝ) (385/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0581.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (3/4:ℝ) (385/512:ℝ)
    (385/512:ℝ) (211675683/100000000000000:ℝ) (-2939062812782684309853/50000000000000000000000000:ℝ) (1512646200463755506153/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_384
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1153).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_384 :
    (∫ x in (3/4:ℝ)..(385/512:ℝ), x^2*thetaFirstMode x) ≤ (2395868187992487/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/4:ℝ) (385/512:ℝ)
    (44690077/20000000000000:ℝ) (211676637/100000000000000:ℝ) (1512646200463755506153/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_384 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1153).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_385 :
    (1140574190319853/500000000000000000000000:ℝ) ≤ ∫ x in (385/512:ℝ)..(193/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2938054038277696384625885119/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (385/512:ℝ) (193/256:ℝ)-(6534077305948613955765/8689317914228980285952:ℝ)*thetaPowerMass 2 (385/512:ℝ) (193/256:ℝ)) ≤
      thetaFirstModeFirst (6534077305948613955765/8689317914228980285952:ℝ)*(thetaPowerMass 3 (385/512:ℝ) (193/256:ℝ)-(6534077305948613955765/8689317914228980285952:ℝ)*thetaPowerMass 2 (385/512:ℝ) (193/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0582.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (385/512:ℝ) (193/256:ℝ)
    (6534077305948613955765/8689317914228980285952:ℝ) (10579809/5000000000000:ℝ) (-2938054038277696384625885119/50000000000000000000000000000000:ℝ) (1444535251539540222233/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_385
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1157).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_385 :
    (∫ x in (385/512:ℝ)..(193/256:ℝ), x^2*thetaFirstMode x) ≤ (285150714670251/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (385/512:ℝ) (193/256:ℝ)
    (211676637/100000000000000:ℝ) (50120003/25000000000000:ℝ) (1444535251539540222233/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_385 (thetaFirstMode_refined_node_1153).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_386 :
    (2171499550169537/1000000000000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(387/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-2656836907245666823941/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (193/256:ℝ) (387/512:ℝ)-(387/512:ℝ)*thetaPowerMass 2 (193/256:ℝ) (387/512:ℝ)) ≤
      thetaFirstModeFirst (387/512:ℝ)*(thetaPowerMass 3 (193/256:ℝ) (387/512:ℝ)-(387/512:ℝ)*thetaPowerMass 2 (193/256:ℝ) (387/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0584.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (193/256:ℝ) (387/512:ℝ)
    (387/512:ℝ) (189833661/100000000000000:ℝ) (-2656836907245666823941/50000000000000000000000000:ℝ) (43099680239324046491/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_386
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1159).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_386 :
    (∫ x in (193/256:ℝ)..(387/512:ℝ), x^2*thetaFirstMode x) ≤ (1085766137833881/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (193/256:ℝ) (387/512:ℝ)
    (50120003/25000000000000:ℝ) (189834523/100000000000000:ℝ) (43099680239324046491/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_386 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1159).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_387 :
    (413320480919263/200000000000000000000000:ℝ) ≤ ∫ x in (387/512:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-53118438712850890005802797/1000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (387/512:ℝ) (97/128:ℝ)-(34229931486855451316343/45285304621504058652160:ℝ)*thetaPowerMass 2 (387/512:ℝ) (97/128:ℝ)) ≤
      thetaFirstModeFirst (34229931486855451316343/45285304621504058652160:ℝ)*(thetaPowerMass 3 (387/512:ℝ) (97/128:ℝ)-(34229931486855451316343/45285304621504058652160:ℝ)*thetaPowerMass 2 (387/512:ℝ) (97/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0585.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (387/512:ℝ) (97/128:ℝ)
    (34229931486855451316343/45285304621504058652160:ℝ) (47440541/25000000000000:ℝ) (-53118438712850890005802797/1000000000000000000000000000000:ℝ) (1316511465572846673839/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_387
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1163).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_387 :
    (∫ x in (387/512:ℝ)..(97/128:ℝ), x^2*thetaFirstMode x) ≤ (413331107484121/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (387/512:ℝ) (97/128:ℝ)
    (189834523/100000000000000:ℝ) (179715241/100000000000000:ℝ) (1316511465572846673839/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_387 (thetaFirstMode_refined_node_1159).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_388 :
    (1966359209419491/1000000000000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(389/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1199810983116795438807/25000000000000000000000000:ℝ)*(thetaPowerMass 3 (97/128:ℝ) (389/512:ℝ)-(389/512:ℝ)*thetaPowerMass 2 (97/128:ℝ) (389/512:ℝ)) ≤
      thetaFirstModeFirst (389/512:ℝ)*(thetaPowerMass 3 (97/128:ℝ) (389/512:ℝ)-(389/512:ℝ)*thetaPowerMass 2 (97/128:ℝ) (389/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0587.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (97/128:ℝ) (389/512:ℝ)
    (389/512:ℝ) (85048737/50000000000000:ℝ) (-1199810983116795438807/25000000000000000000000000:ℝ) (125640493830125248933/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_388
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1165).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_388 :
    (∫ x in (97/128:ℝ)..(389/512:ℝ), x^2*thetaFirstMode x) ≤ (1966389449182819/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (97/128:ℝ) (389/512:ℝ)
    (179715241/100000000000000:ℝ) (42524563/25000000000000:ℝ) (125640493830125248933/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_388 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1165).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_389 :
    (187050486332529/100000000000000000000000:ℝ) ≤ ∫ x in (389/512:ℝ)..(195/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-299849097179838837701341767/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (389/512:ℝ) (195/256:ℝ)-(35855303234927171773041/47191752594083278773760:ℝ)*thetaPowerMass 2 (389/512:ℝ) (195/256:ℝ)) ≤
      thetaFirstModeFirst (35855303234927171773041/47191752594083278773760:ℝ)*(thetaPowerMass 3 (389/512:ℝ) (195/256:ℝ)-(35855303234927171773041/47191752594083278773760:ℝ)*thetaPowerMass 2 (389/512:ℝ) (195/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0588.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (389/512:ℝ) (195/256:ℝ)
    (35855303234927171773041/47191752594083278773760:ℝ) (17003323/10000000000000:ℝ) (-299849097179838837701341767/6250000000000000000000000000000:ℝ) (599388808956942227249/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_389
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1169).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_389 :
    (∫ x in (389/512:ℝ)..(195/256:ℝ), x^2*thetaFirstMode x) ≤ (1870554068207317/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (389/512:ℝ) (195/256:ℝ)
    (42524563/25000000000000:ℝ) (257537/160000000000:ℝ) (599388808956942227249/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_389 (thetaFirstMode_refined_node_1165).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_390 :
    (889473738432363/500000000000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(391/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-108270392241695314659/2500000000000000000000000:ℝ)*(thetaPowerMass 3 (195/256:ℝ) (391/512:ℝ)-(391/512:ℝ)*thetaPowerMass 2 (195/256:ℝ) (391/512:ℝ)) ≤
      thetaFirstModeFirst (391/512:ℝ)*(thetaPowerMass 3 (195/256:ℝ) (391/512:ℝ)-(391/512:ℝ)*thetaPowerMass 2 (195/256:ℝ) (391/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0590.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (195/256:ℝ) (391/512:ℝ)
    (391/512:ℝ) (15227967/10000000000000:ℝ) (-108270392241695314659/2500000000000000000000000:ℝ) (228707943376429807781/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_390
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1171).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_390 :
    (∫ x in (195/256:ℝ)..(391/512:ℝ), x^2*thetaFirstMode x) ≤ (444743853240537/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (195/256:ℝ) (391/512:ℝ)
    (257537/160000000000:ℝ) (152280373/100000000000000:ℝ) (228707943376429807781/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_390 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1171).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_391 :
    (845719889060417/500000000000000000000000:ℝ) ≤ ∫ x in (391/512:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-270582132373772827394153683/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (391/512:ℝ) (49/64:ℝ)-(37548920246270157404559/49168060985435061199360:ℝ)*thetaPowerMass 2 (391/512:ℝ) (49/64:ℝ)) ≤
      thetaFirstModeFirst (37548920246270157404559/49168060985435061199360:ℝ)*(thetaPowerMass 3 (391/512:ℝ) (49/64:ℝ)-(37548920246270157404559/49168060985435061199360:ℝ)*thetaPowerMass 2 (391/512:ℝ) (49/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0591.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (391/512:ℝ) (49/64:ℝ)
    (37548920246270157404559/49168060985435061199360:ℝ) (152221993/100000000000000:ℝ) (-270582132373772827394153683/6250000000000000000000000000000:ℝ) (545302077230300748787/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_391
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1175).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_391 :
    (∫ x in (391/512:ℝ)..(49/64:ℝ), x^2*thetaFirstMode x) ≤ (105717831829121/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (391/512:ℝ) (49/64:ℝ)
    (152280373/100000000000000:ℝ) (72018211/50000000000000:ℝ) (545302077230300748787/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_391 (thetaFirstMode_refined_node_1171).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_392 :
    (1607895472314013/1000000000000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(393/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-61010217271264374633/1562500000000000000000000:ℝ)*(thetaPowerMass 3 (49/64:ℝ) (393/512:ℝ)-(393/512:ℝ)*thetaPowerMass 2 (49/64:ℝ) (393/512:ℝ)) ≤
      thetaFirstModeFirst (393/512:ℝ)*(thetaPowerMass 3 (49/64:ℝ) (393/512:ℝ)-(393/512:ℝ)*thetaPowerMass 2 (49/64:ℝ) (393/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0593.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (49/64:ℝ) (393/512:ℝ)
    (393/512:ℝ) (68103971/50000000000000:ℝ) (-61010217271264374633/1562500000000000000000000:ℝ) (20797729653449226181/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_392
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1177).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_392 :
    (∫ x in (49/64:ℝ)..(393/512:ℝ), x^2*thetaFirstMode x) ≤ (160792124346541/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (49/64:ℝ) (393/512:ℝ)
    (72018211/50000000000000:ℝ) (5448343/4000000000000:ℝ) (20797729653449226181/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_392 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1177).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_393 :
    (1528084156737851/1000000000000000000000000:ℝ) ≤ ∫ x in (393/512:ℝ)..(197/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-243955966584715408959034827/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (393/512:ℝ) (197/256:ℝ)-(39313276758463040392257/51216412690723244700160:ℝ)*thetaPowerMass 2 (393/512:ℝ) (197/256:ℝ)) ≤
      thetaFirstModeFirst (39313276758463040392257/51216412690723244700160:ℝ)*(thetaPowerMass 3 (393/512:ℝ) (197/256:ℝ)-(39313276758463040392257/51216412690723244700160:ℝ)*thetaPowerMass 2 (393/512:ℝ) (197/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0594.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (393/512:ℝ) (197/256:ℝ)
    (39313276758463040392257/51216412690723244700160:ℝ) (68078103/50000000000000:ℝ) (-243955966584715408959034827/6250000000000000000000000000000:ℝ) (991304873654742215107/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_393
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1181).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_393 :
    (∫ x in (393/512:ℝ)..(197/256:ℝ), x^2*thetaFirstMode x) ≤ (1528126223263679/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (393/512:ℝ) (197/256:ℝ)
    (5448343/4000000000000:ℝ) (32194371/25000000000000:ℝ) (991304873654742215107/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_393 (thetaFirstMode_refined_node_1177).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_394 :
    (362981218735439/250000000000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(395/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-219830713874743950111/6250000000000000000000000:ℝ)*(thetaPowerMass 3 (197/256:ℝ) (395/512:ℝ)-(395/512:ℝ)*thetaPowerMass 2 (197/256:ℝ) (395/512:ℝ)) ≤
      thetaFirstModeFirst (395/512:ℝ)*(thetaPowerMass 3 (197/256:ℝ) (395/512:ℝ)-(395/512:ℝ)*thetaPowerMass 2 (197/256:ℝ) (395/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0596.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (197/256:ℝ) (395/512:ℝ)
    (395/512:ℝ) (121724043/100000000000000:ℝ) (-219830713874743950111/6250000000000000000000000:ℝ) (944780016879046322359/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_394
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1183).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_394 :
    (∫ x in (197/256:ℝ)..(395/512:ℝ), x^2*thetaFirstMode x) ≤ (1451948623429369/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (197/256:ℝ) (395/512:ℝ)
    (32194371/25000000000000:ℝ) (121724613/100000000000000:ℝ) (944780016879046322359/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_394 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1183).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_395 :
    (689601584782421/500000000000000000000000:ℝ) ≤ ∫ x in (395/512:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-87901588057022216815845429/2500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (395/512:ℝ) (99/128:ℝ)-(8230188948417592711155/10667809430360898647552:ℝ)*thetaPowerMass 2 (395/512:ℝ) (99/128:ℝ)) ≤
      thetaFirstModeFirst (8230188948417592711155/10667809430360898647552:ℝ)*(thetaPowerMass 3 (395/512:ℝ) (99/128:ℝ)-(8230188948417592711155/10667809430360898647552:ℝ)*thetaPowerMass 2 (395/512:ℝ) (99/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0597.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (395/512:ℝ) (99/128:ℝ)
    (8230188948417592711155/10667809430360898647552:ℝ) (60838837/50000000000000:ℝ) (-87901588057022216815845429/2500000000000000000000000000000:ℝ) (900235061987027897989/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_395
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1187).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_395 :
    (∫ x in (395/512:ℝ)..(99/128:ℝ), x^2*thetaFirstMode x) ≤ (1379242027860919/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (395/512:ℝ) (99/128:ℝ)
    (121724613/100000000000000:ℝ) (115032211/100000000000000:ℝ) (900235061987027897989/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_395 (thetaFirstMode_refined_node_1183).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_396 :
    (1309843240785853/1000000000000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(397/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-1582756457897761047819/50000000000000000000000000:ℝ)*(thetaPowerMass 3 (99/128:ℝ) (397/512:ℝ)-(397/512:ℝ)*thetaPowerMass 2 (99/128:ℝ) (397/512:ℝ)) ≤
      thetaFirstModeFirst (397/512:ℝ)*(thetaPowerMass 3 (99/128:ℝ) (397/512:ℝ)-(397/512:ℝ)*thetaPowerMass 2 (99/128:ℝ) (397/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0599.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (99/128:ℝ) (397/512:ℝ)
    (397/512:ℝ) (108682771/100000000000000:ℝ) (-1582756457897761047819/50000000000000000000000000:ℝ) (428797801111739030787/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_396
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1189).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_396 :
    (∫ x in (99/128:ℝ)..(397/512:ℝ), x^2*thetaFirstMode x) ≤ (654932557409507/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (99/128:ℝ) (397/512:ℝ)
    (115032211/100000000000000:ℝ) (27170821/25000000000000:ℝ) (428797801111739030787/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_396 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1189).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_397 :
    (621822834834307/500000000000000000000000:ℝ) ≤ ∫ x in (397/512:ℝ)..(199/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-197775250872396195097220583/6250000000000000000000000000000:ℝ)*(thetaPowerMass 3 (397/512:ℝ) (199/256:ℝ)-(43064575909141158188793/55538261523062839068160:ℝ)*thetaPowerMass 2 (397/512:ℝ) (199/256:ℝ)) ≤
      thetaFirstModeFirst (43064575909141158188793/55538261523062839068160:ℝ)*(thetaPowerMass 3 (397/512:ℝ) (199/256:ℝ)-(43064575909141158188793/55538261523062839068160:ℝ)*thetaPowerMass 2 (397/512:ℝ) (199/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0600.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (397/512:ℝ) (199/256:ℝ)
    (43064575909141158188793/55538261523062839068160:ℝ) (108641251/100000000000000:ℝ) (-197775250872396195097220583/6250000000000000000000000000000:ℝ) (816789565727244178923/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_397
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1193).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_397 :
    (∫ x in (397/512:ℝ)..(199/256:ℝ), x^2*thetaFirstMode x) ≤ (1243681510662561/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (397/512:ℝ) (199/256:ℝ)
    (27170821/25000000000000:ℝ) (25665391/25000000000000:ℝ) (816789565727244178923/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_397 (thetaFirstMode_refined_node_1189).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_398 :
    (59026975320349/50000000000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(399/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-17789622286559827833/625000000000000000000000:ℝ)*(thetaPowerMass 3 (199/256:ℝ) (399/512:ℝ)-(399/512:ℝ)*thetaPowerMass 2 (199/256:ℝ) (399/512:ℝ)) ≤
      thetaFirstModeFirst (399/512:ℝ)*(thetaPowerMass 3 (199/256:ℝ) (399/512:ℝ)-(399/512:ℝ)*thetaPowerMass 2 (199/256:ℝ) (399/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0602.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (199/256:ℝ) (399/512:ℝ)
    (399/512:ℝ) (4847551/5000000000000:ℝ) (-17789622286559827833/625000000000000000000000:ℝ) (194436798485739133227/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_398
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1195).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_398 :
    (∫ x in (199/256:ℝ)..(399/512:ℝ), x^2*thetaFirstMode x) ≤ (590279817404241/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (199/256:ℝ) (399/512:ℝ)
    (25665391/25000000000000:ℝ) (96951481/100000000000000:ℝ) (194436798485739133227/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_398 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1195).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_399 :
    (280084887979079/250000000000000000000000:ℝ) ≤ ∫ x in (399/512:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x := by
  have hd : (-284533901394894733744266069/10000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (399/512:ℝ) (25/32:ℝ)-(45056903762744623817991/57816411855179361794560:ℝ)*thetaPowerMass 2 (399/512:ℝ) (25/32:ℝ)) ≤
      thetaFirstModeFirst (45056903762744623817991/57816411855179361794560:ℝ)*(thetaPowerMass 3 (399/512:ℝ) (25/32:ℝ)-(45056903762744623817991/57816411855179361794560:ℝ)*thetaPowerMass 2 (399/512:ℝ) (25/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0603.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (399/512:ℝ) (25/32:ℝ)
    (45056903762744623817991/57816411855179361794560:ℝ) (96913873/100000000000000:ℝ) (-284533901394894733744266069/10000000000000000000000000000000:ℝ) (370200483421154245411/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_399
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1199).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_399 :
    (∫ x in (399/512:ℝ)..(25/32:ℝ), x^2*thetaFirstMode x) ≤ (11203725893707/10000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (399/512:ℝ) (25/32:ℝ)
    (96951481/100000000000000:ℝ) (91538141/100000000000000:ℝ) (370200483421154245411/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_399 (thetaFirstMode_refined_node_1195).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_400 :
    (531489756642119/500000000000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(401/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-12785070771648217/500000000000000000000:ℝ)*(thetaPowerMass 3 (25/32:ℝ) (401/512:ℝ)-(401/512:ℝ)*thetaPowerMass 2 (25/32:ℝ) (401/512:ℝ)) ≤
      thetaFirstModeFirst (401/512:ℝ)*(thetaPowerMass 3 (25/32:ℝ) (401/512:ℝ)-(401/512:ℝ)*thetaPowerMass 2 (25/32:ℝ) (401/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0605.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (25/32:ℝ) (401/512:ℝ)
    (401/512:ℝ) (540043/625000000000:ℝ) (-12785070771648217/500000000000000000000:ℝ) (704685553528594139707/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_400
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1201).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_400 :
    (∫ x in (25/32:ℝ)..(401/512:ℝ), x^2*thetaFirstMode x) ≤ (1062998023440641/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (25/32:ℝ) (401/512:ℝ)
    (91538141/100000000000000:ℝ) (17281459/20000000000000:ℝ) (704685553528594139707/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_400 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1201).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_401 :
    (100828755796227/100000000000000000000000:ℝ) ≤ ∫ x in (401/512:ℝ)..(201/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-127805607741068420352915781/5000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (401/512:ℝ) (201/256:ℝ)-(47130745688792656218009/60175914297020011010560:ℝ)*thetaPowerMass 2 (401/512:ℝ) (201/256:ℝ)) ≤
      thetaFirstModeFirst (47130745688792656218009/60175914297020011010560:ℝ)*(thetaPowerMass 3 (401/512:ℝ) (201/256:ℝ)-(47130745688792656218009/60175914297020011010560:ℝ)*thetaPowerMass 2 (401/512:ℝ) (201/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0606.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (401/512:ℝ) (201/256:ℝ)
    (47130745688792656218009/60175914297020011010560:ℝ) (21593419/25000000000000:ℝ) (-127805607741068420352915781/5000000000000000000000000000000:ℝ) (335268886713492521407/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_401
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1205).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_401 :
    (∫ x in (401/512:ℝ)..(201/256:ℝ), x^2*thetaFirstMode x) ≤ (252079495869413/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (401/512:ℝ) (201/256:ℝ)
    (17281459/20000000000000:ℝ) (20386329/25000000000000:ℝ) (335268886713492521407/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_401 (thetaFirstMode_refined_node_1201).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_402 :
    (239050451645657/250000000000000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(403/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-4482396845767395801/195312500000000000000000:ℝ)*(thetaPowerMass 3 (201/256:ℝ) (403/512:ℝ)-(403/512:ℝ)*thetaPowerMass 2 (201/256:ℝ) (403/512:ℝ)) ≤
      thetaFirstModeFirst (403/512:ℝ)*(thetaPowerMass 3 (201/256:ℝ) (403/512:ℝ)-(403/512:ℝ)*thetaPowerMass 2 (201/256:ℝ) (403/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0608.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (201/256:ℝ) (403/512:ℝ)
    (403/512:ℝ) (19234701/25000000000000:ℝ) (-4482396845767395801/195312500000000000000000:ℝ) (79737063846885334561/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_402
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1207).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_402 :
    (∫ x in (201/256:ℝ)..(403/512:ℝ), x^2*thetaFirstMode x) ≤ (956218803731997/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (201/256:ℝ) (403/512:ℝ)
    (20386329/25000000000000:ℝ) (9617397/12500000000000:ℝ) (79737063846885334561/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_402 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1207).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_403 :
    (181312597696449/200000000000000000000000:ℝ) ≤ ∫ x in (403/512:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-573543693293688058820251719/25000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (403/512:ℝ) (101/128:ℝ)-(49289005090173420207207/62619246315825509148160:ℝ)*thetaPowerMass 2 (403/512:ℝ) (101/128:ℝ)) ≤
      thetaFirstModeFirst (49289005090173420207207/62619246315825509148160:ℝ)*(thetaPowerMass 3 (403/512:ℝ) (101/128:ℝ)-(49289005090173420207207/62619246315825509148160:ℝ)*thetaPowerMass 2 (403/512:ℝ) (101/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0609.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (403/512:ℝ) (101/128:ℝ)
    (49289005090173420207207/62619246315825509148160:ℝ) (1538183/2000000000000:ℝ) (-573543693293688058820251719/25000000000000000000000000000000:ℝ) (606702680145717299149/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_403
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1211).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_403 :
    (∫ x in (403/512:ℝ)..(101/128:ℝ), x^2*thetaFirstMode x) ≤ (226647744409339/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (403/512:ℝ) (101/128:ℝ)
    (9617397/12500000000000:ℝ) (72576421/100000000000000:ℝ) (606702680145717299149/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_403 (thetaFirstMode_refined_node_1207).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_404 :
    (214828360304721/250000000000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(405/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-205790335072329053403/10000000000000000000000000:ℝ)*(thetaPowerMass 3 (101/128:ℝ) (405/512:ℝ)-(405/512:ℝ)*thetaPowerMass 2 (101/128:ℝ) (405/512:ℝ)) ≤
      thetaFirstModeFirst (405/512:ℝ)*(thetaPowerMass 3 (101/128:ℝ) (405/512:ℝ)-(405/512:ℝ)*thetaPowerMass 2 (101/128:ℝ) (405/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0611.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (101/128:ℝ) (405/512:ℝ)
    (405/512:ℝ) (68444817/100000000000000:ℝ) (-205790335072329053403/10000000000000000000000000:ℝ) (28844958935722614037/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_404
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1213).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_404 :
    (∫ x in (101/128:ℝ)..(405/512:ℝ), x^2*thetaFirstMode x) ≤ (171865808045081/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (101/128:ℝ) (405/512:ℝ)
    (72576421/100000000000000:ℝ) (68445151/100000000000000:ℝ) (28844958935722614037/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_404 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1213).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_405 :
    (162861140991727/200000000000000000000000:ℝ) ≤ ∫ x in (405/512:ℝ)..(203/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-257146535571036027014468161/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (405/512:ℝ) (203/256:ℝ)-(10306934712842449320045/13029789587177640023552:ℝ)*thetaPowerMass 2 (405/512:ℝ) (203/256:ℝ)) ≤
      thetaFirstModeFirst (10306934712842449320045/13029789587177640023552:ℝ)*(thetaPowerMass 3 (405/512:ℝ) (203/256:ℝ)-(10306934712842449320045/13029789587177640023552:ℝ)*thetaPowerMass 2 (405/512:ℝ) (203/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0612.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (405/512:ℝ) (203/256:ℝ)
    (10306934712842449320045/13029789587177640023552:ℝ) (34209179/50000000000000:ℝ) (-257146535571036027014468161/12500000000000000000000000000000:ℝ) (548430824615958364363/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_405
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1217).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_405 :
    (∫ x in (405/512:ℝ)..(203/256:ℝ), x^2*thetaFirstMode x) ≤ (162866286279773/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (405/512:ℝ) (203/256:ℝ)
    (68445151/100000000000000:ℝ) (64533993/100000000000000:ℝ) (548430824615958364363/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_405 (thetaFirstMode_refined_node_1213).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_406 :
    (154297217459699/200000000000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(407/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-11522431429625069401/625000000000000000000000:ℝ)*(thetaPowerMass 3 (203/256:ℝ) (407/512:ℝ)-(407/512:ℝ)*thetaPowerMass 2 (203/256:ℝ) (407/512:ℝ)) ≤
      thetaFirstModeFirst (407/512:ℝ)*(thetaPowerMass 3 (203/256:ℝ) (407/512:ℝ)-(407/512:ℝ)*thetaPowerMass 2 (203/256:ℝ) (407/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0614.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (203/256:ℝ) (407/512:ℝ)
    (407/512:ℝ) (15207947/25000000000000:ℝ) (-11522431429625069401/625000000000000000000000:ℝ) (260622157493413149371/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_406
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1219).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_406 :
    (∫ x in (203/256:ℝ)..(407/512:ℝ), x^2*thetaFirstMode x) ≤ (771500388962707/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (203/256:ℝ) (407/512:ℝ)
    (64533993/100000000000000:ℝ) (60832087/100000000000000:ℝ) (260622157493413149371/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_406 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1219).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_407 :
    (146143643708563/200000000000000000000000:ℝ) ≤ ∫ x in (407/512:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x := by
  have hd : (-460732948638730350424083/25000000000000000000000000000:ℝ)*(thetaPowerMass 3 (407/512:ℝ) (51/64:ℝ)-(53870833123989848203743/67767622995901638300160:ℝ)*thetaPowerMass 2 (407/512:ℝ) (51/64:ℝ)) ≤
      thetaFirstModeFirst (53870833123989848203743/67767622995901638300160:ℝ)*(thetaPowerMass 3 (407/512:ℝ) (51/64:ℝ)-(53870833123989848203743/67767622995901638300160:ℝ)*thetaPowerMass 2 (407/512:ℝ) (51/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0615.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (407/512:ℝ) (51/64:ℝ)
    (53870833123989848203743/67767622995901638300160:ℝ) (60808201/100000000000000:ℝ) (-460732948638730350424083/25000000000000000000000000000:ℝ) (61911020223082356311/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_407
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1223).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_407 :
    (∫ x in (407/512:ℝ)..(51/64:ℝ), x^2*thetaFirstMode x) ≤ (730741841473443/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (407/512:ℝ) (51/64:ℝ)
    (60832087/100000000000000:ℝ) (2866453/5000000000000:ℝ) (61911020223082356311/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_407 (thetaFirstMode_refined_node_1219).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_408 :
    (345976086412431/500000000000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(409/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-51563754746382324809/3125000000000000000000000:ℝ)*(thetaPowerMass 3 (51/64:ℝ) (409/512:ℝ)-(409/512:ℝ)*thetaPowerMass 2 (51/64:ℝ) (409/512:ℝ)) ≤
      thetaFirstModeFirst (409/512:ℝ)*(thetaPowerMass 3 (51/64:ℝ) (409/512:ℝ)-(409/512:ℝ)*thetaPowerMass 2 (51/64:ℝ) (409/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0617.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (51/64:ℝ) (409/512:ℝ)
    (409/512:ℝ) (54014741/100000000000000:ℝ) (-51563754746382324809/3125000000000000000000000:ℝ) (235256328239877616081/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_408
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1225).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_408 :
    (∫ x in (51/64:ℝ)..(409/512:ℝ), x^2*thetaFirstMode x) ≤ (4324782977503/6250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (51/64:ℝ) (409/512:ℝ)
    (2866453/5000000000000:ℝ) (54015009/100000000000000:ℝ) (235256328239877616081/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_408 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1225).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_409 :
    (163765492638261/250000000000000000000000:ℝ) ≤ ∫ x in (409/512:ℝ)..(205/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-824724907872944656516977819/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (409/512:ℝ) (205/256:ℝ)-(56300658464195197911441/70477940425169641423360:ℝ)*thetaPowerMass 2 (409/512:ℝ) (205/256:ℝ)) ≤
      thetaFirstModeFirst (56300658464195197911441/70477940425169641423360:ℝ)*(thetaPowerMass 3 (409/512:ℝ) (205/256:ℝ)-(56300658464195197911441/70477940425169641423360:ℝ)*thetaPowerMass 2 (409/512:ℝ) (205/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0618.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (409/512:ℝ) (205/256:ℝ)
    (56300658464195197911441/70477940425169641423360:ℝ) (26996867/50000000000000:ℝ) (-824724907872944656516977819/50000000000000000000000000000000:ℝ) (446869821522720662701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_409
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1229).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_409 :
    (∫ x in (409/512:ℝ)..(205/256:ℝ), x^2*thetaFirstMode x) ≤ (655083638969961/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (409/512:ℝ) (205/256:ℝ)
    (54015009/100000000000000:ℝ) (50880481/100000000000000:ℝ) (446869821522720662701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_409 (thetaFirstMode_refined_node_1225).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_410 :
    (620001230901021/1000000000000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(411/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-3688527088288399797/250000000000000000000000:ℝ)*(thetaPowerMass 3 (205/256:ℝ) (411/512:ℝ)-(411/512:ℝ)*thetaPowerMass 2 (205/256:ℝ) (411/512:ℝ)) ≤
      thetaFirstModeFirst (411/512:ℝ)*(thetaPowerMass 3 (205/256:ℝ) (411/512:ℝ)-(411/512:ℝ)*thetaPowerMass 2 (205/256:ℝ) (411/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0620.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (205/256:ℝ) (411/512:ℝ)
    (411/512:ℝ) (5989527/12500000000000:ℝ) (-3688527088288399797/250000000000000000000000:ℝ) (424313339071429810603/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_410
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1231).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_410 :
    (∫ x in (205/256:ℝ)..(411/512:ℝ), x^2*thetaFirstMode x) ≤ (620013225336497/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (205/256:ℝ) (411/512:ℝ)
    (50880481/100000000000000:ℝ) (5989557/12500000000000:ℝ) (424313339071429810603/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_410 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1231).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_411 :
    (586653713360977/1000000000000000000000000:ℝ) ≤ ∫ x in (411/512:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x := by
  have hd : (-184360137887577686924503227/12500000000000000000000000000000:ℝ)*(thetaPowerMass 3 (411/512:ℝ) (103/128:ℝ)-(58827419272179392782959/73282635538862459829760:ℝ)*thetaPowerMass 2 (411/512:ℝ) (103/128:ℝ)) ≤
      thetaFirstModeFirst (58827419272179392782959/73282635538862459829760:ℝ)*(thetaPowerMass 3 (411/512:ℝ) (103/128:ℝ)-(58827419272179392782959/73282635538862459829760:ℝ)*thetaPowerMass 2 (411/512:ℝ) (103/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0621.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (411/512:ℝ) (103/128:ℝ)
    (58827419272179392782959/73282635538862459829760:ℝ) (11974381/25000000000000:ℝ) (-184360137887577686924503227/12500000000000000000000000000000:ℝ) (100699638499636611463/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_411
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1235).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_411 :
    (∫ x in (411/512:ℝ)..(103/128:ℝ), x^2*thetaFirstMode x) ≤ (23466943049549/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (411/512:ℝ) (103/128:ℝ)
    (5989557/12500000000000:ℝ) (5639291/12500000000000:ℝ) (100699638499636611463/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_411 (thetaFirstMode_refined_node_1231).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_412 :
    (277488197761983/500000000000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(413/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-164750325583458751739/12500000000000000000000000:ℝ)*(thetaPowerMass 3 (103/128:ℝ) (413/512:ℝ)-(413/512:ℝ)*thetaPowerMass 2 (103/128:ℝ) (413/512:ℝ)) ≤
      thetaFirstModeFirst (413/512:ℝ)*(thetaPowerMass 3 (103/128:ℝ) (413/512:ℝ)-(413/512:ℝ)*thetaPowerMass 2 (103/128:ℝ) (413/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0623.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (103/128:ℝ) (413/512:ℝ)
    (413/512:ℝ) (42465673/100000000000000:ℝ) (-164750325583458751739/12500000000000000000000000:ℝ) (382282366579116366383/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_412
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1237).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_412 :
    (∫ x in (103/128:ℝ)..(413/512:ℝ), x^2*thetaFirstMode x) ≤ (69373419841499/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (103/128:ℝ) (413/512:ℝ)
    (5639291/12500000000000:ℝ) (42465887/100000000000000:ℝ) (382282366579116366383/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_412 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1237).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_413 :
    (104972418740729/200000000000000000000000:ℝ) ≤ ∫ x in (413/512:ℝ)..(207/256:ℝ), x^2*thetaFirstMode x := by
  have hd : (-658763833043370852357635337/50000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (413/512:ℝ) (207/256:ℝ)-(61454482584883441479657/76184511352508643612160:ℝ)*thetaPowerMass 2 (413/512:ℝ) (207/256:ℝ)) ≤
      thetaFirstModeFirst (61454482584883441479657/76184511352508643612160:ℝ)*(thetaPowerMass 3 (413/512:ℝ) (207/256:ℝ)-(61454482584883441479657/76184511352508643612160:ℝ)*thetaPowerMass 2 (413/512:ℝ) (207/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0624.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (413/512:ℝ) (207/256:ℝ)
    (61454482584883441479657/76184511352508643612160:ℝ) (8489811/20000000000000:ℝ) (-658763833043370852357635337/50000000000000000000000000000000:ℝ) (362723226362548670817/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_413
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1241).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_413 :
    (∫ x in (413/512:ℝ)..(207/256:ℝ), x^2*thetaFirstMode x) ≤ (524880286609519/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (413/512:ℝ) (207/256:ℝ)
    (42465887/100000000000000:ℝ) (39963307/100000000000000:ℝ) (362723226362548670817/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_413 (thetaFirstMode_refined_node_1237).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_414 :
    (248135498457299/500000000000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(415/512:ℝ), x^2*thetaFirstMode x := by
  have hd : (-735158806386425209/62500000000000000000000:ℝ)*(thetaPowerMass 3 (207/256:ℝ) (415/512:ℝ)-(415/512:ℝ)*thetaPowerMass 2 (207/256:ℝ) (415/512:ℝ)) ≤
      thetaFirstModeFirst (415/512:ℝ)*(thetaPowerMass 3 (207/256:ℝ) (415/512:ℝ)-(415/512:ℝ)*thetaPowerMass 2 (207/256:ℝ) (415/512:ℝ)) := by
    exact mul_le_mul_of_nonpos_right (thetaTwelfth_derivative_node_0626.2) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (207/256:ℝ) (415/512:ℝ)
    (415/512:ℝ) (37598933/100000000000000:ℝ) (-735158806386425209/62500000000000000000000:ℝ) (172040548003624162409/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_414
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1243).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_414 :
    (∫ x in (207/256:ℝ)..(415/512:ℝ), x^2*thetaFirstMode x) ≤ (496281010505187/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (207/256:ℝ) (415/512:ℝ)
    (39963307/100000000000000:ℝ) (9399781/25000000000000:ℝ) (172040548003624162409/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_414 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1243).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_lower_2_415 :
    (469104384551079/1000000000000000000000000:ℝ) ≤ ∫ x in (415/512:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x := by
  have hd : (-23516574116722947004006353/2000000000000000000000000000000:ℝ)*(thetaPowerMass 3 (415/512:ℝ) (13/16:ℝ)-(12837063038463911715435/15837287983182423613952:ℝ)*thetaPowerMass 2 (415/512:ℝ) (13/16:ℝ)) ≤
      thetaFirstModeFirst (12837063038463911715435/15837287983182423613952:ℝ)*(thetaPowerMass 3 (415/512:ℝ) (13/16:ℝ)-(12837063038463911715435/15837287983182423613952:ℝ)*thetaPowerMass 2 (415/512:ℝ) (13/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0627.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 2 (415/512:ℝ) (13/16:ℝ)
    (12837063038463911715435/15837287983182423613952:ℝ) (18792087/50000000000000:ℝ) (-23516574116722947004006353/2000000000000000000000000000000:ℝ) (13052694597686269063/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_415
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1247).1 hd
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaTwelfth_cell_upper_2_415 :
    (∫ x in (415/512:ℝ)..(13/16:ℝ), x^2*thetaFirstMode x) ≤ (93824204398639/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (415/512:ℝ) (13/16:ℝ)
    (9399781/25000000000000:ℝ) (35366227/100000000000000:ℝ) (13052694597686269063/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_415 (thetaFirstMode_refined_node_1243).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Curvature12
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative18
import CarrySelfAdjointOperator.ThetaTwelfthSourceCertificateData.Derivative19

open MeasureTheory
namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
theorem thetaTwelfth_cell_lower_0_384 :
    (212412041309027/50000000000000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(385/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-618047811068838252726902079/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (3/4:ℝ) (385/512:ℝ)-(3/4:ℝ)*thetaPowerMass 0 (3/4:ℝ) (385/512:ℝ)) ≤
      thetaFirstModeFirst (3/4:ℝ)*(thetaPowerMass 1 (3/4:ℝ) (385/512:ℝ)-(3/4:ℝ)*thetaPowerMass 0 (3/4:ℝ) (385/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0580.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (3/4:ℝ) (385/512:ℝ)
    (3/4:ℝ) (111724691/50000000000000:ℝ) (-618047811068838252726902079/10000000000000000000000000000000:ℝ) (1512646200463755506153/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_384
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1152).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_384 :
    (∫ x in (3/4:ℝ)..(385/512:ℝ), x^0*thetaFirstMode x) ≤ (849669629969897/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (3/4:ℝ) (385/512:ℝ)
    (44690077/20000000000000:ℝ) (211676637/100000000000000:ℝ) (1512646200463755506153/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_384 (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1153).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_385 :
    (4023969320956831/1000000000000000000000000:ℝ) ≤ ∫ x in (385/512:ℝ)..(193/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-2938054038277696384625885119/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (385/512:ℝ) (193/256:ℝ)-(6534077305948613955765/8689317914228980285952:ℝ)*thetaPowerMass 0 (385/512:ℝ) (193/256:ℝ)) ≤
      thetaFirstModeFirst (6534077305948613955765/8689317914228980285952:ℝ)*(thetaPowerMass 1 (385/512:ℝ) (193/256:ℝ)-(6534077305948613955765/8689317914228980285952:ℝ)*thetaPowerMass 0 (385/512:ℝ) (193/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0582.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (385/512:ℝ) (193/256:ℝ)
    (6534077305948613955765/8689317914228980285952:ℝ) (10579809/5000000000000:ℝ) (-2938054038277696384625885119/50000000000000000000000000000000:ℝ) (1444535251539540222233/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_385
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1157).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_385 :
    (∫ x in (385/512:ℝ)..(193/256:ℝ), x^0*thetaFirstMode x) ≤ (2012035194932117/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (385/512:ℝ) (193/256:ℝ)
    (211676637/100000000000000:ℝ) (50120003/25000000000000:ℝ) (1444535251539540222233/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_385 (thetaFirstMode_refined_node_1153).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_386 :
    (952677647159711/250000000000000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(387/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-349338200679397703756588057/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (193/256:ℝ) (387/512:ℝ)-(193/256:ℝ)*thetaPowerMass 0 (193/256:ℝ) (387/512:ℝ)) ≤
      thetaFirstModeFirst (193/256:ℝ)*(thetaPowerMass 1 (193/256:ℝ) (387/512:ℝ)-(193/256:ℝ)*thetaPowerMass 0 (193/256:ℝ) (387/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0583.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (193/256:ℝ) (387/512:ℝ)
    (193/256:ℝ) (40095821/20000000000000:ℝ) (-349338200679397703756588057/6250000000000000000000000000000:ℝ) (43099680239324046491/31250000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_386
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1158).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_386 :
    (∫ x in (193/256:ℝ)..(387/512:ℝ), x^0*thetaFirstMode x) ≤ (476351133393647/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (193/256:ℝ) (387/512:ℝ)
    (50120003/25000000000000:ℝ) (189834523/100000000000000:ℝ) (43099680239324046491/31250000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_386 (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1159).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_387 :
    (1803987160881017/500000000000000000000000:ℝ) ≤ ∫ x in (387/512:ℝ)..(97/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-53118438712850890005802797/1000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (387/512:ℝ) (97/128:ℝ)-(34229931486855451316343/45285304621504058652160:ℝ)*thetaPowerMass 0 (387/512:ℝ) (97/128:ℝ)) ≤
      thetaFirstModeFirst (34229931486855451316343/45285304621504058652160:ℝ)*(thetaPowerMass 1 (387/512:ℝ) (97/128:ℝ)-(34229931486855451316343/45285304621504058652160:ℝ)*thetaPowerMass 0 (387/512:ℝ) (97/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0585.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (387/512:ℝ) (97/128:ℝ)
    (34229931486855451316343/45285304621504058652160:ℝ) (47440541/25000000000000:ℝ) (-53118438712850890005802797/1000000000000000000000000000000:ℝ) (1316511465572846673839/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_387
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1163).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_387 :
    (∫ x in (387/512:ℝ)..(97/128:ℝ), x^0*thetaFirstMode x) ≤ (1804033508082041/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (387/512:ℝ) (97/128:ℝ)
    (189834523/100000000000000:ℝ) (179715241/100000000000000:ℝ) (1316511465572846673839/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_387 (thetaFirstMode_refined_node_1159).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_388 :
    (136611081225781/40000000000000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(389/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1262622235062069163251677961/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (97/128:ℝ) (389/512:ℝ)-(97/128:ℝ)*thetaPowerMass 0 (97/128:ℝ) (389/512:ℝ)) ≤
      thetaFirstModeFirst (97/128:ℝ)*(thetaPowerMass 1 (97/128:ℝ) (389/512:ℝ)-(97/128:ℝ)*thetaPowerMass 0 (97/128:ℝ) (389/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0586.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (97/128:ℝ) (389/512:ℝ)
    (97/128:ℝ) (89857211/50000000000000:ℝ) (-1262622235062069163251677961/25000000000000000000000000000000:ℝ) (125640493830125248933/100000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_388
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1164).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_388 :
    (∫ x in (97/128:ℝ)..(389/512:ℝ), x^0*thetaFirstMode x) ≤ (3415367313723527/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (97/128:ℝ) (389/512:ℝ)
    (179715241/100000000000000:ℝ) (42524563/25000000000000:ℝ) (125640493830125248933/100000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_388 (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1165).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_389 :
    (3232167583977401/1000000000000000000000000:ℝ) ≤ ∫ x in (389/512:ℝ)..(195/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-299849097179838837701341767/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (389/512:ℝ) (195/256:ℝ)-(35855303234927171773041/47191752594083278773760:ℝ)*thetaPowerMass 0 (389/512:ℝ) (195/256:ℝ)) ≤
      thetaFirstModeFirst (35855303234927171773041/47191752594083278773760:ℝ)*(thetaPowerMass 1 (389/512:ℝ) (195/256:ℝ)-(35855303234927171773041/47191752594083278773760:ℝ)*thetaPowerMass 0 (389/512:ℝ) (195/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0588.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (389/512:ℝ) (195/256:ℝ)
    (35855303234927171773041/47191752594083278773760:ℝ) (17003323/10000000000000:ℝ) (-299849097179838837701341767/6250000000000000000000000000000:ℝ) (599388808956942227249/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_389
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1169).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_389 :
    (∫ x in (389/512:ℝ)..(195/256:ℝ), x^0*thetaFirstMode x) ≤ (3232252546598121/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (389/512:ℝ) (195/256:ℝ)
    (42524563/25000000000000:ℝ) (257537/160000000000:ℝ) (599388808956942227249/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_389 (thetaFirstMode_refined_node_1165).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_390 :
    (764550349591641/250000000000000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(391/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1823816786254770653470453/40000000000000000000000000000:ℝ)*(thetaPowerMass 1 (195/256:ℝ) (391/512:ℝ)-(195/256:ℝ)*thetaPowerMass 0 (195/256:ℝ) (391/512:ℝ)) ≤
      thetaFirstModeFirst (195/256:ℝ)*(thetaPowerMass 1 (195/256:ℝ) (391/512:ℝ)-(195/256:ℝ)*thetaPowerMass 0 (195/256:ℝ) (391/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0589.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (195/256:ℝ) (391/512:ℝ)
    (195/256:ℝ) (32191977/20000000000000:ℝ) (-1823816786254770653470453/40000000000000000000000000000:ℝ) (228707943376429807781/200000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_390
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1170).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_390 :
    (∫ x in (195/256:ℝ)..(391/512:ℝ), x^0*thetaFirstMode x) ≤ (3058284118191549/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (195/256:ℝ) (391/512:ℝ)
    (257537/160000000000:ℝ) (152280373/100000000000000:ℝ) (228707943376429807781/200000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_390 (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1171).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_391 :
    (1446481873470997/500000000000000000000000:ℝ) ≤ ∫ x in (391/512:ℝ)..(49/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-270582132373772827394153683/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (391/512:ℝ) (49/64:ℝ)-(37548920246270157404559/49168060985435061199360:ℝ)*thetaPowerMass 0 (391/512:ℝ) (49/64:ℝ)) ≤
      thetaFirstModeFirst (37548920246270157404559/49168060985435061199360:ℝ)*(thetaPowerMass 1 (391/512:ℝ) (49/64:ℝ)-(37548920246270157404559/49168060985435061199360:ℝ)*thetaPowerMass 0 (391/512:ℝ) (49/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0591.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (391/512:ℝ) (49/64:ℝ)
    (37548920246270157404559/49168060985435061199360:ℝ) (152221993/100000000000000:ℝ) (-270582132373772827394153683/6250000000000000000000000000000:ℝ) (545302077230300748787/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_391
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1175).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_391 :
    (∫ x in (391/512:ℝ)..(49/64:ℝ), x^0*thetaFirstMode x) ≤ (289304156499253/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (391/512:ℝ) (49/64:ℝ)
    (152280373/100000000000000:ℝ) (72018211/50000000000000:ℝ) (545302077230300748787/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_391 (thetaFirstMode_refined_node_1171).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_392 :
    (1368023103608361/500000000000000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(393/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1028173668489559087449442309/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (49/64:ℝ) (393/512:ℝ)-(49/64:ℝ)*thetaPowerMass 0 (49/64:ℝ) (393/512:ℝ)) ≤
      thetaFirstModeFirst (49/64:ℝ)*(thetaPowerMass 1 (49/64:ℝ) (393/512:ℝ)-(49/64:ℝ)*thetaPowerMass 0 (49/64:ℝ) (393/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0592.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (49/64:ℝ) (393/512:ℝ)
    (49/64:ℝ) (28807151/20000000000000:ℝ) (-1028173668489559087449442309/25000000000000000000000000000000:ℝ) (20797729653449226181/20000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_392
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1176).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_392 :
    (∫ x in (49/64:ℝ)..(393/512:ℝ), x^0*thetaFirstMode x) ≤ (684030475580973/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (49/64:ℝ) (393/512:ℝ)
    (72018211/50000000000000:ℝ) (5448343/4000000000000:ℝ) (20797729653449226181/20000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_392 (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1177).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_393 :
    (1293533915823959/500000000000000000000000:ℝ) ≤ ∫ x in (393/512:ℝ)..(197/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-243955966584715408959034827/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (393/512:ℝ) (197/256:ℝ)-(39313276758463040392257/51216412690723244700160:ℝ)*thetaPowerMass 0 (393/512:ℝ) (197/256:ℝ)) ≤
      thetaFirstModeFirst (39313276758463040392257/51216412690723244700160:ℝ)*(thetaPowerMass 1 (393/512:ℝ) (197/256:ℝ)-(39313276758463040392257/51216412690723244700160:ℝ)*thetaPowerMass 0 (393/512:ℝ) (197/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0594.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (393/512:ℝ) (197/256:ℝ)
    (39313276758463040392257/51216412690723244700160:ℝ) (68078103/50000000000000:ℝ) (-243955966584715408959034827/6250000000000000000000000000000:ℝ) (991304873654742215107/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_393
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1181).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_393 :
    (∫ x in (393/512:ℝ)..(197/256:ℝ), x^0*thetaFirstMode x) ≤ (517427799870087/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (393/512:ℝ) (197/256:ℝ)
    (5448343/4000000000000:ℝ) (32194371/25000000000000:ℝ) (991304873654742215107/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_393 (thetaFirstMode_refined_node_1177).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_394 :
    (1222826856532207/500000000000000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(395/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-231646744760667274867987257/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (197/256:ℝ) (395/512:ℝ)-(197/256:ℝ)*thetaPowerMass 0 (197/256:ℝ) (395/512:ℝ)) ≤
      thetaFirstModeFirst (197/256:ℝ)*(thetaPowerMass 1 (197/256:ℝ) (395/512:ℝ)-(197/256:ℝ)*thetaPowerMass 0 (197/256:ℝ) (395/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0595.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (197/256:ℝ) (395/512:ℝ)
    (197/256:ℝ) (128776883/100000000000000:ℝ) (-231646744760667274867987257/6250000000000000000000000000000:ℝ) (944780016879046322359/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_394
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1182).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_394 :
    (∫ x in (197/256:ℝ)..(395/512:ℝ), x^0*thetaFirstMode x) ≤ (489144588875423/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (197/256:ℝ) (395/512:ℝ)
    (32194371/25000000000000:ℝ) (121724613/100000000000000:ℝ) (944780016879046322359/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_394 (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1183).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_395 :
    (462290868584149/200000000000000000000000:ℝ) ≤ ∫ x in (395/512:ℝ)..(99/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-87901588057022216815845429/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (395/512:ℝ) (99/128:ℝ)-(8230188948417592711155/10667809430360898647552:ℝ)*thetaPowerMass 0 (395/512:ℝ) (99/128:ℝ)) ≤
      thetaFirstModeFirst (8230188948417592711155/10667809430360898647552:ℝ)*(thetaPowerMass 1 (395/512:ℝ) (99/128:ℝ)-(8230188948417592711155/10667809430360898647552:ℝ)*thetaPowerMass 0 (395/512:ℝ) (99/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0597.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (395/512:ℝ) (99/128:ℝ)
    (8230188948417592711155/10667809430360898647552:ℝ) (60838837/50000000000000:ℝ) (-87901588057022216815845429/2500000000000000000000000000000:ℝ) (900235061987027897989/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_395
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1187).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_395 :
    (∫ x in (395/512:ℝ)..(99/128:ℝ), x^0*thetaFirstMode x) ≤ (2311519419884541/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (395/512:ℝ) (99/128:ℝ)
    (121724613/100000000000000:ℝ) (115032211/100000000000000:ℝ) (900235061987027897989/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_395 (thetaFirstMode_refined_node_1183).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_396 :
    (1092062956341597/500000000000000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(397/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1668581238067534158733256773/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (99/128:ℝ) (397/512:ℝ)-(99/128:ℝ)*thetaPowerMass 0 (99/128:ℝ) (397/512:ℝ)) ≤
      thetaFirstModeFirst (99/128:ℝ)*(thetaPowerMass 1 (99/128:ℝ) (397/512:ℝ)-(99/128:ℝ)*thetaPowerMass 0 (99/128:ℝ) (397/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0598.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (99/128:ℝ) (397/512:ℝ)
    (99/128:ℝ) (11503167/10000000000000:ℝ) (-1668581238067534158733256773/50000000000000000000000000000000:ℝ) (428797801111739030787/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_396
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1188).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_396 :
    (∫ x in (99/128:ℝ)..(397/512:ℝ), x^0*thetaFirstMode x) ≤ (2184189165429881/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (99/128:ℝ) (397/512:ℝ)
    (115032211/100000000000000:ℝ) (27170821/25000000000000:ℝ) (428797801111739030787/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_396 (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1189).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_397 :
    (128959248759821/62500000000000000000000:ℝ) ≤ ∫ x in (397/512:ℝ)..(199/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-197775250872396195097220583/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (397/512:ℝ) (199/256:ℝ)-(43064575909141158188793/55538261523062839068160:ℝ)*thetaPowerMass 0 (397/512:ℝ) (199/256:ℝ)) ≤
      thetaFirstModeFirst (43064575909141158188793/55538261523062839068160:ℝ)*(thetaPowerMass 1 (397/512:ℝ) (199/256:ℝ)-(43064575909141158188793/55538261523062839068160:ℝ)*thetaPowerMass 0 (397/512:ℝ) (199/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0600.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (397/512:ℝ) (199/256:ℝ)
    (43064575909141158188793/55538261523062839068160:ℝ) (108641251/100000000000000:ℝ) (-197775250872396195097220583/6250000000000000000000000000000:ℝ) (816789565727244178923/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_397
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1193).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_397 :
    (∫ x in (397/512:ℝ)..(199/256:ℝ), x^0*thetaFirstMode x) ≤ (1031703700771243/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (397/512:ℝ) (199/256:ℝ)
    (27170821/25000000000000:ℝ) (25665391/25000000000000:ℝ) (816789565727244178923/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_397 (thetaFirstMode_refined_node_1189).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_398 :
    (1948805509027319/1000000000000000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(399/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-187627697452966701727544563/6250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (199/256:ℝ) (399/512:ℝ)-(199/256:ℝ)*thetaPowerMass 0 (199/256:ℝ) (399/512:ℝ)) ≤
      thetaFirstModeFirst (199/256:ℝ)*(thetaPowerMass 1 (199/256:ℝ) (399/512:ℝ)-(199/256:ℝ)*thetaPowerMass 0 (199/256:ℝ) (399/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0601.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (199/256:ℝ) (399/512:ℝ)
    (199/256:ℝ) (102661077/100000000000000:ℝ) (-187627697452966701727544563/6250000000000000000000000000000:ℝ) (194436798485739133227/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_398
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1194).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_398 :
    (∫ x in (199/256:ℝ)..(399/512:ℝ), x^0*thetaFirstMode x) ≤ (1948863253565417/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (199/256:ℝ) (399/512:ℝ)
    (25665391/25000000000000:ℝ) (96951481/100000000000000:ℝ) (194436798485739133227/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_398 (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1195).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_399 :
    (460051259258739/250000000000000000000000:ℝ) ≤ ∫ x in (399/512:ℝ)..(25/32:ℝ), x^0*thetaFirstMode x := by
  have hd : (-284533901394894733744266069/10000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (399/512:ℝ) (25/32:ℝ)-(45056903762744623817991/57816411855179361794560:ℝ)*thetaPowerMass 0 (399/512:ℝ) (25/32:ℝ)) ≤
      thetaFirstModeFirst (45056903762744623817991/57816411855179361794560:ℝ)*(thetaPowerMass 1 (399/512:ℝ) (25/32:ℝ)-(45056903762744623817991/57816411855179361794560:ℝ)*thetaPowerMass 0 (399/512:ℝ) (25/32:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0603.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (399/512:ℝ) (25/32:ℝ)
    (45056903762744623817991/57816411855179361794560:ℝ) (96913873/100000000000000:ℝ) (-284533901394894733744266069/10000000000000000000000000000000:ℝ) (370200483421154245411/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_399
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1199).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_399 :
    (∫ x in (399/512:ℝ)..(25/32:ℝ), x^0*thetaFirstMode x) ≤ (920129631710313/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (399/512:ℝ) (25/32:ℝ)
    (96951481/100000000000000:ℝ) (91538141/100000000000000:ℝ) (370200483421154245411/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_399 (thetaFirstMode_refined_node_1195).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_400 :
    (1737258208846167/1000000000000000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(401/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-84316365055329730026288149/3125000000000000000000000000000:ℝ)*(thetaPowerMass 1 (25/32:ℝ) (401/512:ℝ)-(25/32:ℝ)*thetaPowerMass 0 (25/32:ℝ) (401/512:ℝ)) ≤
      thetaFirstModeFirst (25/32:ℝ)*(thetaPowerMass 1 (25/32:ℝ) (401/512:ℝ)-(25/32:ℝ)*thetaPowerMass 0 (25/32:ℝ) (401/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0604.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (25/32:ℝ) (401/512:ℝ)
    (25/32:ℝ) (11442213/12500000000000:ℝ) (-84316365055329730026288149/3125000000000000000000000000000:ℝ) (704685553528594139707/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_400
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1200).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_400 :
    (∫ x in (25/32:ℝ)..(401/512:ℝ), x^0*thetaFirstMode x) ≤ (217163859007687/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (25/32:ℝ) (401/512:ℝ)
    (91538141/100000000000000:ℝ) (17281459/20000000000000:ℝ) (704685553528594139707/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_400 (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1201).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_401 :
    (1639696449114789/1000000000000000000000000:ℝ) ≤ ∫ x in (401/512:ℝ)..(201/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-127805607741068420352915781/5000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (401/512:ℝ) (201/256:ℝ)-(47130745688792656218009/60175914297020011010560:ℝ)*thetaPowerMass 0 (401/512:ℝ) (201/256:ℝ)) ≤
      thetaFirstModeFirst (47130745688792656218009/60175914297020011010560:ℝ)*(thetaPowerMass 1 (401/512:ℝ) (201/256:ℝ)-(47130745688792656218009/60175914297020011010560:ℝ)*thetaPowerMass 0 (401/512:ℝ) (201/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0606.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (401/512:ℝ) (201/256:ℝ)
    (47130745688792656218009/60175914297020011010560:ℝ) (21593419/25000000000000:ℝ) (-127805607741068420352915781/5000000000000000000000000000000:ℝ) (335268886713492521407/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_401
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1205).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_401 :
    (∫ x in (401/512:ℝ)..(201/256:ℝ), x^0*thetaFirstMode x) ≤ (204968236519149/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (401/512:ℝ) (201/256:ℝ)
    (17281459/20000000000000:ℝ) (20386329/25000000000000:ℝ) (335268886713492521407/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_401 (thetaFirstMode_refined_node_1201).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_402 :
    (1547256058502061/1000000000000000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(403/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-15142202704754247770000391/625000000000000000000000000000:ℝ)*(thetaPowerMass 1 (201/256:ℝ) (403/512:ℝ)-(201/256:ℝ)*thetaPowerMass 0 (201/256:ℝ) (403/512:ℝ)) ≤
      thetaFirstModeFirst (201/256:ℝ)*(thetaPowerMass 1 (201/256:ℝ) (403/512:ℝ)-(201/256:ℝ)*thetaPowerMass 0 (201/256:ℝ) (403/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0607.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (201/256:ℝ) (403/512:ℝ)
    (201/256:ℝ) (81544923/100000000000000:ℝ) (-15142202704754247770000391/625000000000000000000000000000:ℝ) (79737063846885334561/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_402
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1206).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_402 :
    (∫ x in (201/256:ℝ)..(403/512:ℝ), x^0*thetaFirstMode x) ≤ (773652029453499/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (201/256:ℝ) (403/512:ℝ)
    (20386329/25000000000000:ℝ) (9617397/12500000000000:ℝ) (79737063846885334561/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_402 (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1207).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_403 :
    (1459691527234671/1000000000000000000000000:ℝ) ≤ ∫ x in (403/512:ℝ)..(101/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-573543693293688058820251719/25000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (403/512:ℝ) (101/128:ℝ)-(49289005090173420207207/62619246315825509148160:ℝ)*thetaPowerMass 0 (403/512:ℝ) (101/128:ℝ)) ≤
      thetaFirstModeFirst (49289005090173420207207/62619246315825509148160:ℝ)*(thetaPowerMass 1 (403/512:ℝ) (101/128:ℝ)-(49289005090173420207207/62619246315825509148160:ℝ)*thetaPowerMass 0 (403/512:ℝ) (101/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0609.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (403/512:ℝ) (101/128:ℝ)
    (49289005090173420207207/62619246315825509148160:ℝ) (1538183/2000000000000:ℝ) (-573543693293688058820251719/25000000000000000000000000000000:ℝ) (606702680145717299149/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_403
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1211).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_403 :
    (∫ x in (403/512:ℝ)..(101/128:ℝ), x^0*thetaFirstMode x) ≤ (729868280675863/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (403/512:ℝ) (101/128:ℝ)
    (9617397/12500000000000:ℝ) (72576421/100000000000000:ℝ) (606702680145717299149/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_403 (thetaFirstMode_refined_node_1207).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_404 :
    (172095238237807/125000000000000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(405/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-1086739292051088542535118539/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (101/128:ℝ) (405/512:ℝ)-(101/128:ℝ)*thetaPowerMass 0 (101/128:ℝ) (405/512:ℝ)) ≤
      thetaFirstModeFirst (101/128:ℝ)*(thetaPowerMass 1 (101/128:ℝ) (405/512:ℝ)-(101/128:ℝ)*thetaPowerMass 0 (101/128:ℝ) (405/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0610.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (101/128:ℝ) (405/512:ℝ)
    (101/128:ℝ) (72576069/100000000000000:ℝ) (-1086739292051088542535118539/50000000000000000000000000000000:ℝ) (28844958935722614037/50000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_404
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1212).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_404 :
    (∫ x in (101/128:ℝ)..(405/512:ℝ), x^0*thetaFirstMode x) ≤ (55072224116409/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (101/128:ℝ) (405/512:ℝ)
    (72576421/100000000000000:ℝ) (68445151/100000000000000:ℝ) (28844958935722614037/50000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_404 (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1213).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_405 :
    (649121478129959/500000000000000000000000:ℝ) ≤ ∫ x in (405/512:ℝ)..(203/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-257146535571036027014468161/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (405/512:ℝ) (203/256:ℝ)-(10306934712842449320045/13029789587177640023552:ℝ)*thetaPowerMass 0 (405/512:ℝ) (203/256:ℝ)) ≤
      thetaFirstModeFirst (10306934712842449320045/13029789587177640023552:ℝ)*(thetaPowerMass 1 (405/512:ℝ) (203/256:ℝ)-(10306934712842449320045/13029789587177640023552:ℝ)*thetaPowerMass 0 (405/512:ℝ) (203/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0612.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (405/512:ℝ) (203/256:ℝ)
    (10306934712842449320045/13029789587177640023552:ℝ) (34209179/50000000000000:ℝ) (-257146535571036027014468161/12500000000000000000000000000000:ℝ) (548430824615958364363/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_405
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1217).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_405 :
    (∫ x in (405/512:ℝ)..(203/256:ℝ), x^0*thetaFirstMode x) ≤ (1298283942453281/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (405/512:ℝ) (203/256:ℝ)
    (68445151/100000000000000:ℝ) (64533993/100000000000000:ℝ) (548430824615958364363/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_405 (thetaFirstMode_refined_node_1213).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_406 :
    (611957370456377/500000000000000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(407/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-974019628195177236729921279/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (203/256:ℝ) (407/512:ℝ)-(203/256:ℝ)*thetaPowerMass 0 (203/256:ℝ) (407/512:ℝ)) ≤
      thetaFirstModeFirst (203/256:ℝ)*(thetaPowerMass 1 (203/256:ℝ) (407/512:ℝ)-(203/256:ℝ)*thetaPowerMass 0 (203/256:ℝ) (407/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0613.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (203/256:ℝ) (407/512:ℝ)
    (203/256:ℝ) (64533677/100000000000000:ℝ) (-974019628195177236729921279/50000000000000000000000000000000:ℝ) (260622157493413149371/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_406
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1218).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_406 :
    (∫ x in (203/256:ℝ)..(407/512:ℝ), x^0*thetaFirstMode x) ≤ (611977246967521/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (203/256:ℝ) (407/512:ℝ)
    (64533993/100000000000000:ℝ) (60832087/100000000000000:ℝ) (260622157493413149371/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_406 (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1219).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_407 :
    (1153572669295319/1000000000000000000000000:ℝ) ≤ ∫ x in (407/512:ℝ)..(51/64:ℝ), x^0*thetaFirstMode x := by
  have hd : (-460732948638730350424083/25000000000000000000000000000:ℝ)*(thetaPowerMass 1 (407/512:ℝ) (51/64:ℝ)-(53870833123989848203743/67767622995901638300160:ℝ)*thetaPowerMass 0 (407/512:ℝ) (51/64:ℝ)) ≤
      thetaFirstModeFirst (53870833123989848203743/67767622995901638300160:ℝ)*(thetaPowerMass 1 (407/512:ℝ) (51/64:ℝ)-(53870833123989848203743/67767622995901638300160:ℝ)*thetaPowerMass 0 (407/512:ℝ) (51/64:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0615.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (407/512:ℝ) (51/64:ℝ)
    (53870833123989848203743/67767622995901638300160:ℝ) (60808201/100000000000000:ℝ) (-460732948638730350424083/25000000000000000000000000000:ℝ) (61911020223082356311/125000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_407
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1223).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_407 :
    (∫ x in (407/512:ℝ)..(51/64:ℝ), x^0*thetaFirstMode x) ≤ (1153609935807869/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (407/512:ℝ) (51/64:ℝ)
    (60832087/100000000000000:ℝ) (2866453/5000000000000:ℝ) (61911020223082356311/125000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_407 (thetaFirstMode_refined_node_1219).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_408 :
    (1087016161927893/1000000000000000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(409/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-43608675798027496137440357/2500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (51/64:ℝ) (409/512:ℝ)-(51/64:ℝ)*thetaPowerMass 0 (51/64:ℝ) (409/512:ℝ)) ≤
      thetaFirstModeFirst (51/64:ℝ)*(thetaPowerMass 1 (51/64:ℝ) (409/512:ℝ)-(51/64:ℝ)*thetaPowerMass 0 (51/64:ℝ) (409/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0616.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (51/64:ℝ) (409/512:ℝ)
    (51/64:ℝ) (57328777/100000000000000:ℝ) (-43608675798027496137440357/2500000000000000000000000000000:ℝ) (235256328239877616081/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_408
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1224).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_408 :
    (∫ x in (51/64:ℝ)..(409/512:ℝ), x^0*thetaFirstMode x) ≤ (543526145561189/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (51/64:ℝ) (409/512:ℝ)
    (2866453/5000000000000:ℝ) (54015009/100000000000000:ℝ) (235256328239877616081/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_408 (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1225).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_409 :
    (20481174322193/20000000000000000000000:ℝ) ≤ ∫ x in (409/512:ℝ)..(205/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-824724907872944656516977819/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (409/512:ℝ) (205/256:ℝ)-(56300658464195197911441/70477940425169641423360:ℝ)*thetaPowerMass 0 (409/512:ℝ) (205/256:ℝ)) ≤
      thetaFirstModeFirst (56300658464195197911441/70477940425169641423360:ℝ)*(thetaPowerMass 1 (409/512:ℝ) (205/256:ℝ)-(56300658464195197911441/70477940425169641423360:ℝ)*thetaPowerMass 0 (409/512:ℝ) (205/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0618.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (409/512:ℝ) (205/256:ℝ)
    (56300658464195197911441/70477940425169641423360:ℝ) (26996867/50000000000000:ℝ) (-824724907872944656516977819/50000000000000000000000000000000:ℝ) (446869821522720662701/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_409
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1229).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_409 :
    (∫ x in (409/512:ℝ)..(205/256:ℝ), x^0*thetaFirstMode x) ≤ (256023141557363/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (409/512:ℝ) (205/256:ℝ)
    (54015009/100000000000000:ℝ) (50880481/100000000000000:ℝ) (446869821522720662701/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_409 (thetaFirstMode_refined_node_1225).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_410 :
    (120564698511313/125000000000000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(411/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-780239157933164564318631603/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (205/256:ℝ) (411/512:ℝ)-(205/256:ℝ)*thetaPowerMass 0 (205/256:ℝ) (411/512:ℝ)) ≤
      thetaFirstModeFirst (205/256:ℝ)*(thetaPowerMass 1 (205/256:ℝ) (411/512:ℝ)-(205/256:ℝ)*thetaPowerMass 0 (205/256:ℝ) (411/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0619.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (205/256:ℝ) (411/512:ℝ)
    (205/256:ℝ) (12720057/25000000000000:ℝ) (-780239157933164564318631603/50000000000000000000000000000000:ℝ) (424313339071429810603/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_410
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1230).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_410 :
    (∫ x in (205/256:ℝ)..(411/512:ℝ), x^0*thetaFirstMode x) ≤ (964550389496367/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (205/256:ℝ) (411/512:ℝ)
    (50880481/100000000000000:ℝ) (5989557/12500000000000:ℝ) (424313339071429810603/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_410 (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1231).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_411 :
    (227055732764373/250000000000000000000000:ℝ) ≤ ∫ x in (411/512:ℝ)..(103/128:ℝ), x^0*thetaFirstMode x := by
  have hd : (-184360137887577686924503227/12500000000000000000000000000000:ℝ)*(thetaPowerMass 1 (411/512:ℝ) (103/128:ℝ)-(58827419272179392782959/73282635538862459829760:ℝ)*thetaPowerMass 0 (411/512:ℝ) (103/128:ℝ)) ≤
      thetaFirstModeFirst (58827419272179392782959/73282635538862459829760:ℝ)*(thetaPowerMass 1 (411/512:ℝ) (103/128:ℝ)-(58827419272179392782959/73282635538862459829760:ℝ)*thetaPowerMass 0 (411/512:ℝ) (103/128:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0621.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (411/512:ℝ) (103/128:ℝ)
    (58827419272179392782959/73282635538862459829760:ℝ) (11974381/25000000000000:ℝ) (-184360137887577686924503227/12500000000000000000000000000000:ℝ) (100699638499636611463/250000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_411
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1235).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_411 :
    (∫ x in (411/512:ℝ)..(103/128:ℝ), x^0*thetaFirstMode x) ≤ (454126829871213/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (411/512:ℝ) (103/128:ℝ)
    (5989557/12500000000000:ℝ) (5639291/12500000000000:ℝ) (100699638499636611463/250000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_411 (thetaFirstMode_refined_node_1231).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_412 :
    (855008418197431/1000000000000000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(413/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-3486655607294994757452767/250000000000000000000000000000:ℝ)*(thetaPowerMass 1 (103/128:ℝ) (413/512:ℝ)-(103/128:ℝ)*thetaPowerMass 0 (103/128:ℝ) (413/512:ℝ)) ≤
      thetaFirstModeFirst (103/128:ℝ)*(thetaPowerMass 1 (103/128:ℝ) (413/512:ℝ)-(103/128:ℝ)*thetaPowerMass 0 (103/128:ℝ) (413/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0622.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (103/128:ℝ) (413/512:ℝ)
    (103/128:ℝ) (45114101/100000000000000:ℝ) (-3486655607294994757452767/250000000000000000000000000000:ℝ) (382282366579116366383/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_412
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1236).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_412 :
    (∫ x in (103/128:ℝ)..(413/512:ℝ), x^0*thetaFirstMode x) ≤ (42751909248873/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (103/128:ℝ) (413/512:ℝ)
    (5639291/12500000000000:ℝ) (42465887/100000000000000:ℝ) (382282366579116366383/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_412 (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1237).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_413 :
    (100589939477447/125000000000000000000000:ℝ) ≤ ∫ x in (413/512:ℝ)..(207/256:ℝ), x^0*thetaFirstMode x := by
  have hd : (-658763833043370852357635337/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (413/512:ℝ) (207/256:ℝ)-(61454482584883441479657/76184511352508643612160:ℝ)*thetaPowerMass 0 (413/512:ℝ) (207/256:ℝ)) ≤
      thetaFirstModeFirst (61454482584883441479657/76184511352508643612160:ℝ)*(thetaPowerMass 1 (413/512:ℝ) (207/256:ℝ)-(61454482584883441479657/76184511352508643612160:ℝ)*thetaPowerMass 0 (413/512:ℝ) (207/256:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0624.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (413/512:ℝ) (207/256:ℝ)
    (61454482584883441479657/76184511352508643612160:ℝ) (8489811/20000000000000:ℝ) (-658763833043370852357635337/50000000000000000000000000000000:ℝ) (362723226362548670817/1000000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_413
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1241).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_413 :
    (∫ x in (413/512:ℝ)..(207/256:ℝ), x^0*thetaFirstMode x) ≤ (160949477887377/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (413/512:ℝ) (207/256:ℝ)
    (42465887/100000000000000:ℝ) (39963307/100000000000000:ℝ) (362723226362548670817/1000000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_413 (thetaFirstMode_refined_node_1237).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_414 :
    (757205000365969/1000000000000000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(415/512:ℝ), x^0*thetaFirstMode x := by
  have hd : (-622635042916985816620705343/50000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (207/256:ℝ) (415/512:ℝ)-(207/256:ℝ)*thetaPowerMass 0 (207/256:ℝ) (415/512:ℝ)) ≤
      thetaFirstModeFirst (207/256:ℝ)*(thetaPowerMass 1 (207/256:ℝ) (415/512:ℝ)-(207/256:ℝ)*thetaPowerMass 0 (207/256:ℝ) (415/512:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0625.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (207/256:ℝ) (415/512:ℝ)
    (207/256:ℝ) (1248847/3125000000000:ℝ) (-622635042916985816620705343/50000000000000000000000000000000:ℝ) (172040548003624162409/500000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_414
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1242).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_414 :
    (∫ x in (207/256:ℝ)..(415/512:ℝ), x^0*thetaFirstMode x) ≤ (378615990786451/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (207/256:ℝ) (415/512:ℝ)
    (39963307/100000000000000:ℝ) (9399781/25000000000000:ℝ) (172040548003624162409/500000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_414 (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1243).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_lower_0_415 :
    (712324405675709/1000000000000000000000000:ℝ) ≤ ∫ x in (415/512:ℝ)..(13/16:ℝ), x^0*thetaFirstMode x := by
  have hd : (-23516574116722947004006353/2000000000000000000000000000000:ℝ)*(thetaPowerMass 1 (415/512:ℝ) (13/16:ℝ)-(12837063038463911715435/15837287983182423613952:ℝ)*thetaPowerMass 0 (415/512:ℝ) (13/16:ℝ)) ≤
      thetaFirstModeFirst (12837063038463911715435/15837287983182423613952:ℝ)*(thetaPowerMass 1 (415/512:ℝ) (13/16:ℝ)-(12837063038463911715435/15837287983182423613952:ℝ)*thetaPowerMass 0 (415/512:ℝ) (13/16:ℝ)) := by
    exact mul_le_mul_of_nonneg_right (thetaTwelfth_derivative_node_0627.1) (by norm_num [thetaPowerMass])
  have h := thetaFirstMode_weighted_curvature_node_lower 0 (415/512:ℝ) (13/16:ℝ)
    (12837063038463911715435/15837287983182423613952:ℝ) (18792087/50000000000000:ℝ) (-23516574116722947004006353/2000000000000000000000000000000:ℝ) (13052694597686269063/40000000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaTwelfth_cell_curvature_415
    (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1247).1 hd
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

theorem thetaTwelfth_cell_upper_0_415 :
    (∫ x in (415/512:ℝ)..(13/16:ℝ), x^0*thetaFirstMode x) ≤ (89043706421717/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 0 (415/512:ℝ) (13/16:ℝ)
    (9399781/25000000000000:ℝ) (35366227/100000000000000:ℝ) (13052694597686269063/40000000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaTwelfth_cell_curvature_415 (thetaFirstMode_refined_node_1243).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h
  norm_num only [pow_zero, one_mul]
  linarith only [h]

end CarrySelfAdjointOperator

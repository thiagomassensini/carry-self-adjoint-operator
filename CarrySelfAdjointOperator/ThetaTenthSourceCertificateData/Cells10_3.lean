import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature3

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^10*thetaFirstMode x) ≤ (137684878496863/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/8:ℝ) (97/256:ℝ)
    (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_096 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^10*thetaFirstMode x) ≤ (22676842167387/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (97/256:ℝ) (49/128:ℝ)
    (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_097 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^10*thetaFirstMode x) ≤ (763789554528889/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (49/128:ℝ) (99/256:ℝ)
    (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_098 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^10*thetaFirstMode x) ≤ (401381691653227/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (99/256:ℝ) (25/64:ℝ)
    (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_099 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^10*thetaFirstMode x) ≤ (842522708503349/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (25/64:ℝ) (101/256:ℝ)
    (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ) (356296586964953583/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_100 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^10*thetaFirstMode x) ≤ (883004993200339/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (101/256:ℝ) (51/128:ℝ)
    (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ) (34420794807094063/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_101 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^10*thetaFirstMode x) ≤ (4620715058007/5000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (51/128:ℝ) (103/256:ℝ)
    (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_102 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^10*thetaFirstMode x) ≤ (965864997947829/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (103/256:ℝ) (13/32:ℝ)
    (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_103 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^10*thetaFirstMode x) ≤ (504047411626837/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/32:ℝ) (105/256:ℝ)
    (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (30951371593757961/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_104 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^10*thetaFirstMode x) ≤ (2101504398911/2000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (105/256:ℝ) (53/128:ℝ)
    (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_105 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^10*thetaFirstMode x) ≤ (27343822758731/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (53/128:ℝ) (107/256:ℝ)
    (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (143847313866595999/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_106 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^10*thetaFirstMode x) ≤ (1137009068512203/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (107/256:ℝ) (27/64:ℝ)
    (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ) (55435413091796449/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_107 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^10*thetaFirstMode x) ≤ (295107349306139/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/64:ℝ) (109/256:ℝ)
    (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_108 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^10*thetaFirstMode x) ≤ (122391953617897/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (109/256:ℝ) (55/128:ℝ)
    (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_109 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^10*thetaFirstMode x) ≤ (633691184826543/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (55/128:ℝ) (111/256:ℝ)
    (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_110 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^10*thetaFirstMode x) ≤ (1310718375607887/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (111/256:ℝ) (7/16:ℝ)
    (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_111 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^10*thetaFirstMode x) ≤ (169228249249483/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/16:ℝ) (113/256:ℝ)
    (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_112 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^10*thetaFirstMode x) ≤ (174575251557773/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (113/256:ℝ) (57/128:ℝ)
    (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_113 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^10*thetaFirstMode x) ≤ (1438941967412617/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (57/128:ℝ) (115/256:ℝ)
    (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_114 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^10*thetaFirstMode x) ≤ (740370279186579/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (115/256:ℝ) (29/64:ℝ)
    (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_115 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^10*thetaFirstMode x) ≤ (760946036707071/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (29/64:ℝ) (117/256:ℝ)
    (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ) (97026004163419267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_116 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^10*thetaFirstMode x) ≤ (781145411613531/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (117/256:ℝ) (59/128:ℝ)
    (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_117 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^10*thetaFirstMode x) ≤ (1601831581514951/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (59/128:ℝ) (119/256:ℝ)
    (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_118 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^10*thetaFirstMode x) ≤ (1640410029261277/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (119/256:ℝ) (15/32:ℝ)
    (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ) (42699420868835591/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_119 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^10*thetaFirstMode x) ≤ (83896160008059/50000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/32:ℝ) (121/256:ℝ)
    (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ) (3270357328822397/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_120 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^10*thetaFirstMode x) ≤ (428567481209131/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (121/256:ℝ) (61/128:ℝ)
    (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_121 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^10*thetaFirstMode x) ≤ (69974050847363/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (61/128:ℝ) (123/256:ℝ)
    (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_122 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^10*thetaFirstMode x) ≤ (356614195644547/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (123/256:ℝ) (31/64:ℝ)
    (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ) (35761737420459491/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_123 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^10*thetaFirstMode x) ≤ (907667940488951/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (31/64:ℝ) (125/256:ℝ)
    (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ) (68333801879586489/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_124 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^10*thetaFirstMode x) ≤ (923028161906193/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (125/256:ℝ) (63/128:ℝ)
    (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_125 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^10*thetaFirstMode x) ≤ (937573279916027/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (63/128:ℝ) (127/256:ℝ)
    (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_126 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^10*thetaFirstMode x) ≤ (951262566945101/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (127/256:ℝ) (1/2:ℝ)
    (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_127 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

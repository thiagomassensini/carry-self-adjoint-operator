import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature3

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_2_096 :
    (422155404012218017/250000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (3/8:ℝ) (97/256:ℝ)
    (10783875/28607488:ℝ) (152099143523/50000000000000:ℝ) (814502165006677/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_096
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0578).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^2*thetaFirstMode x) ≤ (844320076342534009/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (3/8:ℝ) (97/256:ℝ)
    (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_096 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_097 :
    (1639054113929841303/1000000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (97/256:ℝ) (49/128:ℝ)
    (11122605/29203456:ℝ) (289242780903/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_097
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0584).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x) ≤ (819536238898594381/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (97/256:ℝ) (49/128:ℝ)
    (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_097 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_098 :
    (1589953789123793223/1000000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (49/128:ℝ) (99/256:ℝ)
    (11468355/29805568:ℝ) (137454803347/50000000000000:ℝ) (76251226959833959/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_098
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0590).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^2*thetaFirstMode x) ≤ (397492992788907399/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (49/128:ℝ) (99/256:ℝ)
    (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_098 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_099 :
    (1541368293469866271/1000000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (99/256:ℝ) (25/64:ℝ)
    (11821197/30413824:ℝ) (261178563961/100000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_099
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0596).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x) ≤ (770693142462749061/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (99/256:ℝ) (25/64:ℝ)
    (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_099 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_100 :
    (746671258912370789/500000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (25/64:ℝ) (101/256:ℝ)
    (12181203/31028224:ℝ) (124014927113/50000000000000:ℝ) (356296586964953583/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_100
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0602).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^2*thetaFirstMode x) ≤ (1493360310280088847/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (25/64:ℝ) (101/256:ℝ)
    (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ) (356296586964953583/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_100 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_101 :
    (90369912867029337/62500000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (101/256:ℝ) (51/128:ℝ)
    (12548445/31648768:ℝ) (29430510381/12500000000000:ℝ) (34420794807094063/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_101
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0608).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x) ≤ (722968095618725921/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (101/256:ℝ) (51/128:ℝ)
    (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ) (34420794807094063/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_101 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_102 :
    (699567986980723453/500000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (51/128:ℝ) (103/256:ℝ)
    (12922995/32275456:ℝ) (44680452331/20000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_102
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0614).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^2*thetaFirstMode x) ≤ (1399153344479055843/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (51/128:ℝ) (103/256:ℝ)
    (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_102 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_103 :
    (33825783414936021/25000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (103/256:ℝ) (13/32:ℝ)
    (13304925/32908288:ℝ) (105942904071/50000000000000:ℝ) (40102031478612231/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_103
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0620).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x) ≤ (1353048484861653677/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (103/256:ℝ) (13/32:ℝ)
    (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_103 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_104 :
    (65381936868372683/50000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (13/32:ℝ) (105/256:ℝ)
    (13694307/33547264:ℝ) (50219137063/25000000000000:ℝ) (30951371593757961/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_104
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0626).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^2*thetaFirstMode x) ≤ (326913914082079569/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (13/32:ℝ) (105/256:ℝ)
    (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (30951371593757961/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_104 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_105 :
    (631494792496135023/500000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (105/256:ℝ) (53/128:ℝ)
    (14091213/34192384:ℝ) (38071343149/20000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_105
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0632).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x) ≤ (1263006267954898547/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (105/256:ℝ) (53/128:ℝ)
    (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_105 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_106 :
    (1219112694189880749/1000000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (53/128:ℝ) (107/256:ℝ)
    (14495715/34843648:ℝ) (180308952359/100000000000000:ℝ) (143847313866595999/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_106
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0638).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^2*thetaFirstMode x) ≤ (243825826964411879/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (53/128:ℝ) (107/256:ℝ)
    (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (143847313866595999/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_106 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_107 :
    (1176034331091179207/1000000000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (107/256:ℝ) (27/64:ℝ)
    (14907885/35501056:ℝ) (170716307377/100000000000000:ℝ) (55435413091796449/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_107
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0644).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x) ≤ (1176050523428878501/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (107/256:ℝ) (27/64:ℝ)
    (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ) (55435413091796449/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_107 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_108 :
    (566889131457507879/500000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (27/64:ℝ) (109/256:ℝ)
    (15327795/36164608:ℝ) (161562236809/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_108
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0650).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^2*thetaFirstMode x) ≤ (566897100682134771/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (27/64:ℝ) (109/256:ℝ)
    (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_108 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_109 :
    (54618290578868981/50000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (109/256:ℝ) (55/128:ℝ)
    (15755517/36834304:ℝ) (76415301097/50000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_109
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0656).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x) ≤ (1092381490910672641/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (109/256:ℝ) (55/128:ℝ)
    (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_109 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_110 :
    (1051815910945474297/1000000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (55/128:ℝ) (111/256:ℝ)
    (16191123/37510144:ℝ) (144505669033/100000000000000:ℝ) (247181206801729151/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_110
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0662).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^2*thetaFirstMode x) ≤ (1051831326323840777/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (55/128:ℝ) (111/256:ℝ)
    (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_110 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_111 :
    (20242903350855439/20000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (111/256:ℝ) (7/16:ℝ)
    (16634685/38192128:ℝ) (136572104877/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_111
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0668).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x) ≤ (1012160314487249847/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (111/256:ℝ) (7/16:ℝ)
    (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_111 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_112 :
    (973367924207636129/1000000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (7/16:ℝ) (113/256:ℝ)
    (17086275/38880256:ℝ) (32253744263/25000000000000:ℝ) (57116879476505503/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_112
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0674).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^2*thetaFirstMode x) ≤ (973382798630441403/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (7/16:ℝ) (113/256:ℝ)
    (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_112 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_113 :
    (935496326676198673/1000000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (113/256:ℝ) (57/128:ℝ)
    (17545965/39574528:ℝ) (30454937517/25000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_113
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0680).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^2*thetaFirstMode x) ≤ (29234716401579283/31250000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (113/256:ℝ) (57/128:ℝ)
    (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_113 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_114 :
    (449270196264438383/500000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (57/128:ℝ) (115/256:ℝ)
    (18013827/40274944:ℝ) (57486141343/50000000000000:ℝ) (105381898272623603/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_114
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0686).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^2*thetaFirstMode x) ≤ (449277355561186743/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (57/128:ℝ) (115/256:ℝ)
    (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_114 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_115 :
    (862508082512887307/1000000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (115/256:ℝ) (29/64:ℝ)
    (18489933/40981504:ℝ) (54229412347/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_115
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0692).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^2*thetaFirstMode x) ≤ (862522118547785741/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (115/256:ℝ) (29/64:ℝ)
    (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_115 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_116 :
    (827405373683523773/1000000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (29/64:ℝ) (117/256:ℝ)
    (18974355/41694208:ℝ) (102266013367/100000000000000:ℝ) (97026004163419267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_116
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0698).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^2*thetaFirstMode x) ≤ (165483824912874477/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (29/64:ℝ) (117/256:ℝ)
    (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ) (97026004163419267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_116 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_117 :
    (198309083573965469/250000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (117/256:ℝ) (59/128:ℝ)
    (19467165/42413056:ℝ) (1927617393/2000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_117
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0704).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^2*thetaFirstMode x) ≤ (79324979779594517/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (117/256:ℝ) (59/128:ℝ)
    (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_117 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_118 :
    (38000160003440349/50000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (59/128:ℝ) (119/256:ℝ)
    (19968435/43138048:ℝ) (45395397031/50000000000000:ℝ) (89155610570721081/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_118
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0710).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^2*thetaFirstMode x) ≤ (380008187164478633/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (59/128:ℝ) (119/256:ℝ)
    (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_118 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_119 :
    (727706451661692053/1000000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (119/256:ℝ) (15/32:ℝ)
    (20478237/43869184:ℝ) (42741781173/50000000000000:ℝ) (42699420868835591/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_119
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0716).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^2*thetaFirstMode x) ≤ (727719335172150107/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (119/256:ℝ) (15/32:ℝ)
    (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ) (42699420868835591/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_119 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_120 :
    (696344892945952879/1000000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (15/32:ℝ) (121/256:ℝ)
    (20996643/44606464:ℝ) (40223660429/50000000000000:ℝ) (3270357328822397/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_120
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0722).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^2*thetaFirstMode x) ≤ (139271496911291969/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (15/32:ℝ) (121/256:ℝ)
    (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ) (3270357328822397/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_120 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_121 :
    (665915730007417867/1000000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (121/256:ℝ) (61/128:ℝ)
    (21523725/45349888:ℝ) (7567058173/10000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_121
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0728).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^2*thetaFirstMode x) ≤ (166482007231076223/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (121/256:ℝ) (61/128:ℝ)
    (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_121 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_122 :
    (25456586022780783/40000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (61/128:ℝ) (123/256:ℝ)
    (22059555/46099456:ℝ) (71142217811/100000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_122
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0734).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^2*thetaFirstMode x) ≤ (25457066253314293/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (61/128:ℝ) (123/256:ℝ)
    (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_122 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_123 :
    (151958975878928729/250000000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (123/256:ℝ) (31/64:ℝ)
    (22604205/46855168:ℝ) (66851457389/100000000000000:ℝ) (35761737420459491/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_123
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0740).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^2*thetaFirstMode x) ≤ (607847616018233263/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (123/256:ℝ) (31/64:ℝ)
    (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ) (35761737420459491/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_123 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_124 :
    (580172378490512347/1000000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (31/64:ℝ) (125/256:ℝ)
    (23157747/47617024:ℝ) (6278787873/10000000000000:ℝ) (68333801879586489/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_124
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0746).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^2*thetaFirstMode x) ≤ (145045949485007613/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (31/64:ℝ) (125/256:ℝ)
    (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ) (68333801879586489/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_124 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_125 :
    (110683137024921381/200000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (125/256:ℝ) (63/128:ℝ)
    (23720253/48385024:ℝ) (2947070221/5000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_125
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0752).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^2*thetaFirstMode x) ≤ (110685362412334883/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (125/256:ℝ) (63/128:ℝ)
    (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_125 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_126 :
    (131889057980467271/250000000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (63/128:ℝ) (127/256:ℝ)
    (24291795/49159168:ℝ) (1106045911/2000000000000:ℝ) (24910558921058049/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_126
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0758).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^2*thetaFirstMode x) ≤ (65945883399079617/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (63/128:ℝ) (127/256:ℝ)
    (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_126 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_2_127 :
    (62822913050403901/125000000000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 2 (127/256:ℝ) (1/2:ℝ)
    (24872445/49939456:ℝ) (25930572867/50000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_127
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0764).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_2_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x) ≤ (50259384916531789/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 2 (127/256:ℝ) (1/2:ℝ)
    (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_127 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

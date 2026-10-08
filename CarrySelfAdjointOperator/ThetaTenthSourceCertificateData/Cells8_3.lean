import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature3

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_8_096 :
    (2422246804892107/500000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (3/8:ℝ) (97/256:ℝ)
    (65332341813084493257/173304480845017500160:ℝ) (12164766849/4000000000000:ℝ) (814502165006677/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_096
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0581).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^8*thetaFirstMode x) ≤ (2422273361000391/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (3/8:ℝ) (97/256:ℝ)
    (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_096 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_097 :
    (500231752849571/100000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (97/256:ℝ) (49/128:ℝ)
    (14336762398671353355/37640552179499351552:ℝ) (72291929829/25000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_097
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0587).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^8*thetaFirstMode x) ≤ (5002373503029347/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (97/256:ℝ) (49/128:ℝ)
    (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_097 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_098 :
    (2579409635237683/500000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (49/128:ℝ) (99/256:ℝ)
    (78578341309131839793/204209882504936988160:ℝ) (274838413521/100000000000000:ℝ) (76251226959833959/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_098
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0593).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^8*thetaFirstMode x) ≤ (5158878189784941/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (49/128:ℝ) (99/256:ℝ)
    (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_098 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_099 :
    (1062726571243561/200000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (99/256:ℝ) (25/64:ℝ)
    (86056132492075958991/221395846441879298560:ℝ) (261111060999/100000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_099
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0599).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^8*thetaFirstMode x) ≤ (332105925034517/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (99/256:ℝ) (25/64:ℝ)
    (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_099 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_100 :
    (5466391052904317/1000000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (25/64:ℝ) (101/256:ℝ)
    (94159912870084059009/239834298071963906560:ℝ) (247965870591/100000000000000:ℝ) (356296586964953583/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_100
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0605).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^8*thetaFirstMode x) ≤ (1093291220008889/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (25/64:ℝ) (101/256:ℝ)
    (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ) (356296586964953583/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_100 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_101 :
    (1123345359562193/200000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (101/256:ℝ) (51/128:ℝ)
    (102935065125197358207/259602677601152028160:ℝ) (2353834549/1000000000000:ℝ) (34420794807094063/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_101
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0611).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^8*thetaFirstMode x) ≤ (21940605557389/3906250000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (101/256:ℝ) (51/128:ℝ)
    (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ) (34420794807094063/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_101 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_102 :
    (1152854926922359/200000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (51/128:ℝ) (103/256:ℝ)
    (22485952682885662245/56156474985950039552:ℝ) (223344831929/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_102
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0617).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^8*thetaFirstMode x) ≤ (230573844359383/40000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (51/128:ℝ) (103/256:ℝ)
    (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_102 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_103 :
    (2954336077564517/500000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (103/256:ℝ) (13/32:ℝ)
    (122695115016799804743/303458889196134300160:ℝ) (211831426291/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_103
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0623).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^8*thetaFirstMode x) ≤ (5908746947278437/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (103/256:ℝ) (13/32:ℝ)
    (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_103 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_104 :
    (302478071949429/50000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (13/32:ℝ) (105/256:ℝ)
    (133785307673187732441/327721993105999567360:ℝ) (200825070001/100000000000000:ℝ) (30951371593757961/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_104
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0629).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^8*thetaFirstMode x) ≤ (6049639613386197/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (13/32:ℝ) (105/256:ℝ)
    (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (30951371593757961/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_104 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_105 :
    (3093295241734563/500000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (105/256:ℝ) (53/128:ℝ)
    (145757762788870993959/353665902141891765760:ℝ) (95154001427/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_105
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0635).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^8*thetaFirstMode x) ≤ (6186672100419651/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (105/256:ℝ) (53/128:ℝ)
    (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_105 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_106 :
    (315970730791211/50000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (53/128:ℝ) (107/256:ℝ)
    (158673294672040530657/381389448748703772160:ℝ) (90131436197/50000000000000:ℝ) (143847313866595999/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_106
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0641).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^8*thetaFirstMode x) ≤ (6319499731198507/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (53/128:ℝ) (107/256:ℝ)
    (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (143847313866595999/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_106 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_107 :
    (1289539576175729/200000000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (107/256:ℝ) (27/64:ℝ)
    (34519255196979847635/82199252318350141952:ℝ) (170672733493/100000000000000:ℝ) (55435413091796449/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_107
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0647).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^8*thetaFirstMode x) ≤ (6447786545743753/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (107/256:ℝ) (27/64:ℝ)
    (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ) (55435413091796449/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_107 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_108 :
    (3285557198068887/500000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (27/64:ℝ) (109/256:ℝ)
    (187594809587397482193/442594949984965788160:ℝ) (161521047537/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_108
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0653).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^8*thetaFirstMode x) ≤ (821400832066191/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (27/64:ℝ) (109/256:ℝ)
    (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_108 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_109 :
    (6689349667633113/1000000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (109/256:ℝ) (55/128:ℝ)
    (203740906957094489391/476299293587687964160:ℝ) (152791681241/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_109
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0659).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^8*thetaFirstMode x) ≤ (6689445564117149/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (109/256:ℝ) (55/128:ℝ)
    (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_109 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_110 :
    (3401050929430413/500000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (55/128:ℝ) (111/256:ℝ)
    (221110673372114090409/512228437469441512960:ℝ) (72234452543/50000000000000:ℝ) (247181206801729151/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_110
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0665).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^8*thetaFirstMode x) ≤ (6802201426391261/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (55/128:ℝ) (111/256:ℝ)
    (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_110 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_111 :
    (3454541503575463/500000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (111/256:ℝ) (7/16:ℝ)
    (239784500047674155607/550507092643036572160:ℝ) (68268695707/50000000000000:ℝ) (59424277358972619/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_111
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0671).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^8*thetaFirstMode x) ≤ (1727296568663571/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (111/256:ℝ) (7/16:ℝ)
    (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_111 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_112 :
    (1752505044951453/250000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (7/16:ℝ) (113/256:ℝ)
    (51969452684042517525/118253148433449738752:ℝ) (64491106081/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_112
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0677).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^8*thetaFirstMode x) ≤ (7010127170062289/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (7/16:ℝ) (113/256:ℝ)
    (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_112 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_113 :
    (1776164141300671/250000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (113/256:ℝ) (57/128:ℝ)
    (281388531776708917143/634640852921264412160:ℝ) (60894418137/50000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_113
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0683).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^8*thetaFirstMode x) ≤ (3552383647261557/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (113/256:ℝ) (57/128:ℝ)
    (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_113 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_114 :
    (7192752492324427/1000000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (57/128:ℝ) (115/256:ℝ)
    (304502779430409389841/680775093154008808960:ℝ) (114943126783/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_114
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0689).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^8*thetaFirstMode x) ≤ (7192866970200599/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (57/128:ℝ) (115/256:ℝ)
    (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_114 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_115 :
    (909260796689217/125000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (115/256:ℝ) (29/64:ℝ)
    (329289608647804933359/729817555912400028160:ℝ) (54215668789/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_115
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0695).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^8*thetaFirstMode x) ≤ (1454840920522433/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (115/256:ℝ) (29/64:ℝ)
    (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_115 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_116 :
    (7348455566688877/1000000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (29/64:ℝ) (117/256:ℝ)
    (355853979535385553057/781923988453504668160:ℝ) (25560027471/25000000000000:ℝ) (97026004163419267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_116
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0701).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^8*thetaFirstMode x) ≤ (7348577542553681/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (29/64:ℝ) (117/256:ℝ)
    (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ) (97026004163419267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_116 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_117 :
    (1853919287815329/250000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (117/256:ℝ) (59/128:ℝ)
    (76861289619680304915/167451405549299389952:ℝ) (96356468443/100000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_117
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0707).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^8*thetaFirstMode x) ≤ (7415802862164587/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (117/256:ℝ) (59/128:ℝ)
    (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_117 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_118 :
    (3737794307540199/500000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (59/128:ℝ) (119/256:ℝ)
    (414763412687601229593/895986442171253532160:ℝ) (90767817427/100000000000000:ℝ) (89155610570721081/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_118
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0713).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^8*thetaFirstMode x) ≤ (7475718041736633/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (59/128:ℝ) (119/256:ℝ)
    (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_118 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_119 :
    (3764024224303751/500000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (119/256:ℝ) (15/32:ℝ)
    (447347369053687618791/958289379521344821760:ℝ) (85461936087/100000000000000:ℝ) (42699420868835591/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_119
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0719).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^8*thetaFirstMode x) ≤ (3764090782112041/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (119/256:ℝ) (15/32:ℝ)
    (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ) (42699420868835591/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_119 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_120 :
    (7572936643913253/1000000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (15/32:ℝ) (121/256:ℝ)
    (482187174233040082809/1024350621420112591360:ℝ) (16085394831/20000000000000:ℝ) (3270357328822397/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_120
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0725).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^8*thetaFirstMode x) ≤ (7573073413888083/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (15/32:ℝ) (121/256:ℝ)
    (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ) (3270357328822397/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_120 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_121 :
    (3805077547862511/500000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (121/256:ℝ) (61/128:ℝ)
    (519418319492085968007/1094362844259452700160:ℝ) (15130289401/20000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_121
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0731).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^8*thetaFirstMode x) ≤ (23782173368187/3125000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (121/256:ℝ) (61/128:ℝ)
    (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_121 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_122 :
    (3819813952210837/500000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (61/128:ℝ) (123/256:ℝ)
    (111836642512315217805/233705377354370135552:ℝ) (35562115301/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_122
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0737).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^8*thetaFirstMode x) ≤ (1909942962108183/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (61/128:ℝ) (123/256:ℝ)
    (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_122 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_123 :
    (383065078891711/50000000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (123/256:ℝ) (31/64:ℝ)
    (601631469395921364543/1247052024347146908160:ℝ) (66834556229/100000000000000:ℝ) (35761737420459491/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_123
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0743).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^8*thetaFirstMode x) ≤ (7661449025670813/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (123/256:ℝ) (31/64:ℝ)
    (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ) (35761737420459491/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_123 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_124 :
    (7675145133129779/1000000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (31/64:ℝ) (125/256:ℝ)
    (646920215696683136241/1330156250206437122560:ℝ) (1961625157/3125000000000:ℝ) (68333801879586489/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_124
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0749).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^8*thetaFirstMode x) ≤ (7675296018943083/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (31/64:ℝ) (125/256:ℝ)
    (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ) (68333801879586489/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_124 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_125 :
    (3840575049352373/500000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (125/256:ℝ) (63/128:ℝ)
    (695214398443277823759/1418066563546442882560:ℝ) (920726599/1562500000000:ℝ) (130504180498755121/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_125
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0755).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^8*thetaFirstMode x) ≤ (1536260869720037/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (125/256:ℝ) (63/128:ℝ)
    (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_125 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_126 :
    (1535866083109213/200000000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (63/128:ℝ) (127/256:ℝ)
    (746687107677957320457/1511019264768615708160:ℝ) (55288311903/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_126
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0761).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^8*thetaFirstMode x) ≤ (7679487948049277/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (63/128:ℝ) (127/256:ℝ)
    (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_126 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_8_127 :
    (1917430560418257/250000000000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 8 (127/256:ℝ) (1/2:ℝ)
    (160303981759231989195/321852051581633495552:ℝ) (12962007471/25000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_127
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0767).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_8_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^8*thetaFirstMode x) ≤ (1917470741846571/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 8 (127/256:ℝ) (1/2:ℝ)
    (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_127 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

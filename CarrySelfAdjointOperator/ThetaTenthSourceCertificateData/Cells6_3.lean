import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature3

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_lower_6_096 :
    (34092655330063249/1000000000000000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (3/8:ℝ) (97/256:ℝ)
    (4364764631770375/11578443094624256:ℝ) (6082910757/2000000000000:ℝ) (814502165006677/2000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_096
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0580).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^6*thetaFirstMode x) ≤ (34093029268023657/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (3/8:ℝ) (97/256:ℝ)
    (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ) (814502165006677/2000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_096 (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_097 :
    (34484984878299663/1000000000000000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (97/256:ℝ) (49/128:ℝ)
    (4691376420086265/12317222597752832:ℝ) (289192734869/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_097
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0586).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x) ≤ (2155335682903667/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (97/256:ℝ) (49/128:ℝ)
    (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ) (394124895899789529/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_097 (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_098 :
    (8711376778942689/250000000000000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (49/128:ℝ) (99/256:ℝ)
    (5038717029229415/13094874042423296:ℝ) (274862139921/100000000000000:ℝ) (76251226959833959/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_098
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0592).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^6*thetaFirstMode x) ≤ (8711476316225817/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (49/128:ℝ) (99/256:ℝ)
    (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ) (76251226959833959/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_098 (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_099 :
    (8793367478176357/250000000000000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (99/256:ℝ) (25/64:ℝ)
    (5407871390045593/13913016748648448:ℝ) (130566778813/50000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_099
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0598).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x) ≤ (17586940066235413/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (99/256:ℝ) (25/64:ℝ)
    (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ) (368646294189955231/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_099 (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_100 :
    (35468210361172531/1000000000000000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (25/64:ℝ) (101/256:ℝ)
    (5799969393965607/14773320111515648:ℝ) (247987194389/100000000000000:ℝ) (356296586964953583/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_100
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0604).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^6*thetaFirstMode x) ≤ (35468632599378843/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (25/64:ℝ) (101/256:ℝ)
    (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ) (356296586964953583/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_100 (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_101 :
    (17864578270953369/500000000000000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (101/256:ℝ) (51/128:ℝ)
    (6216187276192985/15677504623056896:ℝ) (14712728779/6250000000000:ℝ) (34420794807094063/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_101
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0610).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x) ≤ (35729590724618327/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (101/256:ℝ) (51/128:ℝ)
    (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ) (34420794807094063/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_101 (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_102 :
    (35955828913552289/1000000000000000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (51/128:ℝ) (103/256:ℝ)
    (6657749026974535/16627342904440832:ℝ) (223363971597/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_102
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0616).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^6*thetaFirstMode x) ≤ (35956274944396327/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (51/128:ℝ) (103/256:ℝ)
    (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ) (332381038839280923/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_102 (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_103 :
    (36147841318850801/1000000000000000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (103/256:ℝ) (13/32:ℝ)
    (7125927831236025/17624660748486656:ℝ) (21184955023/10000000000000:ℝ) (40102031478612231/125000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_103
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0622).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x) ≤ (18074149539502963/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (103/256:ℝ) (13/32:ℝ)
    (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ) (40102031478612231/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_103 (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_104 :
    (36304901609513639/1000000000000000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (13/32:ℝ) (105/256:ℝ)
    (7622047536865223/18671338172499968:ℝ) (12552639143/6250000000000:ℝ) (30951371593757961/100000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_104
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0628).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^6*thetaFirstMode x) ≤ (18152685478811963/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (13/32:ℝ) (105/256:ℝ)
    (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ) (30951371593757961/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_104 (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_105 :
    (7285362378309677/200000000000000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (105/256:ℝ) (53/128:ℝ)
    (8147484151924537/19769310481430528:ℝ) (47581059389/25000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_105
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0634).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x) ≤ (36427292663281983/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (105/256:ℝ) (53/128:ℝ)
    (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ) (298473301835686887/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_105 (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_106 :
    (36513468392516461/1000000000000000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (53/128:ℝ) (107/256:ℝ)
    (8703667371075495/20920569341351936:ℝ) (180278229643/100000000000000:ℝ) (143847313866595999/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_106
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0640).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^6*thetaFirstMode x) ≤ (7302792080204439/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (53/128:ℝ) (107/256:ℝ)
    (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ) (143847313866595999/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_106 (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_107 :
    (36564860959106827/1000000000000000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (107/256:ℝ) (27/64:ℝ)
    (9292082131497305/22127163863263232:ℝ) (170687255559/100000000000000:ℝ) (55435413091796449/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_107
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0646).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x) ≤ (731307279894907/20000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (107/256:ℝ) (27/64:ℝ)
    (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ) (55435413091796449/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_107 (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_108 :
    (36581072189375929/1000000000000000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (27/64:ℝ) (109/256:ℝ)
    (9914270198581735/23391201697212416:ℝ) (161534774899/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_108
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0652).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^6*thetaFirstMode x) ≤ (36581586020126749/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (27/64:ℝ) (109/256:ℝ)
    (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ) (133459873385764947/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_108 (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_109 :
    (36562276209912659/1000000000000000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (109/256:ℝ) (55/128:ℝ)
    (10571831781686553/24714850136741888:ℝ) (38201163163/25000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_109
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0658).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x) ≤ (18281400290681363/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (109/256:ℝ) (55/128:ℝ)
    (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ) (256921569980402861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_109 (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_110 :
    (7301747421492381/200000000000000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (55/128:ℝ) (111/256:ℝ)
    (11266427180229767/26100337233655808:ℝ) (144481157641/100000000000000:ℝ) (247181206801729151/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_110
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0664).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^6*thetaFirstMode x) ≤ (2281829483952987/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (55/128:ℝ) (111/256:ℝ)
    (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ) (247181206801729151/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_110 (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_111 :
    (18210403514109271/500000000000000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (111/256:ℝ) (7/16:ℝ)
    (11999778460406905/27549952923109376:ℝ) (13654896061/10000000000000:ℝ) (59424277358972619/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_111
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0670).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x) ≤ (36421351630258947/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (111/256:ℝ) (7/16:ℝ)
    (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ) (59424277358972619/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_111 (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_112 :
    (18149461978435843/500000000000000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (7/16:ℝ) (113/256:ℝ)
    (12773671162813575/29066050159020032:ℝ) (128993131963/100000000000000:ℝ) (57116879476505503/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_112
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0676).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^6*thetaFirstMode x) ≤ (907486955133581/25000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (7/16:ℝ) (113/256:ℝ)
    (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ) (57116879476505503/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_112 (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_113 :
    (36143609188969533/1000000000000000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (113/256:ℝ) (57/128:ℝ)
    (13589956041255545/30651046059800576:ℝ) (121799139163/100000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_113
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0682).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^6*thetaFirstMode x) ≤ (7228834548807337/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (113/256:ℝ) (57/128:ℝ)
    (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ) (219490467503629413/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_113 (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_114 :
    (35955464517457577/1000000000000000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (57/128:ℝ) (115/256:ℝ)
    (14450550833028583/32307423064414208:ℝ) (5747642191/5000000000000:ℝ) (105381898272623603/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_114
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0688).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^6*thetaFirstMode x) ≤ (35956037018838939/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (57/128:ℝ) (115/256:ℝ)
    (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ) (105381898272623603/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_114 (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_115 :
    (35735169144675823/1000000000000000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (115/256:ℝ) (29/64:ℝ)
    (15357442060950297/34037730098751488:ℝ) (54220249229/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_115
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0694).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^6*thetaFirstMode x) ≤ (17867875106066577/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (115/256:ℝ) (29/64:ℝ)
    (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ) (4045703083264843/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_115 (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_116 :
    (17741738170524633/500000000000000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (29/64:ℝ) (117/256:ℝ)
    (16312686867426215/35844583752329216:ℝ) (20449748597/20000000000000:ℝ) (97026004163419267/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_116
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0700).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^6*thetaFirstMode x) ≤ (17742032787916979/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (29/64:ℝ) (117/256:ℝ)
    (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ) (97026004163419267/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_116 (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_117 :
    (17600604934851149/500000000000000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (117/256:ℝ) (59/128:ℝ)
    (17318414880832345/37730669465311232:ℝ) (48182300439/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_117
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0706).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^6*thetaFirstMode x) ≤ (35201806854951897/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (117/256:ℝ) (59/128:ℝ)
    (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ) (186061653955860893/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_117 (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_118 :
    (4361157524475751/125000000000000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (59/128:ℝ) (119/256:ℝ)
    (18376830114496455/39698742725851136:ℝ) (22693868773/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_118
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0712).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^6*thetaFirstMode x) ≤ (4361233062121671/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (59/128:ℝ) (119/256:ℝ)
    (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ) (89155610570721081/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_118 (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_119 :
    (6909716100398723/200000000000000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (119/256:ℝ) (15/32:ℝ)
    (19490212898560313/41751630277756928:ℝ) (21367285927/25000000000000:ℝ) (42699420868835591/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_119
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0718).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^6*thetaFirstMode x) ≤ (8637297917153073/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (119/256:ℝ) (15/32:ℝ)
    (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ) (42699420868835591/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_119 (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_120 :
    (17090091265376323/500000000000000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (15/32:ℝ) (121/256:ℝ)
    (20660921845005127/43892231338477568:ℝ) (20108438833/25000000000000:ℝ) (3270357328822397/20000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_120
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0724).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^6*thetaFirstMode x) ≤ (34180800097081707/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (15/32:ℝ) (121/256:ℝ)
    (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ) (3270357328822397/20000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_120 (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_121 :
    (33785132276748357/1000000000000000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (121/256:ℝ) (61/128:ℝ)
    (21891395846122425/46123518827411456:ℝ) (75657824261/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_121
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0730).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^6*thetaFirstMode x) ≤ (33785755761757077/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (121/256:ℝ) (61/128:ℝ)
    (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ) (156468455838422989/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_121 (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_122 :
    (333645455467563/10000000000000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (61/128:ℝ) (123/256:ℝ)
    (23184156106712615/48448540604536832:ℝ) (71130225419/100000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_122
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0736).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^6*thetaFirstMode x) ≤ (33365174456594363/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (61/128:ℝ) (123/256:ℝ)
    (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ) (149646006282575861/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_122 (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_123 :
    (16459791708017153/500000000000000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (123/256:ℝ) (31/64:ℝ)
    (24541808210293465/50870420719364096:ℝ) (16710047273/25000000000000:ℝ) (35761737420459491/250000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_123
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0742).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^6*thetaFirstMode x) ≤ (32920217244334557/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (123/256:ℝ) (31/64:ℝ)
    (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ) (35761737420459491/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_123 (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_124 :
    (8112861899356797/250000000000000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (31/64:ℝ) (125/256:ℝ)
    (25967044219600743/53392360670210048:ℝ) (62777295461/100000000000000:ℝ) (68333801879586489/500000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_124
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0748).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^6*thetaFirstMode x) ≤ (4056510728338659/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (31/64:ℝ) (125/256:ℝ)
    (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ) (68333801879586489/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_124 (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_125 :
    (31961375748182737/1000000000000000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (125/256:ℝ) (63/128:ℝ)
    (27462644811663257/56017640673794048:ℝ) (58931468953/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_125
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0754).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^6*thetaFirstMode x) ≤ (7990504462828359/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (125/256:ℝ) (63/128:ℝ)
    (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ) (130504180498755121/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_125 (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_126 :
    (1965664796145369/62500000000000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (63/128:ℝ) (127/256:ℝ)
    (29031481447734535/58749620945156096:ℝ) (27646486213/50000000000000:ℝ) (24910558921058049/200000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_126
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0760).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^6*thetaFirstMode x) ≤ (1965705136173817/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (63/128:ℝ) (127/256:ℝ)
    (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ) (24910558921058049/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_126 (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_lower_6_127 :
    (30920525895897537/1000000000000000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_curvature_cell_lower 6 (127/256:ℝ) (1/2:ℝ)
    (30676518578363385/61591742987896832:ℝ) (51852401189/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) thetaSource_cell_curvature_127
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0766).1
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_6_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x) ≤ (30921174130265801/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 6 (127/256:ℝ) (1/2:ℝ)
    (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ) (118809471896163623/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_127 (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

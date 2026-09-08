import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes00
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes01
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes02
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes03
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes04
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes05
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes06
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes07
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes08
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes09
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes10
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes11
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes12
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes13
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes14
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes15
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes16
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes17
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes18
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes19
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes20
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes21
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes22
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes23
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes24
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes25
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes26
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes27
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes28
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes29
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes30
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes31
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes32
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes33
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes34
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes35
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes36
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes37
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes38
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes39
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes40
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes41
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes42
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes43
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes44
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes45
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes46
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes47
import CarrySelfAdjointOperator.ThetaEighthMomentCertificateData.ThetaNodes48
import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaFirstMode_refined_cell_lower_2_096 :
    (4249193772602051/2516582400000000000000:ℝ) ≤ ∫ x in (3/8:ℝ)..(97/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/8:ℝ) (97/256:ℝ) (10783875/28607488:ℝ) (152099143523/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0578).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_096 :
    (∫ x in (3/8:ℝ)..(97/256:ℝ), x^2*thetaFirstMode x) ≤ (17001301758068591/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/8:ℝ) (97/256:ℝ) (311943577261/100000000000000:ℝ) (296667793723/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0576).2 (thetaFirstMode_refined_node_0582).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_097 :
    (2749638289524219/1677721600000000000000:ℝ) ≤ ∫ x in (97/256:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (97/256:ℝ) (49/128:ℝ) (11122605/29203456:ℝ) (289242780903/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0584).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_097 :
    (∫ x in (97/256:ℝ)..(49/128:ℝ), x^2*thetaFirstMode x) ≤ (8251151140886473/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (97/256:ℝ) (49/128:ℝ) (296667793723/100000000000000:ℝ) (282024656491/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0582).2 (thetaFirstMode_refined_node_0588).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_098 :
    (4000896961021129/2516582400000000000000:ℝ) ≤ ∫ x in (49/128:ℝ)..(99/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (49/128:ℝ) (99/256:ℝ) (11468355/29805568:ℝ) (137454803347/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0590).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_098 :
    (∫ x in (49/128:ℝ)..(99/256:ℝ), x^2*thetaFirstMode x) ≤ (32016008152586611/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (49/128:ℝ) (99/256:ℝ) (282024656491/100000000000000:ℝ) (33499220303/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0588).2 (thetaFirstMode_refined_node_0594).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_099 :
    (7757264528205661/5033164800000000000000:ℝ) ≤ ∫ x in (99/256:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (99/256:ℝ) (25/64:ℝ) (11821197/30413824:ℝ) (261178563961/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0596).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_099 :
    (∫ x in (99/256:ℝ)..(25/64:ℝ), x^2*thetaFirstMode x) ≤ (7759443445948333/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (99/256:ℝ) (25/64:ℝ) (33499220303/12500000000000:ℝ) (12727755463/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0594).2 (thetaFirstMode_refined_node_0600).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_100 :
    (3757776306451013/2516582400000000000000:ℝ) ≤ ∫ x in (25/64:ℝ)..(101/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/64:ℝ) (101/256:ℝ) (12181203/31028224:ℝ) (124014927113/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0602).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_100 :
    (∫ x in (25/64:ℝ)..(101/256:ℝ), x^2*thetaFirstMode x) ≤ (7517701343445937/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/64:ℝ) (101/256:ℝ) (12727755463/5000000000000:ℝ) (30211137237/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0600).2 (thetaFirstMode_refined_node_0606).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_101 :
    (303202928115189/209715200000000000000:ℝ) ≤ ∫ x in (101/256:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (101/256:ℝ) (51/128:ℝ) (12548445/31648768:ℝ) (29430510381/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0608).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_101 :
    (∫ x in (101/256:ℝ)..(51/128:ℝ), x^2*thetaFirstMode x) ≤ (29115951533502281/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (101/256:ℝ) (51/128:ℝ) (30211137237/12500000000000:ℝ) (9175061369/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0606).2 (thetaFirstMode_refined_node_0612).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_102 :
    (1408283177020789/1006632960000000000000:ℝ) ≤ ∫ x in (51/128:ℝ)..(103/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (51/128:ℝ) (103/256:ℝ) (12922995/32275456:ℝ) (44680452331/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0614).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_102 :
    (∫ x in (51/128:ℝ)..(103/256:ℝ), x^2*thetaFirstMode x) ≤ (14087002983448159/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (51/128:ℝ) (103/256:ℝ) (9175061369/4000000000000:ℝ) (217598630551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0612).2 (thetaFirstMode_refined_node_0618).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_103 :
    (1134895702709909/838860800000000000000:ℝ) ≤ ∫ x in (103/256:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (103/256:ℝ) (13/32:ℝ) (13304925/32908288:ℝ) (105942904071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0620).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_103 :
    (∫ x in (103/256:ℝ)..(13/32:ℝ), x^2*thetaFirstMode x) ≤ (1702856749013473/1258291200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (103/256:ℝ) (13/32:ℝ) (217598630551/100000000000000:ℝ) (206337006571/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0618).2 (thetaFirstMode_refined_node_0624).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_104 :
    (1645229149320943/1258291200000000000000:ℝ) ≤ ∫ x in (13/32:ℝ)..(105/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/32:ℝ) (105/256:ℝ) (13694307/33547264:ℝ) (50219137063/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0626).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_104 :
    (∫ x in (13/32:ℝ)..(105/256:ℝ), x^2*thetaFirstMode x) ≤ (8777247708004083/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/32:ℝ) (105/256:ℝ) (206337006571/100000000000000:ℝ) (97786844973/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0624).2 (thetaFirstMode_refined_node_0630).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_105 :
    (1271240219088259/1006632960000000000000:ℝ) ≤ ∫ x in (105/256:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (105/256:ℝ) (53/128:ℝ) (14091213/34192384:ℝ) (38071343149/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0632).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_105 :
    (∫ x in (105/256:ℝ)..(53/128:ℝ), x^2*thetaFirstMode x) ≤ (2119395323211161/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (105/256:ℝ) (53/128:ℝ) (97786844973/50000000000000:ℝ) (92645558231/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0630).2 (thetaFirstMode_refined_node_0636).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_106 :
    (6135372721919693/5033164800000000000000:ℝ) ≤ ∫ x in (53/128:ℝ)..(107/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (53/128:ℝ) (107/256:ℝ) (14495715/34843648:ℝ) (180308952359/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0638).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_106 :
    (∫ x in (53/128:ℝ)..(107/256:ℝ), x^2*thetaFirstMode x) ≤ (3068661314534059/2516582400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (53/128:ℝ) (107/256:ℝ) (92645558231/50000000000000:ℝ) (17547212979/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0636).2 (thetaFirstMode_refined_node_0642).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_107 :
    (5918563660453213/5033164800000000000000:ℝ) ≤ ∫ x in (107/256:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (107/256:ℝ) (27/64:ℝ) (14907885/35501056:ℝ) (170716307377/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0644).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_107 :
    (∫ x in (107/256:ℝ)..(27/64:ℝ), x^2*thetaFirstMode x) ≤ (11840955997975769/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (107/256:ℝ) (27/64:ℝ) (17547212979/10000000000000:ℝ) (20762497607/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0642).2 (thetaFirstMode_refined_node_0648).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_108 :
    (5705893517383453/5033164800000000000000:ℝ) ≤ ∫ x in (27/64:ℝ)..(109/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/64:ℝ) (109/256:ℝ) (15327795/36164608:ℝ) (161562236809/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0650).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_108 :
    (∫ x in (27/64:ℝ)..(109/256:ℝ), x^2*thetaFirstMode x) ≤ (22831086966240133/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/64:ℝ) (109/256:ℝ) (20762497607/12500000000000:ℝ) (157158326831/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0648).2 (thetaFirstMode_refined_node_0654).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_109 :
    (2748734795760187/2516582400000000000000:ℝ) ≤ ∫ x in (109/256:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (109/256:ℝ) (55/128:ℝ) (15755517/36834304:ℝ) (76415301097/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0656).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_109 :
    (∫ x in (109/256:ℝ)..(55/128:ℝ), x^2*thetaFirstMode x) ≤ (10998622422320057/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (109/256:ℝ) (55/128:ℝ) (157158326831/100000000000000:ℝ) (148631229741/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0654).2 (thetaFirstMode_refined_node_0660).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_110 :
    (5293387162347823/5033164800000000000000:ℝ) ≤ ∫ x in (55/128:ℝ)..(111/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (55/128:ℝ) (111/256:ℝ) (16191123/37510144:ℝ) (144505669033/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0662).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_110 :
    (∫ x in (55/128:ℝ)..(111/256:ℝ), x^2*thetaFirstMode x) ≤ (4236153394078001/4026531840000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (55/128:ℝ) (111/256:ℝ) (148631229741/100000000000000:ℝ) (17562894341/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0660).2 (thetaFirstMode_refined_node_0666).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_111 :
    (1697909931865823/1677721600000000000000:ℝ) ≤ ∫ x in (111/256:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (111/256:ℝ) (7/16:ℝ) (16634685/38192128:ℝ) (136572104877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0668).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_111 :
    (∫ x in (111/256:ℝ)..(7/16:ℝ), x^2*thetaFirstMode x) ≤ (20381987825316421/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (111/256:ℝ) (7/16:ℝ) (17562894341/12500000000000:ℝ) (132758967949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0666).2 (thetaFirstMode_refined_node_0672).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_112 :
    (1224642415921847/1258291200000000000000:ℝ) ≤ ∫ x in (7/16:ℝ)..(113/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/16:ℝ) (113/256:ℝ) (17086275/38880256:ℝ) (32253744263/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0674).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_112 :
    (∫ x in (7/16:ℝ)..(113/256:ℝ), x^2*thetaFirstMode x) ≤ (19601196316379783/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/16:ℝ) (113/256:ℝ) (132758967949/100000000000000:ℝ) (62691967071/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0672).2 (thetaFirstMode_refined_node_0678).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_113 :
    (392330656739833/419430400000000000000:ℝ) ≤ ∫ x in (113/256:ℝ)..(57/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (113/256:ℝ) (57/128:ℝ) (17545965/39574528:ℝ) (30454937517/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0680).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_113 :
    (∫ x in (113/256:ℝ)..(57/128:ℝ), x^2*thetaFirstMode x) ≤ (9419318557331287/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (113/256:ℝ) (57/128:ℝ) (62691967071/50000000000000:ℝ) (5918185693/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0678).2 (thetaFirstMode_refined_node_0684).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_114 :
    (2260987425161533/2516582400000000000000:ℝ) ≤ ∫ x in (57/128:ℝ)..(115/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (57/128:ℝ) (115/256:ℝ) (18013827/40274944:ℝ) (57486141343/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0686).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_114 :
    (∫ x in (57/128:ℝ)..(115/256:ℝ), x^2*thetaFirstMode x) ≤ (18094512044472197/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (57/128:ℝ) (115/256:ℝ) (5918185693/5000000000000:ℝ) (111684360387/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0684).2 (thetaFirstMode_refined_node_0690).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_115 :
    (2170315311539287/2516582400000000000000:ℝ) ≤ ∫ x in (115/256:ℝ)..(29/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (115/256:ℝ) (29/64:ℝ) (18489933/40981504:ℝ) (54229412347/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0692).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_115 :
    (∫ x in (115/256:ℝ)..(29/64:ℝ), x^2*thetaFirstMode x) ≤ (5789660505843833/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (115/256:ℝ) (29/64:ℝ) (111684360387/100000000000000:ℝ) (52666158177/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0690).2 (thetaFirstMode_refined_node_0696).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_116 :
    (4163965266264139/5033164800000000000000:ℝ) ≤ ∫ x in (29/64:ℝ)..(117/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/64:ℝ) (117/256:ℝ) (18974355/41694208:ℝ) (102266013367/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0698).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_116 :
    (∫ x in (29/64:ℝ)..(117/256:ℝ), x^2*thetaFirstMode x) ≤ (8331083003315587/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/64:ℝ) (117/256:ℝ) (52666158177/50000000000000:ℝ) (4964720503/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0696).2 (thetaFirstMode_refined_node_0702).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_117 :
    (26613328266889/33554432000000000000:ℝ) ≤ ∫ x in (117/256:ℝ)..(59/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (117/256:ℝ) (59/128:ℝ) (19467165/42413056:ℝ) (1927617393/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0704).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_117 :
    (∫ x in (117/256:ℝ)..(59/128:ℝ), x^2*thetaFirstMode x) ≤ (7987073776172059/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (117/256:ℝ) (59/128:ℝ) (4964720503/5000000000000:ℝ) (46778925753/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0702).2 (thetaFirstMode_refined_node_0708).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_118 :
    (1912371890724937/2516582400000000000000:ℝ) ≤ ∫ x in (59/128:ℝ)..(119/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (59/128:ℝ) (119/256:ℝ) (19968435/43138048:ℝ) (45395397031/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0710).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_118 :
    (∫ x in (59/128:ℝ)..(119/256:ℝ), x^2*thetaFirstMode x) ≤ (7652485649230027/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (59/128:ℝ) (119/256:ℝ) (46778925753/50000000000000:ℝ) (22027557043/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0708).2 (thetaFirstMode_refined_node_0714).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_119 :
    (610366882410831/838860800000000000000:ℝ) ≤ ∫ x in (119/256:ℝ)..(15/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (119/256:ℝ) (15/32:ℝ) (20478237/43869184:ℝ) (42741781173/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0716).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_119 :
    (∫ x in (119/256:ℝ)..(15/32:ℝ), x^2*thetaFirstMode x) ≤ (3663661762813463/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (119/256:ℝ) (15/32:ℝ) (22027557043/25000000000000:ℝ) (10367437567/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0714).2 (thetaFirstMode_refined_node_0720).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_120 :
    (1752182871947669/2516582400000000000000:ℝ) ≤ ∫ x in (15/32:ℝ)..(121/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/32:ℝ) (121/256:ℝ) (20996643/44606464:ℝ) (40223660429/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0722).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_120 :
    (∫ x in (15/32:ℝ)..(121/256:ℝ), x^2*thetaFirstMode x) ≤ (3505787713920659/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/32:ℝ) (121/256:ℝ) (10367437567/12500000000000:ℝ) (3901699867/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0720).2 (thetaFirstMode_refined_node_0726).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_121 :
    (335122305307651/503316480000000000000:ℝ) ≤ ∫ x in (121/256:ℝ)..(61/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (121/256:ℝ) (61/128:ℝ) (21523725/45349888:ℝ) (7567058173/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0728).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_121 :
    (∫ x in (121/256:ℝ)..(61/128:ℝ), x^2*thetaFirstMode x) ≤ (13410426585474139/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (121/256:ℝ) (61/128:ℝ) (3901699867/5000000000000:ℝ) (73382410647/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0726).2 (thetaFirstMode_refined_node_0732).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_122 :
    (3202751503633409/5033164800000000000000:ℝ) ≤ ∫ x in (61/128:ℝ)..(123/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (61/128:ℝ) (123/256:ℝ) (22059555/46099456:ℝ) (71142217811/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0734).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_122 :
    (∫ x in (61/128:ℝ)..(123/256:ℝ), x^2*thetaFirstMode x) ≤ (4272129180521139/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (61/128:ℝ) (123/256:ℝ) (73382410647/100000000000000:ℝ) (34486895331/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0732).2 (thetaFirstMode_refined_node_0738).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_123 :
    (3058922135748473/5033164800000000000000:ℝ) ≤ ∫ x in (123/256:ℝ)..(31/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (123/256:ℝ) (31/64:ℝ) (22604205/46855168:ℝ) (66851457389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0740).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_123 :
    (∫ x in (123/256:ℝ)..(31/64:ℝ), x^2*thetaFirstMode x) ≤ (4080306017927173/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (123/256:ℝ) (31/64:ℝ) (34486895331/50000000000000:ℝ) (12959508073/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0738).2 (thetaFirstMode_refined_node_0744).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_124 :
    (97323304960791/167772160000000000000:ℝ) ≤ ∫ x in (31/64:ℝ)..(125/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/64:ℝ) (125/256:ℝ) (23157747/47617024:ℝ) (6278787873/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0746).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_124 :
    (∫ x in (31/64:ℝ)..(125/256:ℝ), x^2*thetaFirstMode x) ≤ (11683875082162789/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/64:ℝ) (125/256:ℝ) (12959508073/20000000000000:ℝ) (7605426243/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0744).2 (thetaFirstMode_refined_node_0750).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_125 :
    (139252015012471/251658240000000000000:ℝ) ≤ ∫ x in (125/256:ℝ)..(63/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (125/256:ℝ) (63/128:ℝ) (23720253/48385024:ℝ) (2947070221/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0752).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_125 :
    (∫ x in (125/256:ℝ)..(63/128:ℝ), x^2*thetaFirstMode x) ≤ (3715029937648457/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (125/256:ℝ) (63/128:ℝ) (7605426243/12500000000000:ℝ) (57101491059/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0750).2 (thetaFirstMode_refined_node_0756).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_126 :
    (53097946049377/100663296000000000000:ℝ) ≤ ∫ x in (63/128:ℝ)..(127/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (63/128:ℝ) (127/256:ℝ) (24291795/49159168:ℝ) (1106045911/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0758).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_126 :
    (∫ x in (63/128:ℝ)..(127/256:ℝ), x^2*thetaFirstMode x) ≤ (885364103813801/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (63/128:ℝ) (127/256:ℝ) (57101491059/100000000000000:ℝ) (53562210939/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0756).2 (thetaFirstMode_refined_node_0762).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_127 :
    (421536036050241/838860800000000000000:ℝ) ≤ ∫ x in (127/256:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (127/256:ℝ) (1/2:ℝ) (24872445/49939456:ℝ) (25930572867/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0764).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_127 :
    (∫ x in (127/256:ℝ)..(1/2:ℝ), x^2*thetaFirstMode x) ≤ (1686916294578439/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (127/256:ℝ) (1/2:ℝ) (53562210939/100000000000000:ℝ) (50216326329/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0762).2 (thetaFirstMode_refined_node_0768).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

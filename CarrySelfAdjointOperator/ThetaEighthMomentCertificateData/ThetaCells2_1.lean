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

theorem thetaFirstMode_refined_cell_lower_2_032 :
    (1961334045900983/838860800000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/8:ℝ) (33/256:ℝ) (412035/3245056:ℝ) (1856737815621/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0194).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^2*thetaFirstMode x) ≤ (15691936159746879/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/8:ℝ) (33/256:ℝ) (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_033 :
    (12136104557583643/5033164800000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (33/256:ℝ) (17/128:ℝ) (451245/3447808:ℝ) (3604426658029/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0200).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^2*thetaFirstMode x) ≤ (16182802237019131/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (33/256:ℝ) (17/128:ℝ) (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_034 :
    (3122578687133443/1258291200000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/128:ℝ) (35/256:ℝ) (492867/3656704:ℝ) (874426963633/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0206).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^2*thetaFirstMode x) ≤ (49965446096609041/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/128:ℝ) (35/256:ℝ) (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_035 :
    (1603756557877909/629145600000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (35/256:ℝ) (9/64:ℝ) (536973/3871744:ℝ) (424162009489/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0212).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^2*thetaFirstMode x) ≤ (4277049730477633/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (35/256:ℝ) (9/64:ℝ) (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_036 :
    (876986486535943/335544320000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/64:ℝ) (37/256:ℝ) (583635/4092928:ℝ) (658233540057/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0218).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^2*thetaFirstMode x) ≤ (4385314731340137/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/64:ℝ) (37/256:ℝ) (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_037 :
    (42075278103787/15728640000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (37/256:ℝ) (19/128:ℝ) (632925/4320256:ℝ) (9972808273/312500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0224).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^2*thetaFirstMode x) ≤ (8976857459374569/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (37/256:ℝ) (19/128:ℝ) (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_038 :
    (6878762786982979/2516582400000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/128:ℝ) (39/256:ℝ) (684915/4553728:ℝ) (1546832198557/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0230).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^2*thetaFirstMode x) ≤ (27517546238719529/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/128:ℝ) (39/256:ℝ) (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_039 :
    (14034761478482501/5033164800000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (39/256:ℝ) (5/32:ℝ) (739677/4793344:ℝ) (2998240008221/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0236).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^2*thetaFirstMode x) ≤ (28072118681739623/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (39/256:ℝ) (5/32:ℝ) (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_040 :
    (4765168557414349/1677721600000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/32:ℝ) (41/256:ℝ) (797283/5039104:ℝ) (2905000136607/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0242).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^2*thetaFirstMode x) ≤ (5718741494895793/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/32:ℝ) (41/256:ℝ) (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_041 :
    (2423253291987499/838860800000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (41/256:ℝ) (21/128:ℝ) (857805/5291008:ℝ) (1406959526991/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0248).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^2*thetaFirstMode x) ≤ (2326546851790657/805306368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (41/256:ℝ) (21/128:ℝ) (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_042 :
    (14766616040717633/5033164800000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/128:ℝ) (43/256:ℝ) (921315/5549056:ℝ) (2724970666307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0254).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^2*thetaFirstMode x) ≤ (59072255371243459/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/128:ℝ) (43/256:ℝ) (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_043 :
    (14976655678315583/5033164800000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (43/256:ℝ) (11/64:ℝ) (987885/5813248:ℝ) (2638128532379/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0260).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^2*thetaFirstMode x) ≤ (29956305708823513/10066329600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (43/256:ℝ) (11/64:ℝ) (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_044 :
    (15169546707237403/5033164800000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/64:ℝ) (45/256:ℝ) (1057587/6083584:ℝ) (2553365882383/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0266).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^2*thetaFirstMode x) ≤ (3034218564417683/1006632960000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/64:ℝ) (45/256:ℝ) (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_045 :
    (7672621079070007/2516582400000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (45/256:ℝ) (23/128:ℝ) (1130493/6360064:ℝ) (1235327818237/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0272).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^2*thetaFirstMode x) ≤ (61387346795085541/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (45/256:ℝ) (23/128:ℝ) (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_046 :
    (15503738136745001/5033164800000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/128:ℝ) (47/256:ℝ) (1206675/6642688:ℝ) (2389970423423/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0278).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^2*thetaFirstMode x) ≤ (4134768136973767/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/128:ℝ) (47/256:ℝ) (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_047 :
    (15645071914208177/5033164800000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (47/256:ℝ) (3/16:ℝ) (1286205/6931456:ℝ) (2311282599233/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0284).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^2*thetaFirstMode x) ≤ (62587045850823859/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (47/256:ℝ) (3/16:ℝ) (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_048 :
    (1576932002368003/503316480000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/16:ℝ) (49/256:ℝ) (1369155/7226368:ℝ) (223456426579/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0290).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^2*thetaFirstMode x) ≤ (6308422402154233/2013265920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/16:ℝ) (49/256:ℝ) (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_049 :
    (5292198788364149/1677721600000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (49/256:ℝ) (25/128:ℝ) (1455597/7527424:ℝ) (2159787289497/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0296).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^2*thetaFirstMode x) ≤ (10585585313081921/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (49/256:ℝ) (25/128:ℝ) (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_050 :
    (7983525160254497/2516582400000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/128:ℝ) (51/256:ℝ) (1545603/7834624:ℝ) (1043461659947/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0302).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^2*thetaFirstMode x) ≤ (21291835556385091/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/128:ℝ) (51/256:ℝ) (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_051 :
    (8020432441345421/2516582400000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (51/256:ℝ) (13/64:ℝ) (1639245/8147968:ℝ) (1007971904153/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0308).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^2*thetaFirstMode x) ≤ (4278062672720633/1342177280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (51/256:ℝ) (13/64:ℝ) (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_052 :
    (16098254798061799/5033164800000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/64:ℝ) (53/256:ℝ) (1736595/8467456:ℝ) (1946820026371/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0314).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^2*thetaFirstMode x) ≤ (21466890287974801/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/64:ℝ) (53/256:ℝ) (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_053 :
    (2689910787872823/838860800000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (53/256:ℝ) (27/128:ℝ) (1837725/8793088:ℝ) (939761542287/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0320).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^2*thetaFirstMode x) ≤ (2690236557248993/838860800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (53/256:ℝ) (27/128:ℝ) (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_054 :
    (16164767424874831/5033164800000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/128:ℝ) (55/256:ℝ) (1942707/9124864:ℝ) (1814023950721/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0326).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^2*thetaFirstMode x) ≤ (10777841731846007/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/128:ℝ) (55/256:ℝ) (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_055 :
    (673935914176151/209715200000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (55/256:ℝ) (7/32:ℝ) (2051613/9462784:ℝ) (218786683533/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0332).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^2*thetaFirstMode x) ≤ (16176496468534657/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (55/256:ℝ) (7/32:ℝ) (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_056 :
    (3233774368414187/1006632960000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/32:ℝ) (57/256:ℝ) (2164515/9806848:ℝ) (337660474931/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0338).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^2*thetaFirstMode x) ≤ (5390314822370057/1677721600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/32:ℝ) (57/256:ℝ) (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_057 :
    (201854293344067/62914560000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (57/256:ℝ) (29/128:ℝ) (2281485/10157056:ℝ) (20350266493/1250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0344).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^2*thetaFirstMode x) ≤ (10766968583993321/3355443200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (57/256:ℝ) (29/128:ℝ) (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_058 :
    (322264883981749/100663296000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/128:ℝ) (59/256:ℝ) (2402595/10513408:ℝ) (31388417647/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0350).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^2*thetaFirstMode x) ≤ (16115389025505733/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/128:ℝ) (59/256:ℝ) (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_059 :
    (8031980385078221/2516582400000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (59/256:ℝ) (15/64:ℝ) (2527917/10875904:ℝ) (756235795601/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0356).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^2*thetaFirstMode x) ≤ (21421519466005049/6710886400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (59/256:ℝ) (15/64:ℝ) (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_060 :
    (2666816266794927/838860800000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/64:ℝ) (61/256:ℝ) (2657523/11244544:ℝ) (728571969801/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0362).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^2*thetaFirstMode x) ≤ (2133747862860211/671088640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/64:ℝ) (61/256:ℝ) (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_061 :
    (497639848960121/157286400000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (61/256:ℝ) (31/128:ℝ) (2791485/11619328:ℝ) (43856512643/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0368).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^2*thetaFirstMode x) ≤ (1592671757310517/503316480000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (61/256:ℝ) (31/128:ℝ) (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_062 :
    (15835128401291753/5033164800000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/128:ℝ) (63/256:ℝ) (2929875/12000256:ℝ) (1351235463887/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0374).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^2*thetaFirstMode x) ≤ (63349601187795391/20132659200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/128:ℝ) (63/256:ℝ) (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_2_063 :
    (15733305133642511/5033164800000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (63/256:ℝ) (1/4:ℝ) (3072765/12387328:ℝ) (1300595613263/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0380).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_2_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^2*thetaFirstMode x) ≤ (15735604933979359/5033164800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (63/256:ℝ) (1/4:ℝ) (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

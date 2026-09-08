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

theorem thetaFirstMode_refined_cell_lower_8_032 :
    (41672600378624438778424039/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(33/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/8:ℝ) (33/256:ℝ) (730222341159285/5748281504317952:ℝ) (3711782621959/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0197).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^8*thetaFirstMode x) ≤ (27783968676470589102034733/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/8:ℝ) (33/256:ℝ) (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_033 :
    (51540156469786056003412117/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (33/256:ℝ)..(17/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (33/256:ℝ) (17/128:ℝ) (4795188919157943/36622101413148160:ℝ) (3602818939147/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0203).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^8*thetaFirstMode x) ≤ (6872584875990491758784369/566683977944357425643520000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (33/256:ℝ) (17/128:ℝ) (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_034 :
    (21092042290750794259596061/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(35/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (17/128:ℝ) (35/256:ℝ) (6247526395102641/46332533517852160:ℝ) (3496180167453/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0209).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^8*thetaFirstMode x) ≤ (632814245908712268960513067/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (17/128:ℝ) (35/256:ℝ) (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_035 :
    (77145169379051123653794371/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (35/256:ℝ)..(9/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (35/256:ℝ) (9/64:ℝ) (8078499778926159/58225454071144960:ℝ) (3391843597631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0215).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^8*thetaFirstMode x) ≤ (128586262902320432716513247/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (35/256:ℝ) (9/64:ℝ) (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_036 :
    (93435788395295889195201913/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(37/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (9/64:ℝ) (37/256:ℝ) (10371833391193857/72708564804252160:ℝ) (3289785996133/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0221).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^8*thetaFirstMode x) ≤ (155739879210897168256917911/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (9/64:ℝ) (37/256:ℝ) (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_037 :
    (112460835971147865867619451/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (37/256:ℝ)..(19/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (37/256:ℝ) (19/128:ℝ) (2645329456026675/18050233071498752:ℝ) (3189983630081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0227).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^8*thetaFirstMode x) ≤ (3124189657346059602974929/118059162071741130342400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (37/256:ℝ) (19/128:ℝ) (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_038 :
    (13455784731695815082856943/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(39/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (19/128:ℝ) (39/256:ℝ) (16759748134830393/111391385333532160:ℝ) (309241229113/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0233).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^8*thetaFirstMode x) ≤ (336425099862088559567149657/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (19/128:ℝ) (39/256:ℝ) (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_039 :
    (32017839431181404168975423/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (39/256:ℝ)..(5/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (39/256:ℝ) (5/32:ℝ) (21108185233275591/136744035433576960:ℝ) (599409463703/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0239).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^8*thetaFirstMode x) ≤ (400259977311528778196857039/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (39/256:ℝ) (5/32:ℝ) (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_040 :
    (63147354806018055207040567/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(41/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (5/32:ℝ) (41/256:ℝ) (26432093791371609/167009112048540160:ℝ) (2903863621341/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0245).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^8*thetaFirstMode x) ≤ (118412448104443882859975323/2656331146614175432704000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (5/32:ℝ) (41/256:ℝ) (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_041 :
    (27878524261611045841157539/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (41/256:ℝ)..(21/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (41/256:ℝ) (21/128:ℝ) (32917849303728807/202980990606108160:ℝ) (351604462549/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0251).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^8*thetaFirstMode x) ≤ (2230496264325670575207310771/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (41/256:ℝ) (21/128:ℝ) (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_042 :
    (261283446490068800788224451/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(43/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (21/128:ℝ) (43/256:ℝ) (8156311544891565/49111668780733952:ℝ) (2723937669481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0257).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^8*thetaFirstMode x) ≤ (522618098540868512450075813/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (21/128:ℝ) (43/256:ℝ) (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_043 :
    (304667125722892445475235637/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (43/256:ℝ)..(11/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (43/256:ℝ) (11/64:ℝ) (50272907626205343/295754822586012160:ℝ) (2637143276417/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0263).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^8*thetaFirstMode x) ≤ (30469756582303129030989701/425012983458268069232640000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (43/256:ℝ) (11/64:ℝ) (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_044 :
    (117887026968298675838363483/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(45/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (11/64:ℝ) (45/256:ℝ) (61679411798377041/354710535855669760:ℝ) (2552425923669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0269).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^8*thetaFirstMode x) ≤ (1768485541650915791407512161/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (11/64:ℝ) (45/256:ℝ) (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_045 :
    (204384287662344030225909193/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (45/256:ℝ)..(23/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (45/256:ℝ) (23/128:ℝ) (75331067100848559/423704371432783360:ℝ) (1234879344403/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0275).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^8*thetaFirstMode x) ≤ (817622060784115594538887163/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (45/256:ℝ) (23/128:ℝ) (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_046 :
    (78418820117873984862508187/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(47/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (23/128:ℝ) (47/256:ℝ) (91605462777481257/504167194710300160:ℝ) (1194557172351/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0281).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^8*thetaFirstMode x) ≤ (1568542471666808214305220881/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (23/128:ℝ) (47/256:ℝ) (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_047 :
    (539435875593520980686026681/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (47/256:ℝ)..(3/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (47/256:ℝ) (3/16:ℝ) (22186673770886955/119539193595863552:ℝ) (2310465379561/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0287).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^8*thetaFirstMode x) ≤ (1078988211315928276867334693/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (47/256:ℝ) (3/16:ℝ) (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_048 :
    (102682634805910877101060691/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(49/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (3/16:ℝ) (49/256:ℝ) (133804837701602793/706068831528348160:ℝ) (1116892008393/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0293).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^8*thetaFirstMode x) ≤ (616163605092446377555861819/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (3/16:ℝ) (49/256:ℝ) (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_049 :
    (233688543734305614392808553/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (49/256:ℝ)..(25/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (49/256:ℝ) (25/128:ℝ) (160775853321491991/831261189349250560:ℝ) (2159042234709/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0299).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^8*thetaFirstMode x) ≤ (1168573786731796060605806051/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (49/256:ℝ) (25/128:ℝ) (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_050 :
    (794930500094505584661239591/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(51/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (25/128:ℝ) (51/256:ℝ) (192475564448517009/975462843111554560:ℝ) (2086211786141/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0305).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^8*thetaFirstMode x) ≤ (883357104002612853857069783/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (25/128:ℝ) (51/256:ℝ) (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_051 :
    (449142652198666365252373381/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (51/256:ℝ)..(13/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (51/256:ℝ) (13/64:ℝ) (229614139092996207/1141096218995868160:ℝ) (1007632108921/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0311).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^8*thetaFirstMode x) ≤ (2994633322396564359981989131/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (51/256:ℝ) (13/64:ℝ) (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_052 :
    (1011731938481509580506567799/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(53/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (13/64:ℝ) (53/256:ℝ) (54598255949620845/266167146581207552:ℝ) (1946170889819/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0317).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^8*thetaFirstMode x) ≤ (674568081478441597389736667/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (13/64:ℝ) (53/256:ℝ) (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_053 :
    (378625458771574971654972659/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (53/256:ℝ)..(27/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (53/256:ℝ) (27/128:ℝ) (323505440094667743/1547628340508700160:ℝ) (1878902994507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0323).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^8*thetaFirstMode x) ≤ (1893356498238154467172136909/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (53/256:ℝ) (27/128:ℝ) (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_054 :
    (79457847411039351353797159/265633114661417543270400000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(55/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (27/128:ℝ) (55/256:ℝ) (382163785687980441/1794715319477839360:ℝ) (113339473489/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0329).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^8*thetaFirstMode x) ≤ (1059568692359288628405289639/3541774862152233910272000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (27/128:ℝ) (55/256:ℝ) (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_055 :
    (31526313499010035924882921/94447329657392904273920000000000000:ℝ) ≤ ∫ x in (55/256:ℝ)..(7/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (55/256:ℝ) (7/32:ℝ) (450092942792761959/2075655332250933760:ℝ) (349945509609/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0335).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^8*thetaFirstMode x) ≤ (7094312558141269925562646733/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (55/256:ℝ) (7/32:ℝ) (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_056 :
    (1578550885641505213901036609/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(57/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (7/32:ℝ) (57/256:ℝ) (528550581246993657/2394348818532252160:ℝ) (1687761714569/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0341).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^8*thetaFirstMode x) ≤ (175417020414035052832125117/472236648286964521369600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (7/32:ℝ) (57/256:ℝ) (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_057 :
    (875757708801313905363781621/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (57/256:ℝ)..(29/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (57/256:ℝ) (29/128:ℝ) (123787575796526235/551012753541565952:ℝ) (813752393251/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0347).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^8*thetaFirstMode x) ≤ (72989339968027516994280859/177088743107611695513600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (57/256:ℝ) (29/128:ℝ) (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_058 :
    (193815419281658180674211177/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(59/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (29/128:ℝ) (59/256:ℝ) (722812917611120193/3162462922265628160:ℝ) (156892740107/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0353).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^8*thetaFirstMode x) ≤ (1938412122936804018670771369/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (29/128:ℝ) (59/256:ℝ) (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_059 :
    (534756718016254299092747987/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (59/256:ℝ)..(15/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (59/256:ℝ) (15/64:ℝ) (841905060294227391/3621632464243356160:ℝ) (378000034967/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0359).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^8*thetaFirstMode x) ≤ (7131056460899582237164553087/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (59/256:ℝ) (15/64:ℝ) (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_060 :
    (2354672419131947177540220169/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(61/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (15/64:ℝ) (61/256:ℝ) (978130364965943409/4138112237655400960:ℝ) (1456693546909/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0365).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^8*thetaFirstMode x) ≤ (52333283968484289931672189/94447329657392904273920000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (15/64:ℝ) (61/256:ℝ) (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_061 :
    (17237367875800783937968273/28334198897217871282176000000000000:ℝ) ≤ ∫ x in (61/256:ℝ)..(31/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (61/256:ℝ) (31/128:ℝ) (1133608087849118607/4717927560779292160:ℝ) (28059562929/2000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0371).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^8*thetaFirstMode x) ≤ (646492301820209125052114923/1062532458645670173081600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (61/256:ℝ) (31/128:ℝ) (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_062 :
    (118012955987557191520464817/177088743107611695513600000000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(63/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (31/128:ℝ) (63/256:ℝ) (262135666824211125/1073524536622218752:ℝ) (168853057581/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0377).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^8*thetaFirstMode x) ≤ (5665434462503674808037462797/8500259669165361384652800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (31/128:ℝ) (63/256:ℝ) (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_063 :
    (1547621490588948222595456831/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (63/256:ℝ)..(1/4:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (63/256:ℝ) (1/4:ℝ) (1511920914525505143/6094295942728092160:ℝ) (650101513471/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0383).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^8*thetaFirstMode x) ≤ (619139070562750395209068829/850025966916536138465280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (63/256:ℝ) (1/4:ℝ) (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

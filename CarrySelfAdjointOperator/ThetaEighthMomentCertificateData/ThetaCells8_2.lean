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

theorem thetaFirstMode_refined_cell_lower_8_064 :
    (93744948224530987334795747/118059162071741130342400000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (1/4:ℝ) (65/256:ℝ) (1740175468704392841/6905636680726120960:ℝ) (312771103803/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0389).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^8*thetaFirstMode x) ≤ (5625534410289665065748211919/7083549724304467820544000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (1/4:ℝ) (65/256:ℝ) (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_065 :
    (611902157652258110413657639/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (65/256:ℝ) (33/128:ℝ) (1998562918031146359/7809963970327836160:ℝ) (601719622347/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0395).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^8*thetaFirstMode x) ≤ (12239899615414137446784769211/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (65/256:ℝ) (33/128:ℝ) (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_066 :
    (1992679924373806897206088333/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (33/128:ℝ) (67/256:ℝ) (2290508312768691057/8816267219187228160:ℝ) (578619100303/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0401).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^8*thetaFirstMode x) ≤ (1328658581698444643514436189/1416709944860893564108800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (33/128:ℝ) (67/256:ℝ) (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_067 :
    (863388698552669169198475963/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (67/256:ℝ) (17/64:ℝ) (523953028089808515/1986849740868925952:ℝ) (222490410103/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0407).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^8*thetaFirstMode x) ≤ (1727049246709200509734563769/1700051933833072276930560000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (67/256:ℝ) (17/64:ℝ) (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_068 :
    (2333198588135739082730642251/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (17/64:ℝ) (69/256:ℝ) (2990441164477942593/11174368100215452160:ℝ) (534525830191/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0413).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^8*thetaFirstMode x) ≤ (46671455402331064832035563667/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (17/64:ℝ) (69/256:ℝ) (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_069 :
    (2516949722354019702819319841/2125064917291340346163200000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (69/256:ℝ) (35/128:ℝ) (3407025864107161791/12547889060924853760:ℝ) (513504005171/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0419).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^8*thetaFirstMode x) ≤ (12586804508274784022526599557/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (69/256:ℝ) (35/128:ℝ) (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_070 :
    (5419570869938104909843944689/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (35/128:ℝ) (71/256:ℝ) (3874419549088930809/14066927919229519360:ℝ) (986292210119/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0425).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^8*thetaFirstMode x) ≤ (54204727194211681442938045691/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (35/128:ℝ) (71/256:ℝ) (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_071 :
    (5823471037196637564237728111/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (71/256:ℝ) (9/32:ℝ) (4397964224531456007/15744504565196700160:ℝ) (946875514151/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0431).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^8*thetaFirstMode x) ≤ (1213428773601786833311922239/885443715538058477568000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (71/256:ℝ) (9/32:ℝ) (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_072 :
    (1249119152690581941385976749/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (9/32:ℝ) (73/256:ℝ) (996695256742326405/3518919113747927552:ℝ) (181745867269/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0437).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^8*thetaFirstMode x) ≤ (4164449358758349405365250887/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (9/32:ℝ) (73/256:ℝ) (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_073 :
    (6685874570398229480751978923/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (73/256:ℝ) (37/128:ℝ) (5637281108870877543/19632189611037468160:ℝ) (871825264493/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0443).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^8*thetaFirstMode x) ≤ (1044851601158084679881166577/664082786653543858176000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (73/256:ℝ) (37/128:ℝ) (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_074 :
    (893021054207632457661527339/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (37/128:ℝ) (75/256:ℝ) (6366249662322494241/21873345290796674560:ℝ) (104516884289/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0449).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^8*thetaFirstMode x) ≤ (992423325377531544172119057/590295810358705651712000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (37/128:ℝ) (75/256:ℝ) (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_075 :
    (846696425415155852919742269/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (75/256:ℝ) (19/64:ℝ) (7177837152534081759/24335251372240130560:ℝ) (801630743121/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0455).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^8*thetaFirstMode x) ≤ (3175690757651236432727963603/1770887431076116955136000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (75/256:ℝ) (19/64:ℝ) (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_076 :
    (2028472773038567951176165319/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (19/64:ℝ) (77/256:ℝ) (8080123862216333457/27036289542638748160:ℝ) (192071115779/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0461).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^8*thetaFirstMode x) ≤ (81153984212448742679011609147/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (19/64:ℝ) (77/256:ℝ) (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_077 :
    (2874894371727153515853350219/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (77/256:ℝ) (39/128:ℝ) (1816371645569997795/5999219949625943552:ℝ) (736068654267/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0467).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^8*thetaFirstMode x) ≤ (958479427009767188581165411/472236648286964521369600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (77/256:ℝ) (39/128:ℝ) (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_078 :
    (3050738128313401979321967889/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (39/128:ℝ) (79/256:ℝ) (10192502262515829993/33235648177494300160:ℝ) (704955976797/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0473).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^8*thetaFirstMode x) ≤ (10171086400111255599184034453/4722366482869645213696000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (39/128:ℝ) (79/256:ℝ) (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_079 :
    (1615996731045251042195088329/708354972430446782054400000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (79/256:ℝ) (5/16:ℝ) (11422279416358375191/36777297964497103360:ℝ) (337459671627/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0479).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^8*thetaFirstMode x) ≤ (96978828334384410892352522407/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (79/256:ℝ) (5/16:ℝ) (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_080 :
    (569744520849459821597743951/236118324143482260684800000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (5/16:ℝ) (81/256:ℝ) (12782224971512359209/40644882680317749760:ℝ) (322965965079/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0485).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^8*thetaFirstMode x) ≤ (10257450481373588665856466901/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (5/16:ℝ) (81/256:ℝ) (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_081 :
    (10829822533572399976055266153/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (81/256:ℝ) (41/128:ℝ) (14284239070852168407/44863782688534812160:ℝ) (617967189223/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0491).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^8*thetaFirstMode x) ≤ (108320260319012465149568965981/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (81/256:ℝ) (41/128:ℝ) (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_082 :
    (190308575157314704942147499/70835497243044678205440000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (41/128:ℝ) (83/256:ℝ) (3188228496497630685/9892200887210173952:ℝ) (29549942907/5000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0497).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^8*thetaFirstMode x) ≤ (7613920175140578101615883251/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (41/128:ℝ) (83/256:ℝ) (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_083 :
    (4006891450198525420545966953/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (83/256:ℝ) (21/64:ℝ) (17766735204530144943/54465262754276508160:ℝ) (565000970919/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0503).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^8*thetaFirstMode x) ≤ (60116051661841597273359758737/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (83/256:ℝ) (21/64:ℝ) (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_084 :
    (1263542683007219589195372119/425012983458268069232640000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (21/64:ℝ) (85/256:ℝ) (19775858017267564641/59907066245820060160:ℝ) (53994786779/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0509).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^8*thetaFirstMode x) ≤ (63190705523561955198496311523/21250649172913403461632000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (21/64:ℝ) (85/256:ℝ) (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_085 :
    (4420608721428379223876551601/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (85/256:ℝ) (43/128:ℝ) (21984457092577248159/65818805832858856960:ℝ) (515814204633/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0515).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^8*thetaFirstMode x) ≤ (132647268659478581555427053879/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (85/256:ℝ) (43/128:ℝ) (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_086 :
    (13898858121195442217224429691/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (43/128:ℝ) (87/256:ℝ) (24409651773064480857/72234846544296732160:ℝ) (492574961981/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0521).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^8*thetaFirstMode x) ≤ (46339844769889887284969651293/14167099448608935641088000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (43/128:ℝ) (87/256:ℝ) (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_087 :
    (3636360627915091704103510543/1062532458645670173081600000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (87/256:ℝ) (11/32:ℝ) (5413961127233958075/15838324523948298752:ℝ) (117551363383/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0527).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^8*thetaFirstMode x) ≤ (9699160422510547354014790847/2833419889721787128217600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (87/256:ℝ) (11/32:ℝ) (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_088 :
    (3040087211412761187868778723/850025966916536138465280000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (11/32:ℝ) (89/256:ℝ) (29984600961233742393/86727736009265052160:ℝ) (89736266843/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0533).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^8*thetaFirstMode x) ≤ (3040789038784782564685018141/850025966916536138465280000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (11/32:ℝ) (89/256:ℝ) (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_089 :
    (528754520750009838672094063/141670994486089356410880000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (89/256:ℝ) (45/128:ℝ) (33175116720304347591/94884058348837864960:ℝ) (42797860779/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0539).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^8*thetaFirstMode x) ≤ (158663639484624659386937536033/42501298345826806923264000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (89/256:ℝ) (45/128:ℝ) (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_090 :
    (16530781802475651127351286903/4250129834582680692326400000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (45/128:ℝ) (91/256:ℝ) (36663910216296708609/103703836492258332160:ℝ) (408073633973/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0545).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^8*thetaFirstMode x) ≤ (41336843591564535860441936941/10625324586456701730816000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (45/128:ℝ) (91/256:ℝ) (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_091 :
    (5734520948233264968995121961/1416709944860893564108800000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (91/256:ℝ) (23/64:ℝ) (40475102494972215807/113232801681326748160:ℝ) (388943135103/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0551).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^8*thetaFirstMode x) ≤ (17207753822581698952803785753/4250129834582680692326400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (91/256:ℝ) (23/64:ℝ) (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_092 :
    (1986624321560028405729830839/472236648286964521369600000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (23/64:ℝ) (93/256:ℝ) (8926893532018987965/24703856487388477952:ℝ) (370564202331/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0557).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^8*thetaFirstMode x) ≤ (4471013284641031750284566167/1062532458645670173081600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (23/64:ℝ) (93/256:ℝ) (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_093 :
    (193307776434367933866783629/44272185776902923878400000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (93/256:ℝ) (47/128:ℝ) (49169526224045867343/134614321254731292160:ℝ) (11028571917/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0563).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^8*thetaFirstMode x) ≤ (2900348723359655427013696849/664082786653543858176000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (93/256:ℝ) (47/128:ℝ) (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_094 :
    (1602991969209860297166188699/354177486215223391027200000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (47/128:ℝ) (95/256:ℝ) (54109642629131284041/146571795189741237760:ℝ) (83992819407/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0569).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^8*thetaFirstMode x) ≤ (16034039647808628725392636253/3541774862152233910272000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (47/128:ℝ) (95/256:ℝ) (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_8_095 :
    (2489151797053556884013498317/531266229322835086540800000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^8*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 8 (95/256:ℝ) (3/8:ℝ) (59486127077809925559/159448540415669455360:ℝ) (39964170157/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0575).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_8_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^8*thetaFirstMode x) ≤ (24898030477902910291795108619/5312662293228350865408000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 8 (95/256:ℝ) (3/8:ℝ) (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

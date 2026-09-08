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

theorem thetaFirstMode_refined_cell_lower_6_064 :
    (630836460543489355598389/50440315826549555200000000000000:ℝ) ≤ ∫ x in (1/4:ℝ)..(65/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (1/4:ℝ) (65/256:ℝ) (260188853259783/1032563465259008:ℝ) (1251209358709/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0388).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_064 :
    (∫ x in (1/4:ℝ)..(65/256:ℝ), x^6*thetaFirstMode x) ≤ (15773260042076725078059/1261007895663738880000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/4:ℝ) (65/256:ℝ) (1275971452837/100000000000000:ℝ) (1227570184781/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0384).2 (thetaFirstMode_refined_node_0390).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_065 :
    (332743512007032533305043/25220157913274777600000000000000:ℝ) ≤ ∫ x in (65/256:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (65/256:ℝ) (33/128:ℝ) (289770553653497/1132406395762688:ℝ) (601779286253/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0394).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_065 :
    (∫ x in (65/256:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x) ≤ (5324703885022869426223307/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (65/256:ℝ) (33/128:ℝ) (1227570184781/100000000000000:ℝ) (9223661601/781250000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0390).2 (thetaFirstMode_refined_node_0396).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_066 :
    (700835643874517784690789/50440315826549555200000000000000:ℝ) ≤ ∫ x in (33/128:ℝ)..(67/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (33/128:ℝ) (67/256:ℝ) (322189499008615/1240168251938816:ℝ) (1157352154767/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0400).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_066 :
    (∫ x in (33/128:ℝ)..(67/256:ℝ), x^6*thetaFirstMode x) ≤ (2803775843661799311792769/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (33/128:ℝ) (67/256:ℝ) (9223661601/781250000000:ℝ) (567558816199/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0396).2 (thetaFirstMode_refined_node_0402).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_067 :
    (184205926790109060891007/12610078956637388800000000000000:ℝ) ≤ ∫ x in (67/256:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (67/256:ℝ) (17/64:ℝ) (357668934677145/1356343732447232:ℝ) (278140215523/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0406).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_067 :
    (∫ x in (67/256:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x) ≤ (168443363869047157856479/11529215046068469760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (67/256:ℝ) (17/64:ℝ) (567558816199/50000000000000:ℝ) (1091007799227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0402).2 (thetaFirstMode_refined_node_0408).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_068 :
    (773389099514498827121659/50440315826549555200000000000000:ℝ) ≤ ∫ x in (17/64:ℝ)..(69/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (17/64:ℝ) (69/256:ℝ) (396445943426855/1481450361153536:ℝ) (1069155550087/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0412).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_068 :
    (∫ x in (17/64:ℝ)..(69/256:ℝ), x^6*thetaFirstMode x) ≤ (1237621025157354966233711/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/64:ℝ) (69/256:ℝ) (1091007799227/100000000000000:ℝ) (65516879131/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0408).2 (thetaFirstMode_refined_node_0414).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_069 :
    (810466399993021533250359/50440315826549555200000000000000:ℝ) ≤ ∫ x in (69/256:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (69/256:ℝ) (35/128:ℝ) (438772078999513/1616029178697728:ℝ) (1027107189069/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0418).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_069 :
    (∫ x in (69/256:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x) ≤ (231599660518141764434387/14411518807585587200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (69/256:ℝ) (35/128:ℝ) (65516879131/6250000000000:ℝ) (251718859441/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0414).2 (thetaFirstMode_refined_node_0420).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_070 :
    (24228202647407539385961/1441151880758558720000000000000:ℝ) ≤ ∫ x in (35/128:ℝ)..(71/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (35/128:ℝ) (71/256:ℝ) (484914018720327/1760645444384768:ℝ) (197277375897/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0424).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_070 :
    (∫ x in (35/128:ℝ)..(71/256:ℝ), x^6*thetaFirstMode x) ≤ (193857877416684376655483/11529215046068469760000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (35/128:ℝ) (71/256:ℝ) (251718859441/25000000000000:ℝ) (966795058203/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0420).2 (thetaFirstMode_refined_node_0426).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_071 :
    (885879793852536762400811/50440315826549555200000000000000:ℝ) ≤ ∫ x in (71/256:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (71/256:ℝ) (9/32:ℝ) (535154235440825/1915889348397056:ℝ) (946965866963/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0430).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_071 :
    (∫ x in (71/256:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x) ≤ (3544119844470400531777461/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (71/256:ℝ) (9/32:ℝ) (966795058203/100000000000000:ℝ) (928000225389/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0426).2 (thetaFirstMode_refined_node_0432).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_072 :
    (924070494054730571045967/50440315826549555200000000000000:ℝ) ≤ ∫ x in (9/32:ℝ)..(73/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (9/32:ℝ) (73/256:ℝ) (589791689097415/2082376734328832:ℝ) (908815557063/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0436).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_072 :
    (∫ x in (9/32:ℝ)..(73/256:ℝ), x^6*thetaFirstMode x) ≤ (1056262904995002073027383/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/32:ℝ) (73/256:ℝ) (928000225389/100000000000000:ℝ) (222615601443/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0432).2 (thetaFirstMode_refined_node_0438).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_073 :
    (962482813082264820650207/50440315826549555200000000000000:ℝ) ≤ ∫ x in (73/256:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (73/256:ℝ) (37/128:ℝ) (649142538167865/2260749832042496:ℝ) (871907529641/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0442).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_073 :
    (∫ x in (73/256:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x) ≤ (962652071992654088862163/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (73/256:ℝ) (37/128:ℝ) (222615601443/25000000000000:ℝ) (213538312097/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0438).2 (thetaFirstMode_refined_node_0444).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_074 :
    (250259566847617813334071/12610078956637388800000000000000:ℝ) ≤ ∫ x in (37/128:ℝ)..(75/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (37/128:ℝ) (75/256:ℝ) (713540871307943/2451678000846848:ℝ) (209053388221/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0448).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_074 :
    (∫ x in (37/128:ℝ)..(75/256:ℝ), x^6*thetaFirstMode x) ≤ (500608781509002526650833/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (37/128:ℝ) (75/256:ℝ) (213538312097/25000000000000:ℝ) (204761149653/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0444).2 (thetaFirstMode_refined_node_0450).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_075 :
    (129957068511282233537917/6305039478318694400000000000000:ℝ) ≤ ∫ x in (75/256:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (75/256:ℝ) (19/64:ℝ) (783339459450457/2655858482997248:ℝ) (100213199617/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0454).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_075 :
    (∫ x in (75/256:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x) ≤ (8123798437467552001983/394064967394918400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (75/256:ℝ) (19/64:ℝ) (204761149653/25000000000000:ℝ) (39255425577/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0450).2 (thetaFirstMode_refined_node_0456).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_076 :
    (1078255808379295559027937/50440315826549555200000000000000:ℝ) ≤ ∫ x in (19/64:ℝ)..(77/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (19/64:ℝ) (77/256:ℝ) (858910528648935/2874017167517696:ℝ) (768355847181/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0460).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_076 :
    (∫ x in (19/64:ℝ)..(77/256:ℝ), x^6*thetaFirstMode x) ≤ (8627649031057297034111309/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/64:ℝ) (77/256:ℝ) (39255425577/5000000000000:ℝ) (752317264991/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0456).2 (thetaFirstMode_refined_node_0462).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_077 :
    (1116752958865069628464133/50440315826549555200000000000000:ℝ) ≤ ∫ x in (77/256:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (77/256:ℝ) (39/128:ℝ) (940646553948185/3106909364344832:ℝ) (736136717087/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0466).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_077 :
    (∫ x in (77/256:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x) ≤ (2233928503759921055343077/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (77/256:ℝ) (39/128:ℝ) (752317264991/100000000000000:ℝ) (720643372107/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0462).2 (thetaFirstMode_refined_node_0468).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_078 :
    (1155063969423259122061701/50440315826549555200000000000000:ℝ) ≤ ∫ x in (39/128:ℝ)..(79/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (39/128:ℝ) (79/256:ℝ) (1028961074563975/3355320588793856:ℝ) (705020860683/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0472).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_078 :
    (∫ x in (39/128:ℝ)..(79/256:ℝ), x^6*thetaFirstMode x) ≤ (1848458446824365671182653/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (39/128:ℝ) (79/256:ℝ) (720643372107/100000000000000:ℝ) (345029796773/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0468).2 (thetaFirstMode_refined_node_0474).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_079 :
    (42610863430557732436239/1801439850948198400000000000000:ℝ) ≤ ∫ x in (79/256:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (79/256:ℝ) (5/16:ℝ) (1124289530654073/3620067356346368:ℝ) (168745296153/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0478).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_079 :
    (∫ x in (79/256:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x) ≤ (1909341257996241278103511/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (79/256:ℝ) (5/16:ℝ) (345029796773/50000000000000:ℝ) (660538949293/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0474).2 (thetaFirstMode_refined_node_0480).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_080 :
    (615394295626745861179719/25220157913274777600000000000000:ℝ) ≤ ∫ x in (5/16:ℝ)..(81/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (5/16:ℝ) (81/256:ℝ) (1227090121962887/3901997987760128:ℝ) (322995429879/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0484).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_080 :
    (∫ x in (5/16:ℝ)..(81/256:ℝ), x^6*thetaFirstMode x) ≤ (1231034523347975266906303/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/16:ℝ) (81/256:ℝ) (660538949293/100000000000000:ℝ) (632054730013/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0480).2 (thetaFirstMode_refined_node_0486).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_081 :
    (181147459482919526619851/7205759403792793600000000000000:ℝ) ≤ ∫ x in (81/256:ℝ)..(41/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (81/256:ℝ) (41/128:ℝ) (1337844688621945/4201993424500736:ℝ) (618023332451/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0490).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_081 :
    (∫ x in (81/256:ℝ)..(41/128:ℝ), x^6*thetaFirstMode x) ≤ (405852873208100034096111/16140901064495857664000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (81/256:ℝ) (41/128:ℝ) (632054730013/100000000000000:ℝ) (151145126999/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0486).2 (thetaFirstMode_refined_node_0492).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_082 :
    (1304750354565588615718301/50440315826549555200000000000000:ℝ) ≤ ∫ x in (41/128:ℝ)..(83/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (41/128:ℝ) (83/256:ℝ) (1457059614388455/4520968054495232:ℝ) (591052335239/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0496).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_082 :
    (∫ x in (41/128:ℝ)..(83/256:ℝ), x^6*thetaFirstMode x) ≤ (10440165530736314936653143/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (41/128:ℝ) (83/256:ℝ) (151145126999/25000000000000:ℝ) (578090147677/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0492).2 (thetaFirstMode_refined_node_0498).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_083 :
    (268171784519923392432831/10088063165309911040000000000000:ℝ) ≤ ∫ x in (83/256:ℝ)..(21/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (83/256:ℝ) (21/64:ℝ) (1585266752604185/4859870548207616:ℝ) (113010379443/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0502).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_083 :
    (∫ x in (83/256:ℝ)..(21/64:ℝ), x^6*thetaFirstMode x) ≤ (670570906187771130168603/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (83/256:ℝ) (21/64:ℝ) (578090147677/100000000000000:ℝ) (110511563137/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0498).2 (thetaFirstMode_refined_node_0504).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_084 :
    (12288167503348524806477/450359962737049600000000000000:ℝ) ≤ ∫ x in (21/64:ℝ)..(85/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (21/64:ℝ) (85/256:ℝ) (1723024375156903/5219684705036288:ℝ) (33749772119/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0508).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_084 :
    (∫ x in (21/64:ℝ)..(85/256:ℝ), x^6*thetaFirstMode x) ≤ (2753140830338147597137799/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/64:ℝ) (85/256:ℝ) (110511563137/20000000000000:ℝ) (527957990481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0504).2 (thetaFirstMode_refined_node_0510).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_085 :
    (352728984091113593119641/12610078956637388800000000000000:ℝ) ≤ ∫ x in (85/256:ℝ)..(43/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (85/256:ℝ) (43/128:ℝ) (1870918144726617/5601430310033408:ℝ) (128965089171/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0514).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_085 :
    (∫ x in (85/256:ℝ)..(43/128:ℝ), x^6*thetaFirstMode x) ≤ (451591856168291942276401/16140901064495857664000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (85/256:ℝ) (43/128:ℝ) (527957990481/100000000000000:ℝ) (252132735761/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0510).2 (thetaFirstMode_refined_node_0516).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_086 :
    (57788081912175102794577/2017612633061982208000000000000:ℝ) ≤ ∫ x in (43/128:ℝ)..(87/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (43/128:ℝ) (87/256:ℝ) (2029562110598855/6006164000946176:ℝ) (19704755271/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0520).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_086 :
    (∫ x in (43/128:ℝ)..(87/256:ℝ), x^6*thetaFirstMode x) ≤ (2312038075084486411887173/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (43/128:ℝ) (87/256:ℝ) (252132735761/50000000000000:ℝ) (481455387969/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0516).2 (thetaFirstMode_refined_node_0522).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_087 :
    (1477554514087294006201123/50440315826549555200000000000000:ℝ) ≤ ∫ x in (87/256:ℝ)..(11/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (87/256:ℝ) (11/32:ℝ) (2199599728327225/6434980145580032:ℝ) (470247238747/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0526).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_087 :
    (∫ x in (87/256:ℝ)..(11/32:ℝ), x^6*thetaFirstMode x) ≤ (11823116431883037024869231/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (87/256:ℝ) (11/32:ℝ) (481455387969/100000000000000:ℝ) (57437900869/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0522).2 (thetaFirstMode_refined_node_0528).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_088 :
    (150939686207780324025209/5044031582654955520000000000000:ℝ) ≤ ∫ x in (11/32:ℝ)..(89/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (11/32:ℝ) (89/256:ℝ) (2381704903527495/6889011729483776:ℝ) (44872107857/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0532).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_088 :
    (∫ x in (11/32:ℝ)..(89/256:ℝ), x^6*thetaFirstMode x) ≤ (6038981311281601135922531/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/32:ℝ) (89/256:ℝ) (57437900869/12500000000000:ℝ) (219192370681/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0528).2 (thetaFirstMode_refined_node_0534).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_089 :
    (1540155002080515935496497/50440315826549555200000000000000:ℝ) ≤ ∫ x in (89/256:ℝ)..(45/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (89/256:ℝ) (45/128:ℝ) (2576583060085433/7369431253956608:ℝ) (428016401207/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0538).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_089 :
    (∫ x in (89/256:ℝ)..(45/128:ℝ), x^6*thetaFirstMode x) ≤ (12324136056469903429042869/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (89/256:ℝ) (45/128:ℝ) (219192370681/50000000000000:ℝ) (16723046287/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0534).2 (thetaFirstMode_refined_node_0540).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_090 :
    (784878746600701284195739/25220157913274777600000000000000:ℝ) ≤ ∫ x in (45/128:ℝ)..(91/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (45/128:ℝ) (91/256:ℝ) (2784972233060647/7877451644377088:ℝ) (204054781369/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0544).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_090 :
    (∫ x in (45/128:ℝ)..(91/256:ℝ), x^6*thetaFirstMode x) ≤ (897218930418427564935153/28823037615171174400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (45/128:ℝ) (91/256:ℝ) (16723046287/4000000000000:ℝ) (398553980321/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0540).2 (thetaFirstMode_refined_node_0546).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_091 :
    (319627159379068538506717/10088063165309911040000000000000:ℝ) ≤ ∫ x in (91/256:ℝ)..(23/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (91/256:ℝ) (23/64:ℝ) (3007644186568665/8414327168854016:ℝ) (77795456401/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0550).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_091 :
    (∫ x in (91/256:ℝ)..(23/64:ℝ), x^6*thetaFirstMode x) ≤ (114180366387357052456933/3602879701896396800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (91/256:ℝ) (23/64:ℝ) (398553980321/100000000000000:ℝ) (379795103081/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0546).2 (thetaFirstMode_refined_node_0552).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_092 :
    (812612258852651223861927/25220157913274777600000000000000:ℝ) ≤ ∫ x in (23/64:ℝ)..(93/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (23/64:ℝ) (93/256:ℝ) (3245405556923495/8981354367199232:ℝ) (185298323403/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0556).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_092 :
    (∫ x in (23/64:ℝ)..(93/256:ℝ), x^6*thetaFirstMode x) ≤ (928930052016174014806839/28823037615171174400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/64:ℝ) (93/256:ℝ) (379795103081/100000000000000:ℝ) (72355358003/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0552).2 (thetaFirstMode_refined_node_0558).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_093 :
    (165096163006964391602227/5044031582654955520000000000000:ℝ) ≤ ∫ x in (93/256:ℝ)..(47/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (93/256:ℝ) (47/128:ℝ) (3499099021322905/9579872990222336:ℝ) (35294511961/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0562).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_093 :
    (∫ x in (93/256:ℝ)..(47/128:ℝ), x^6*thetaFirstMode x) ≤ (6605513850637841110110987/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (93/256:ℝ) (47/128:ℝ) (72355358003/20000000000000:ℝ) (344476683437/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0558).2 (thetaFirstMode_refined_node_0564).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_094 :
    (167528869031177489415191/5044031582654955520000000000000:ℝ) ≤ ∫ x in (47/128:ℝ)..(95/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (47/128:ℝ) (95/256:ℝ) (3769604492358663/10211266949347328:ℝ) (33600054281/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0568).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_094 :
    (∫ x in (47/128:ℝ)..(95/256:ℝ), x^6*thetaFirstMode x) ≤ (6702877100761070677285281/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (47/128:ℝ) (95/256:ℝ) (344476683437/100000000000000:ℝ) (327872808403/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0564).2 (thetaFirstMode_refined_node_0570).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_095 :
    (1698151032936479887999351/50440315826549555200000000000000:ℝ) ≤ ∫ x in (95/256:ℝ)..(3/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (95/256:ℝ) (3/8:ℝ) (4057840338633977/10876965276551168:ℝ) (319741143511/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0574).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_095 :
    (∫ x in (95/256:ℝ)..(3/8:ℝ), x^6*thetaFirstMode x) ≤ (1358876269694844596583077/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (95/256:ℝ) (3/8:ℝ) (327872808403/100000000000000:ℝ) (311943577261/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0570).2 (thetaFirstMode_refined_node_0576).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

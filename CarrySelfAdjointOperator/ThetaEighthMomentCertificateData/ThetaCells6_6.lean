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

theorem thetaFirstMode_refined_cell_lower_6_192 :
    (18844547310128979403917/12610078956637388800000000000000:ℝ) ≤ ∫ x in (3/4:ℝ)..(193/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (3/4:ℝ) (193/256:ℝ) (548559415042533895/729502937539807232:ℝ) (52904013/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1156).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_192 :
    (∫ x in (3/4:ℝ)..(193/256:ℝ), x^6*thetaFirstMode x) ≤ (603850434708979224936037/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/4:ℝ) (193/256:ℝ) (44690077/20000000000000:ℝ) (50120003/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1152).2 (thetaFirstMode_refined_node_1158).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_193 :
    (13946938081663566445849/10088063165309911040000000000000:ℝ) ≤ ∫ x in (193/256:ℝ)..(97/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (193/256:ℝ) (97/128:ℝ) (568820330690682105/752537778572097536:ℝ) (37956007/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1162).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_193 :
    (∫ x in (193/256:ℝ)..(97/128:ℝ), x^6*thetaFirstMode x) ≤ (111730678434587957074137/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (193/256:ℝ) (97/128:ℝ) (50120003/25000000000000:ℝ) (179715241/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1158).2 (thetaFirstMode_refined_node_1164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_194 :
    (8055914621077183560171/6305039478318694400000000000000:ℝ) ≤ ∫ x in (97/128:ℝ)..(195/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (97/128:ℝ) (195/256:ℝ) (589719320504220263/776175582409545728:ℝ) (21256161/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1168).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_194 :
    (∫ x in (97/128:ℝ)..(195/256:ℝ), x^6*thetaFirstMode x) ≤ (32269219683129813764097/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (97/128:ℝ) (195/256:ℝ) (179715241/100000000000000:ℝ) (257537/160000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1164).2 (thetaFirstMode_refined_node_1170).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_195 :
    (5949923033899685334381/5044031582654955520000000000000:ℝ) ≤ ∫ x in (195/256:ℝ)..(49/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (195/256:ℝ) (49/64:ℝ) (611273043037863577/800428910102816768:ℝ) (15223641/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1174).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_195 :
    (∫ x in (195/256:ℝ)..(49/64:ℝ), x^6*thetaFirstMode x) ≤ (476678052917188506302749/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (195/256:ℝ) (49/64:ℝ) (257537/160000000000:ℝ) (72018211/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1170).2 (thetaFirstMode_refined_node_1176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_196 :
    (54873936028130752727389/50440315826549555200000000000000:ℝ) ≤ ∫ x in (49/64:ℝ)..(197/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (49/64:ℝ) (197/256:ℝ) (633498502977313575/825310517945133056:ℝ) (136169137/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1180).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_196 :
    (∫ x in (49/64:ℝ)..(197/256:ℝ), x^6*thetaFirstMode x) ≤ (43963300576552709446217/40352252661239644160000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (49/64:ℝ) (197/256:ℝ) (72018211/50000000000000:ℝ) (32194371/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1176).2 (thetaFirstMode_refined_node_1182).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_197 :
    (3159707193065887798161/3152519739159347200000000000000:ℝ) ≤ ∫ x in (197/256:ℝ)..(99/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (197/256:ℝ) (99/128:ℝ) (656413056505416665/850833359485048832:ℝ) (7605579/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1186).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_197 :
    (∫ x in (197/256:ℝ)..(99/128:ℝ), x^6*thetaFirstMode x) ≤ (81008675054889892316507/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (197/256:ℝ) (99/128:ℝ) (32194371/25000000000000:ℝ) (115032211/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1182).2 (thetaFirstMode_refined_node_1188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_198 :
    (46527650872805344239083/50440315826549555200000000000000:ℝ) ≤ ∫ x in (99/128:ℝ)..(199/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (99/128:ℝ) (199/256:ℝ) (680034416723500615/877010587549546496:ℝ) (108651629/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1192).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_198 :
    (∫ x in (99/128:ℝ)..(199/256:ℝ), x^6*thetaFirstMode x) ≤ (372783380269569000358967/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (99/128:ℝ) (199/256:ℝ) (115032211/100000000000000:ℝ) (25665391/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1188).2 (thetaFirstMode_refined_node_1194).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_199 :
    (21387825900941808610979/25220157913274777600000000000000:ℝ) ≤ ∫ x in (199/256:ℝ)..(25/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (199/256:ℝ) (25/32:ℝ) (704380659128171193/903855556277454848:ℝ) (48461579/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1198).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_199 :
    (∫ x in (199/256:ℝ)..(25/32:ℝ), x^6*thetaFirstMode x) ≤ (48961519953500345492727/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (199/256:ℝ) (25/32:ℝ) (25665391/25000000000000:ℝ) (91538141/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1194).2 (thetaFirstMode_refined_node_1200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_200 :
    (1571378932889395205879/2017612633061982208000000000000:ℝ) ≤ ∫ x in (25/32:ℝ)..(201/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (25/32:ℝ) (201/256:ℝ) (729470227143851207/931381823163189248:ℝ) (3455279/4000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1204).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_200 :
    (∫ x in (25/32:ℝ)..(201/256:ℝ), x^6*thetaFirstMode x) ≤ (44966620250361126562079/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/32:ℝ) (201/256:ℝ) (91538141/100000000000000:ℝ) (20386329/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1200).2 (thetaFirstMode_refined_node_1206).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_201 :
    (18019867008742741825887/25220157913274777600000000000000:ℝ) ≤ ∫ x in (201/256:ℝ)..(101/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (201/256:ℝ) (101/128:ℝ) (755321937711344185/959603151110813696:ℝ) (38458281/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1210).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_201 :
    (∫ x in (201/256:ℝ)..(101/128:ℝ), x^6*thetaFirstMode x) ≤ (288775376393512742978401/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (201/256:ℝ) (101/128:ℝ) (20386329/25000000000000:ℝ) (72576421/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1206).2 (thetaFirstMode_refined_node_1212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_202 :
    (33027527728702595056289/50440315826549555200000000000000:ℝ) ≤ ∫ x in (101/128:ℝ)..(203/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (101/128:ℝ) (203/256:ℝ) (781954986932704935/988533510498424832:ℝ) (68424971/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1216).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_202 :
    (∫ x in (101/128:ℝ)..(203/256:ℝ), x^6*thetaFirstMode x) ≤ (66161610986875023527941/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (101/128:ℝ) (203/256:ℝ) (72576421/100000000000000:ℝ) (64533993/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1212).2 (thetaFirstMode_refined_node_1218).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_203 :
    (30234437462626064053709/50440315826549555200000000000000:ℝ) ≤ ∫ x in (203/256:ℝ)..(51/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (203/256:ℝ) (51/64:ℝ) (809388955772699225/1018187081252857856:ℝ) (60814097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1222).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_203 :
    (∫ x in (203/256:ℝ)..(51/64:ℝ), x^6*thetaFirstMode x) ≤ (242272144352187811921667/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (203/256:ℝ) (51/64:ℝ) (64533993/100000000000000:ℝ) (2866453/5000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1218).2 (thetaFirstMode_refined_node_1224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_204 :
    (5529507955033771204777/10088063165309911040000000000000:ℝ) ≤ ∫ x in (51/64:ℝ)..(205/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (51/64:ℝ) (205/256:ℝ) (837643815817134823/1048578254934714368:ℝ) (10799797/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1228).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_204 :
    (∫ x in (51/64:ℝ)..(205/256:ℝ), x^6*thetaFirstMode x) ≤ (221549037170237816641611/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (51/64:ℝ) (205/256:ℝ) (2866453/5000000000000:ℝ) (50880481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1224).2 (thetaFirstMode_refined_node_1230).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_205 :
    (6313603207159338105839/12610078956637388800000000000000:ℝ) ≤ ∫ x in (205/256:ℝ)..(103/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (205/256:ℝ) (103/128:ℝ) (866739935088346137/1079721636833712128:ℝ) (11975549/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1234).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_205 :
    (∫ x in (205/256:ℝ)..(103/128:ℝ), x^6*thetaFirstMode x) ≤ (202377689023256665415087/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (205/256:ℝ) (103/128:ℝ) (50880481/100000000000000:ℝ) (5639291/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1230).2 (thetaFirstMode_refined_node_1236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_206 :
    (23043138509764997096663/50440315826549555200000000000000:ℝ) ≤ ∫ x in (103/128:ℝ)..(207/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (103/128:ℝ) (207/256:ℝ) (896698083918114695/1111632048074356736:ℝ) (42453209/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1240).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_206 :
    (∫ x in (103/128:ℝ)..(207/256:ℝ), x^6*thetaFirstMode x) ≤ (184662689688836138748629/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (103/128:ℝ) (207/256:ℝ) (5639291/12500000000000:ℝ) (39963307/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1236).2 (thetaFirstMode_refined_node_1242).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_207 :
    (21002301550745938586567/50440315826549555200000000000000:ℝ) ≤ ∫ x in (207/256:ℝ)..(13/16:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (207/256:ℝ) (13/16:ℝ) (927539440878307705/1144324527731935232:ℝ) (37587863/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1246).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_207 :
    (∫ x in (207/256:ℝ)..(13/16:ℝ), x^6*thetaFirstMode x) ≤ (1314942654502501755583/3152519739159347200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (207/256:ℝ) (13/16:ℝ) (39963307/100000000000000:ℝ) (35366227/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1242).2 (thetaFirstMode_refined_node_1248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_208 :
    (682892495634678082991/1801439850948198400000000000000:ℝ) ≤ ∫ x in (13/16:ℝ)..(209/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (13/16:ℝ) (209/256:ℝ) (959285598769516935/1177814334958831616:ℝ) (8311961/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1252).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_208 :
    (∫ x in (13/16:ℝ)..(209/256:ℝ), x^6*thetaFirstMode x) ≤ (153240240661310686252409/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/16:ℝ) (209/256:ℝ) (35366227/100000000000000:ℝ) (15633749/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1248).2 (thetaFirstMode_refined_node_1254).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_209 :
    (8694394744034163392731/25220157913274777600000000000000:ℝ) ≤ ∫ x in (209/256:ℝ)..(105/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (209/256:ℝ) (105/128:ℝ) (991958570667980153/1212116951121164288:ℝ) (14690101/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1258).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_209 :
    (∫ x in (209/256:ℝ)..(105/128:ℝ), x^6*thetaFirstMode x) ≤ (34840515492074896069929/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (209/256:ℝ) (105/128:ℝ) (15633749/50000000000000:ℝ) (2761667/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1254).2 (thetaFirstMode_refined_node_1260).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_210 :
    (7897889711940208922663/25220157913274777600000000000000:ℝ) ≤ ∫ x in (105/128:ℝ)..(211/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (105/128:ℝ) (211/256:ℝ) (1025580796031067367/1247248081945745408:ℝ) (12968453/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1264).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_210 :
    (∫ x in (105/128:ℝ)..(211/256:ℝ), x^6*thetaFirstMode x) ≤ (31649674736982580342611/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (105/128:ℝ) (211/256:ℝ) (2761667/10000000000000:ℝ) (12184001/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1260).2 (thetaFirstMode_refined_node_1266).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_211 :
    (14332524932059230154747/50440315826549555200000000000000:ℝ) ≤ ∫ x in (211/256:ℝ)..(53/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (211/256:ℝ) (53/64:ℝ) (1060175146861614105/1283223659677362176:ℝ) (22874431/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1270).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_211 :
    (∫ x in (211/256:ℝ)..(53/64:ℝ), x^6*thetaFirstMode x) ≤ (7179663582554340793333/25220157913274777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (211/256:ℝ) (53/64:ℝ) (12184001/50000000000000:ℝ) (10740033/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1266).2 (thetaFirstMode_refined_node_1272).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_212 :
    (405939672908815146237/1576259869579673600000000000000:ℝ) ≤ ∫ x in (53/64:ℝ)..(213/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (53/64:ℝ) (213/256:ℝ) (1095764933931383975/1320059845246380032:ℝ) (629793/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1276).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_212 :
    (∫ x in (53/64:ℝ)..(213/256:ℝ), x^6*thetaFirstMode x) ≤ (104118101328929289610251/403522526612396441600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (53/64:ℝ) (213/256:ℝ) (10740033/50000000000000:ℝ) (151323/800000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1272).2 (thetaFirstMode_refined_node_1278).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_213 :
    (5879961410645561610711/25220157913274777600000000000000:ℝ) ≤ ∫ x in (213/256:ℝ)..(107/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (213/256:ℝ) (107/128:ℝ) (1132373913063942745/1357773030446667776:ℝ) (8869053/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1282).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_213 :
    (∫ x in (213/256:ℝ)..(107/128:ℝ), x^6*thetaFirstMode x) ≤ (1683235322147453557739/7205759403792793600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (213/256:ℝ) (107/128:ℝ) (151323/800000000000:ℝ) (16640047/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1278).2 (thetaFirstMode_refined_node_1284).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_214 :
    (10634053626114538029001/50440315826549555200000000000000:ℝ) ≤ ∫ x in (107/128:ℝ)..(215/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (107/128:ℝ) (215/256:ℝ) (1170026291477226183/1396379840123844608:ℝ) (15596431/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1288).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_214 :
    (∫ x in (107/128:ℝ)..(215/256:ℝ), x^6*thetaFirstMode x) ≤ (10654941689339130131967/50440315826549555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (107/128:ℝ) (215/256:ℝ) (16640047/100000000000000:ℝ) (14623487/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1284).2 (thetaFirstMode_refined_node_1290).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_215 :
    (9604873684197396332857/50440315826549555200000000000000:ℝ) ≤ ∫ x in (215/256:ℝ)..(27/32:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (215/256:ℝ) (27/32:ℝ) (1208746734186083897/1435897134373849088:ℝ) (13699297/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1294).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_215 :
    (∫ x in (215/256:ℝ)..(27/32:ℝ), x^6*thetaFirstMode x) ≤ (38496204822813242347973/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (215/256:ℝ) (27/32:ℝ) (14623487/100000000000000:ℝ) (12838097/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1290).2 (thetaFirstMode_refined_node_1296).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_216 :
    (8665225794590072985253/50440315826549555200000000000000:ℝ) ≤ ∫ x in (27/32:ℝ)..(217/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (27/32:ℝ) (217/256:ℝ) (1248560370465081415/1476342010751830016:ℝ) (12020509/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1300).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_216 :
    (∫ x in (27/32:ℝ)..(217/256:ℝ), x^6*thetaFirstMode x) ≤ (1736562601983071560919/10088063165309911040000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/32:ℝ) (217/256:ℝ) (12838097/100000000000000:ℝ) (11259009/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1296).2 (thetaFirstMode_refined_node_1302).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_217 :
    (48802340162536855227/315251973915934720000000000000:ℝ) ≤ ∫ x in (217/256:ℝ)..(109/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (217/256:ℝ) (109/128:ℝ) (1289492800371842745/1517731806491359232:ℝ) (65853/625000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1306).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_217 :
    (∫ x in (217/256:ℝ)..(109/128:ℝ), x^6*thetaFirstMode x) ≤ (31297932425353680628139/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (217/256:ℝ) (109/128:ℝ) (11259009/100000000000000:ℝ) (9863839/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1302).2 (thetaFirstMode_refined_node_1308).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_218 :
    (27453061965991900773/197032483697459200000000000000:ℝ) ≤ ∫ x in (109/128:ℝ)..(219/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (109/128:ℝ) (219/256:ℝ) (1331570101331215655/1560084100733966336:ℝ) (36039/390625000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1312).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_218 :
    (∫ x in (109/128:ℝ)..(219/256:ℝ), x^6*thetaFirstMode x) ≤ (14085443628123718969031/100880631653099110400000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (109/128:ℝ) (219/256:ℝ) (9863839/100000000000000:ℝ) (8632459/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1308).2 (thetaFirstMode_refined_node_1314).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_219 :
    (6318110903356072792089/50440315826549555200000000000000:ℝ) ≤ ∫ x in (219/256:ℝ)..(55/64:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (219/256:ℝ) (55/64:ℝ) (1374818834780541913/1603416716768995328:ℝ) (8069949/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1318).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_219 :
    (∫ x in (219/256:ℝ)..(55/64:ℝ), x^6*thetaFirstMode x) ≤ (25326314613582859147561/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (219/256:ℝ) (55/64:ℝ) (8632459/100000000000000:ℝ) (7546789/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1314).2 (thetaFirstMode_refined_node_1320).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_220 :
    (1418296439984310868033/12610078956637388800000000000000:ℝ) ≤ ∫ x in (55/64:ℝ)..(221/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (55/64:ℝ) (221/256:ℝ) (1419266052876314727/1647747724283783168:ℝ) (1762813/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1324).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_220 :
    (∫ x in (55/64:ℝ)..(221/256:ℝ), x^6*thetaFirstMode x) ≤ (9096765044986176471793/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (55/64:ℝ) (221/256:ℝ) (7546789/100000000000000:ℝ) (411913/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1320).2 (thetaFirstMode_refined_node_1326).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_221 :
    (5087997333987907416739/50440315826549555200000000000000:ℝ) ≤ ∫ x in (221/256:ℝ)..(111/128:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (221/256:ℝ) (111/128:ℝ) (1464939305262505625/1693095441624160256:ℝ) (6154537/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1330).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_221 :
    (∫ x in (221/256:ℝ)..(111/128:ℝ), x^6*thetaFirstMode x) ≤ (20396813644080212037911/201761263306198220800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (221/256:ℝ) (111/128:ℝ) (411913/6250000000000:ℝ) (2874687/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1326).2 (thetaFirstMode_refined_node_1332).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_222 :
    (142427441308948992151/1576259869579673600000000000000:ℝ) ≤ ∫ x in (111/128:ℝ)..(223/256:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (111/128:ℝ) (223/256:ℝ) (1511866645900843015/1739478438065272832:ℝ) (167689/3125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1336).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_222 :
    (∫ x in (111/128:ℝ)..(223/256:ℝ), x^6*thetaFirstMode x) ≤ (7308610503129841638307/80704505322479288320000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (111/128:ℝ) (223/256:ℝ) (2874687/50000000000000:ℝ) (5010071/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1332).2 (thetaFirstMode_refined_node_1338).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_6_223 :
    (4077689774839858830629/50440315826549555200000000000000:ℝ) ≤ ∫ x in (223/256:ℝ)..(7/8:ℝ), x^6*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 6 (223/256:ℝ) (7/8:ℝ) (1560076639963324665/1786915536092727296:ℝ) (4673477/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_1342).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_6_223 :
    (∫ x in (223/256:ℝ)..(7/8:ℝ), x^6*thetaFirstMode x) ≤ (4670821298562459580983/57646075230342348800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (223/256:ℝ) (7/8:ℝ) (5010071/100000000000000:ℝ) (136283/3125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_1338).2 (thetaFirstMode_refined_node_1344).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

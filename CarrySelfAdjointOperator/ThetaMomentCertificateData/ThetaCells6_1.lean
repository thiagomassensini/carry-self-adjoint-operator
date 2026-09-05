import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes00
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes01
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes02
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes03
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes04
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes05
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes06
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes07
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes08
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes09
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes10
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes11
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes12
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes13
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes14
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes15
import CarrySelfAdjointOperator.ThetaMomentCertificateData.ThetaNodes16
import CarrySelfAdjointOperator.CompletedNativeThetaFirstModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaFirstMode_cell_upper_6_032 :
    (∫ x in (1/4:ℝ)..(33/128:ℝ), x^6*thetaFirstMode x) ≤ (810564965471302910959/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (1/4:ℝ) (33/128:ℝ) (12759714529/1000000000000:ℝ) (236125737/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_128).2 (thetaFirstMode_node_132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_033 :
    (∫ x in (33/128:ℝ)..(17/64:ℝ), x^6*thetaFirstMode x) ≤ (16052762915345697253/562949953421312000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (33/128:ℝ) (17/64:ℝ) (236125737/20000000000:ℝ) (5455038997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_132).2 (thetaFirstMode_node_136).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_034 :
    (∫ x in (17/64:ℝ)..(35/128:ℝ), x^6*thetaFirstMode x) ≤ (990387205055902266247/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (17/64:ℝ) (35/128:ℝ) (5455038997/500000000000:ℝ) (10068754379/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_136).2 (thetaFirstMode_node_140).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_035 :
    (∫ x in (35/128:ℝ)..(9/32:ℝ), x^6*thetaFirstMode x) ≤ (1084209273223305961821/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (35/128:ℝ) (9/32:ℝ) (10068754379/1000000000000:ℝ) (580000141/62500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_140).2 (thetaFirstMode_node_144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_036 :
    (∫ x in (9/32:ℝ)..(37/128:ℝ), x^6*thetaFirstMode x) ≤ (589854126533689799773/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (9/32:ℝ) (37/128:ℝ) (580000141/62500000000:ℝ) (4270766243/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_144).2 (thetaFirstMode_node_148).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_037 :
    (∫ x in (37/128:ℝ)..(19/64:ℝ), x^6*thetaFirstMode x) ≤ (638060783248383591011/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (37/128:ℝ) (19/64:ℝ) (4270766243/500000000000:ℝ) (1962771279/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_148).2 (thetaFirstMode_node_152).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_038 :
    (∫ x in (19/64:ℝ)..(39/128:ℝ), x^6*thetaFirstMode x) ≤ (686323690619280862809/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (19/64:ℝ) (39/128:ℝ) (1962771279/250000000000:ℝ) (3603216861/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_152).2 (thetaFirstMode_node_156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_039 :
    (∫ x in (39/128:ℝ)..(5/16:ℝ), x^6*thetaFirstMode x) ≤ (367114015524350953107/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (39/128:ℝ) (5/16:ℝ) (3603216861/500000000000:ℝ) (3302694747/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_156).2 (thetaFirstMode_node_160).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_040 :
    (∫ x in (5/16:ℝ)..(41/128:ℝ), x^6*thetaFirstMode x) ≤ (1562702199183808405861/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (5/16:ℝ) (41/128:ℝ) (3302694747/500000000000:ℝ) (6045805081/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_160).2 (thetaFirstMode_node_164).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_041 :
    (∫ x in (41/128:ℝ)..(21/64:ℝ), x^6*thetaFirstMode x) ≤ (827268489310867822279/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (41/128:ℝ) (21/64:ℝ) (6045805081/1000000000000:ℝ) (5525578159/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_164).2 (thetaFirstMode_node_168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_042 :
    (∫ x in (21/64:ℝ)..(43/128:ℝ), x^6*thetaFirstMode x) ≤ (348624130786057984279/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (21/64:ℝ) (43/128:ℝ) (5525578159/1000000000000:ℝ) (1260663679/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_168).2 (thetaFirstMode_node_172).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_043 :
    (∫ x in (43/128:ℝ)..(11/32:ℝ), x^6*thetaFirstMode x) ≤ (1827634883276622369931/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (43/128:ℝ) (11/32:ℝ) (1260663679/250000000000:ℝ) (4595032071/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_172).2 (thetaFirstMode_node_176).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_044 :
    (∫ x in (11/32:ℝ)..(45/128:ℝ), x^6*thetaFirstMode x) ≤ (1907294697364299995939/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (11/32:ℝ) (45/128:ℝ) (4595032071/1000000000000:ℝ) (1045190393/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_176).2 (thetaFirstMode_node_180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_045 :
    (∫ x in (45/128:ℝ)..(23/64:ℝ), x^6*thetaFirstMode x) ≤ (495339969780437823309/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (45/128:ℝ) (23/64:ℝ) (1045190393/250000000000:ℝ) (474743879/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_180).2 (thetaFirstMode_node_184).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_046 :
    (∫ x in (23/64:ℝ)..(47/128:ℝ), x^6*thetaFirstMode x) ≤ (512286387344767097737/7881299347898368000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (23/64:ℝ) (47/128:ℝ) (474743879/125000000000:ℝ) (861191709/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_184).2 (thetaFirstMode_node_188).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_047 :
    (∫ x in (47/128:ℝ)..(3/8:ℝ), x^6*thetaFirstMode x) ≤ (2110031770349933234089/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (47/128:ℝ) (3/8:ℝ) (861191709/250000000000:ℝ) (3119435773/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_188).2 (thetaFirstMode_node_192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_048 :
    (∫ x in (3/8:ℝ)..(49/128:ℝ), x^6*thetaFirstMode x) ≤ (2163472010847298620039/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (3/8:ℝ) (49/128:ℝ) (3119435773/1000000000000:ℝ) (1410123283/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_192).2 (thetaFirstMode_node_196).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_049 :
    (∫ x in (49/128:ℝ)..(25/64:ℝ), x^6*thetaFirstMode x) ≤ (441800065168982638291/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (49/128:ℝ) (25/64:ℝ) (1410123283/500000000000:ℝ) (2545551093/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_196).2 (thetaFirstMode_node_200).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_050 :
    (∫ x in (25/64:ℝ)..(51/128:ℝ), x^6*thetaFirstMode x) ≤ (160445510666709694921/2251799813685248000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (25/64:ℝ) (51/128:ℝ) (2545551093/1000000000000:ℝ) (2293765343/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_200).2 (thetaFirstMode_node_204).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_051 :
    (∫ x in (51/128:ℝ)..(13/32:ℝ), x^6*thetaFirstMode x) ≤ (18199148956582284871/252201579132747776000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (51/128:ℝ) (13/32:ℝ) (2293765343/1000000000000:ℝ) (1031685033/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_204).2 (thetaFirstMode_node_208).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_052 :
    (∫ x in (13/32:ℝ)..(53/128:ℝ), x^6*thetaFirstMode x) ≤ (2294774385734075110461/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (13/32:ℝ) (53/128:ℝ) (1031685033/500000000000:ℝ) (370582233/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_208).2 (thetaFirstMode_node_212).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_053 :
    (∫ x in (53/128:ℝ)..(27/64:ℝ), x^6*thetaFirstMode x) ≤ (82349245793840029161/1125899906842624000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (53/128:ℝ) (27/64:ℝ) (370582233/200000000000:ℝ) (1660999809/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_212).2 (thetaFirstMode_node_216).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_054 :
    (∫ x in (27/64:ℝ)..(55/128:ℝ), x^6*thetaFirstMode x) ≤ (2307901079280904359431/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (27/64:ℝ) (55/128:ℝ) (1660999809/1000000000000:ℝ) (743156149/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_216).2 (thetaFirstMode_node_220).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_055 :
    (∫ x in (55/128:ℝ)..(7/16:ℝ), x^6*thetaFirstMode x) ≤ (1150613878210347497739/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (55/128:ℝ) (7/16:ℝ) (743156149/500000000000:ℝ) (16594871/12500000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_220).2 (thetaFirstMode_node_224).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_056 :
    (∫ x in (7/16:ℝ)..(57/128:ℝ), x^6*thetaFirstMode x) ≤ (2285935366041157620661/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (7/16:ℝ) (57/128:ℝ) (16594871/12500000000:ℝ) (1183637139/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_224).2 (thetaFirstMode_node_228).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_057 :
    (∫ x in (57/128:ℝ)..(29/64:ℝ), x^6*thetaFirstMode x) ≤ (323183654804639685319/4503599627370496000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (57/128:ℝ) (29/64:ℝ) (1183637139/1000000000000:ℝ) (263330791/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_228).2 (thetaFirstMode_node_232).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_058 :
    (∫ x in (29/64:ℝ)..(59/128:ℝ), x^6*thetaFirstMode x) ≤ (278827457670841554781/3940649673949184000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (29/64:ℝ) (59/128:ℝ) (263330791/250000000000:ℝ) (233894629/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_232).2 (thetaFirstMode_node_236).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_059 :
    (∫ x in (59/128:ℝ)..(15/32:ℝ), x^6*thetaFirstMode x) ≤ (1095675860728616332229/15762598695796736000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (59/128:ℝ) (15/32:ℝ) (233894629/250000000000:ℝ) (414697503/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_236).2 (thetaFirstMode_node_240).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_060 :
    (∫ x in (15/32:ℝ)..(61/128:ℝ), x^6*thetaFirstMode x) ≤ (428992229593382358319/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (15/32:ℝ) (61/128:ℝ) (414697503/500000000000:ℝ) (733824107/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_240).2 (thetaFirstMode_node_244).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_061 :
    (∫ x in (61/128:ℝ)..(31/64:ℝ), x^6*thetaFirstMode x) ≤ (16735873896353097693/252201579132747776000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (61/128:ℝ) (31/64:ℝ) (733824107/1000000000000:ℝ) (161993851/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_244).2 (thetaFirstMode_node_248).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_062 :
    (∫ x in (31/64:ℝ)..(63/128:ℝ), x^6*thetaFirstMode x) ≤ (406601055604068364593/6305039478318694400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (31/64:ℝ) (63/128:ℝ) (161993851/250000000000:ℝ) (571014911/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_248).2 (thetaFirstMode_node_252).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_6_063 :
    (∫ x in (63/128:ℝ)..(1/2:ℝ), x^6*thetaFirstMode x) ≤ (1968647248907420707897/31525197391593472000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 6 (63/128:ℝ) (1/2:ℝ) (571014911/1000000000000:ℝ) (7846301/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_252).2 (thetaFirstMode_node_256).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

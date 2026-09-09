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

theorem thetaFirstMode_refined_cell_lower_4_000 :
    (8481032229137/549755813888000000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (0/1:ℝ) (1/256:ℝ) (5/1536:ℝ) (8481032229137/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0003).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_000 :
    (∫ x in (0/1:ℝ)..(1/256:ℝ), x^4*thetaFirstMode x) ≤ (8481231955537/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (0/1:ℝ) (1/256:ℝ) (1080348662699/12500000000000:ℝ) (4224460243163/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0000).2 (thetaFirstMode_refined_node_0006).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_001 :
    (257798211802787/549755813888000000000000000:ℝ) ≤ ∫ x in (1/256:ℝ)..(1/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/256:ℝ) (1/128:ℝ) (105/15872:ℝ) (8316071348477/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0009).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_001 :
    (∫ x in (1/256:ℝ)..(1/128:ℝ), x^4*thetaFirstMode x) ≤ (128903769625593/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/256:ℝ) (1/128:ℝ) (4224460243163/50000000000000:ℝ) (4128902200723/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0006).2 (thetaFirstMode_refined_node_0012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_002 :
    (429357880678299/137438953472000000000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(3/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/128:ℝ) (3/256:ℝ) (3325/324096:ℝ) (2034871472409/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0015).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_002 :
    (∫ x in (1/128:ℝ)..(3/256:ℝ), x^4*thetaFirstMode x) ≤ (5152503531893411/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/128:ℝ) (3/256:ℝ) (4128902200723/50000000000000:ℝ) (504339973353/6250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0012).2 (thetaFirstMode_refined_node_0018).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_003 :
    (3108028846685499/274877906944000000000000000:ℝ) ≤ ∫ x in (3/256:ℝ)..(1/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/256:ℝ) (1/64:ℝ) (16835/1199616:ℝ) (3979550379879/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0021).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_003 :
    (∫ x in (3/256:ℝ)..(1/64:ℝ), x^4*thetaFirstMode x) ≤ (37297938652976603/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/256:ℝ) (1/64:ℝ) (504339973353/6250000000000:ℝ) (7883823733123/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0018).2 (thetaFirstMode_refined_node_0024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_004 :
    (16343107411644519/549755813888000000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(5/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/64:ℝ) (5/256:ℝ) (19215/1075712:ℝ) (7778727944619/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0027).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_004 :
    (∫ x in (1/64:ℝ)..(5/256:ℝ), x^4*thetaFirstMode x) ≤ (32687659437675661/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/64:ℝ) (5/256:ℝ) (7883823733123/100000000000000:ℝ) (1925238454167/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0024).2 (thetaFirstMode_refined_node_0030).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_005 :
    (35346446372903943/549755813888000000000000000:ℝ) ≤ ∫ x in (5/256:ℝ)..(3/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/256:ℝ) (3/128:ℝ) (155155/7143936:ℝ) (7599751961493/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0033).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_005 :
    (∫ x in (5/256:ℝ)..(3/128:ℝ), x^4*thetaFirstMode x) ≤ (35348053270744743/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/256:ℝ) (3/128:ℝ) (1925238454167/25000000000000:ℝ) (3760412985663/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0030).2 (thetaFirstMode_refined_node_0036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_006 :
    (13406993155530909/109951162777600000000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(7/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/128:ℝ) (7/256:ℝ) (354965/13871616:ℝ) (1484552447739/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0039).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_006 :
    (∫ x in (3/128:ℝ)..(7/256:ℝ), x^4*thetaFirstMode x) ≤ (26815236643355653/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/128:ℝ) (7/256:ℝ) (3760412985663/50000000000000:ℝ) (7343435558517/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0036).2 (thetaFirstMode_refined_node_0042).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_007 :
    (28921513640952339/137438953472000000000000000:ℝ) ≤ ∫ x in (7/256:ℝ)..(1/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/256:ℝ) (1/32:ℝ) (240825/8172032:ℝ) (1812011380299/25000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0045).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_007 :
    (∫ x in (7/256:ℝ)..(1/32:ℝ), x^4*thetaFirstMode x) ≤ (14461447427212111/68719476736000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/256:ℝ) (1/32:ℝ) (7343435558517/100000000000000:ℝ) (7168777158679/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0042).2 (thetaFirstMode_refined_node_0048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_008 :
    (185957919206205769/549755813888000000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(9/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/32:ℝ) (9/256:ℝ) (1346485/40367616:ℝ) (7075755078049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0051).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_008 :
    (∫ x in (1/32:ℝ)..(9/256:ℝ), x^4*thetaFirstMode x) ≤ (557901020673361829/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/32:ℝ) (9/256:ℝ) (7168777158679/100000000000000:ℝ) (6996844576391/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0048).2 (thetaFirstMode_refined_node_0054).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_009 :
    (282806710545490863/549755813888000000000000000:ℝ) ≤ ∫ x in (9/256:ℝ)..(5/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/256:ℝ) (5/128:ℝ) (2342795/62900736:ℝ) (6905978133513/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0057).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_009 :
    (∫ x in (9/256:ℝ)..(5/128:ℝ), x^4*thetaFirstMode x) ≤ (282820845257151913/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/256:ℝ) (5/128:ℝ) (6996844576391/100000000000000:ℝ) (6827630845943/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0054).2 (thetaFirstMode_refined_node_0060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_010 :
    (82281682164566961/109951162777600000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(11/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/128:ℝ) (11/256:ℝ) (1285935/31258112:ℝ) (1347753225411/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0063).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_010 :
    (∫ x in (5/128:ℝ)..(11/256:ℝ), x^4*thetaFirstMode x) ≤ (822858864724903991/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/128:ℝ) (11/256:ℝ) (6827630845943/100000000000000:ℝ) (666112823751/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0060).2 (thetaFirstMode_refined_node_0066).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_011 :
    (288542713973242813/274877906944000000000000000:ℝ) ≤ ∫ x in (11/256:ℝ)..(3/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/256:ℝ) (3/64:ℝ) (6072115/134831616:ℝ) (3287074810873/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0069).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_011 :
    (∫ x in (11/256:ℝ)..(3/64:ℝ), x^4*thetaFirstMode x) ≤ (288557782665155937/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/256:ℝ) (3/64:ℝ) (666112823751/10000000000000:ℝ) (3248664131823/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0066).2 (thetaFirstMode_refined_node_0072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_012 :
    (785237837968086459/549755813888000000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(13/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/64:ℝ) (13/256:ℝ) (9204125/188100096:ℝ) (6412146217719/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0075).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_012 :
    (∫ x in (3/64:ℝ)..(13/256:ℝ), x^4*thetaFirstMode x) ≤ (4711678447695178333/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/64:ℝ) (13/256:ℝ) (3248664131823/50000000000000:ℝ) (1267244337271/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0072).2 (thetaFirstMode_refined_node_0078).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_013 :
    (520639605429256547/274877906944000000000000000:ℝ) ≤ ∫ x in (13/256:ℝ)..(7/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/256:ℝ) (7/128:ℝ) (4504545/85263872:ℝ) (3126382507937/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0081).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_013 :
    (∫ x in (13/256:ℝ)..(7/128:ℝ), x^4*thetaFirstMode x) ≤ (1041335981230526959/549755813888000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/256:ℝ) (7/128:ℝ) (1267244337271/20000000000000:ℝ) (6177798524727/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0078).2 (thetaFirstMode_refined_node_0084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_014 :
    (1350576948951163219/549755813888000000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(15/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/128:ℝ) (15/256:ℝ) (19305445/340302336:ℝ) (6096009266269/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0087).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_014 :
    (∫ x in (7/128:ℝ)..(15/256:ℝ), x^4*thetaFirstMode x) ≤ (1012989124863622943/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/128:ℝ) (15/256:ℝ) (6177798524727/100000000000000:ℝ) (6022048062889/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0084).2 (thetaFirstMode_refined_node_0090).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_015 :
    (343679412355140389/109951162777600000000000000:ℝ) ≤ ∫ x in (15/256:ℝ)..(1/16:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/256:ℝ) (1/16:ℝ) (26932955/444212736:ℝ) (1188375601589/20000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0093).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_015 :
    (∫ x in (15/256:ℝ)..(1/16:ℝ), x^4*thetaFirstMode x) ≤ (3436989622694035973/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/256:ℝ) (1/16:ℝ) (6022048062889/100000000000000:ℝ) (2934479429249/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0090).2 (thetaFirstMode_refined_node_0096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_016 :
    (268731661960211697/68719476736000000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(17/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (1/16:ℝ) (17/256:ℝ) (12267255/190095872:ℝ) (723795890337/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0099).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_016 :
    (∫ x in (1/16:ℝ)..(17/256:ℝ), x^4*thetaFirstMode x) ≤ (1074989095230093447/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (1/16:ℝ) (17/256:ℝ) (2934479429249/50000000000000:ℝ) (2859259375861/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0096).2 (thetaFirstMode_refined_node_0102).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_017 :
    (2649860531379256899/549755813888000000000000000:ℝ) ≤ ∫ x in (17/256:ℝ)..(9/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (17/256:ℝ) (9/128:ℝ) (49373275/721476096:ℝ) (5641470034509/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0105).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_017 :
    (∫ x in (17/256:ℝ)..(9/128:ℝ), x^4*thetaFirstMode x) ≤ (15900106403769647143/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (17/256:ℝ) (9/128:ℝ) (2859259375861/50000000000000:ℝ) (5570714874669/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0102).2 (thetaFirstMode_refined_node_0108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_018 :
    (3223092357481418411/549755813888000000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(19/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (9/128:ℝ) (19/256:ℝ) (65168285/900911616:ℝ) (5495178187481/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0111).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_018 :
    (∫ x in (9/128:ℝ)..(19/256:ℝ), x^4*thetaFirstMode x) ≤ (3867945118256830741/659706976665600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (9/128:ℝ) (19/256:ℝ) (5570714874669/100000000000000:ℝ) (1356383415313/25000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0108).2 (thetaFirstMode_refined_node_0114).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_019 :
    (3873942723309620269/549755813888000000000000000:ℝ) ≤ ∫ x in (19/256:ℝ)..(5/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (19/256:ℝ) (5/64:ℝ) (28256865/370637312:ℝ) (5351481381169/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0117).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_019 :
    (∫ x in (19/256:ℝ)..(5/64:ℝ), x^4*thetaFirstMode x) ≤ (1549672927093955293/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (19/256:ℝ) (5/64:ℝ) (1356383415313/25000000000000:ℝ) (1056592171499/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0114).2 (thetaFirstMode_refined_node_0120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_020 :
    (4606491569767486889/549755813888000000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(21/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (5/64:ℝ) (21/256:ℝ) (108830605/1357979136:ℝ) (5210368011989/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0123).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_020 :
    (∫ x in (5/64:ℝ)..(21/256:ℝ), x^4*thetaFirstMode x) ≤ (2764069458012852361/329853488332800000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (5/64:ℝ) (21/256:ℝ) (1056592171499/20000000000000:ℝ) (5142981532319/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0120).2 (thetaFirstMode_refined_node_0126).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_021 :
    (542447433243102321/54975581388800000000000000:ℝ) ≤ ∫ x in (21/256:ℝ)..(11/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (21/256:ℝ) (11/128:ℝ) (138068915/1642799616:ℝ) (507182525091/10000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0129).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_021 :
    (∫ x in (21/256:ℝ)..(11/128:ℝ), x^4*thetaFirstMode x) ≤ (4068617984430915253/412316860416000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (21/256:ℝ) (11/128:ℝ) (5142981532319/100000000000000:ℝ) (5005580088729/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0126).2 (thetaFirstMode_refined_node_0132).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_022 :
    (6331255206980597231/549755813888000000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(23/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (11/128:ℝ) (23/256:ℝ) (57759975/656748032:ℝ) (4935839177321/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0135).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_022 :
    (∫ x in (11/128:ℝ)..(23/256:ℝ), x^4*thetaFirstMode x) ≤ (3165835888645272531/274877906944000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (11/128:ℝ) (23/256:ℝ) (5005580088729/100000000000000:ℝ) (194829611019/4000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0132).2 (thetaFirstMode_refined_node_0138).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_023 :
    (916225507936518019/68719476736000000000000000:ℝ) ≤ ∫ x in (23/256:ℝ)..(3/32:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (23/256:ℝ) (3/32:ℝ) (215335435/2344367616:ℝ) (600299360299/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0141).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_023 :
    (∫ x in (23/256:ℝ)..(3/32:ℝ), x^4*thetaFirstMode x) ≤ (1466059263083821221/109951162777600000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (23/256:ℝ) (3/32:ℝ) (194829611019/4000000000000:ℝ) (947689039803/20000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0138).2 (thetaFirstMode_refined_node_0144).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_024 :
    (1052834611464741791/68719476736000000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(25/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (3/32:ℝ) (25/256:ℝ) (265188245/2769409536:ℝ) (583934568791/12500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0147).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_024 :
    (∫ x in (3/32:ℝ)..(25/256:ℝ), x^4*thetaFirstMode x) ≤ (25269762620105538343/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (3/32:ℝ) (25/256:ℝ) (947689039803/20000000000000:ℝ) (4608677336011/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0144).2 (thetaFirstMode_refined_node_0150).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_025 :
    (9611999656976871253/549755813888000000000000000:ℝ) ≤ ∫ x in (25/256:ℝ)..(13/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (25/256:ℝ) (13/128:ℝ) (107958585/1083264512:ℝ) (4543067524003/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0153).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_025 :
    (∫ x in (25/256:ℝ)..(13/128:ℝ), x^4*thetaFirstMode x) ≤ (19225344077913157577/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (25/256:ℝ) (13/128:ℝ) (4608677336011/100000000000000:ℝ) (560177318273/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0150).2 (thetaFirstMode_refined_node_0156).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_026 :
    (10899455442348044671/549755813888000000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(27/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (13/128:ℝ) (27/256:ℝ) (392523565/3790127616:ℝ) (4417150358941/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0159).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_026 :
    (∫ x in (13/128:ℝ)..(27/256:ℝ), x^4*thetaFirstMode x) ≤ (65401401084278800691/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (13/128:ℝ) (27/256:ℝ) (560177318273/12500000000000:ℝ) (4356650085507/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0156).2 (thetaFirstMode_refined_node_0162).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_027 :
    (95986521489737893/4294967296000000000000000:ℝ) ≤ ∫ x in (27/256:ℝ)..(7/64:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (27/256:ℝ) (7/64:ℝ) (472349075/4395204096:ℝ) (33544584913/781250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0165).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_027 :
    (∫ x in (27/256:ℝ)..(7/64:ℝ), x^4*thetaFirstMode x) ≤ (73723018480778309729/3298534883328000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (27/256:ℝ) (7/64:ℝ) (4356650085507/100000000000000:ℝ) (2117176309913/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0162).2 (thetaFirstMode_refined_node_0168).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_028 :
    (13773228836663993961/549755813888000000000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(29/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (7/64:ℝ) (29/256:ℝ) (188221695/1689999872:ℝ) (4172718164781/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0171).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_028 :
    (∫ x in (7/64:ℝ)..(29/256:ℝ), x^4*thetaFirstMode x) ≤ (3443563148542612631/137438953472000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (7/64:ℝ) (29/256:ℝ) (2117176309913/50000000000000:ℝ) (411450623883/10000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0168).2 (thetaFirstMode_refined_node_0174).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_029 :
    (7680312968734529233/274877906944000000000000000:ℝ) ≤ ∫ x in (29/256:ℝ)..(15/128:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (29/256:ℝ) (15/128:ℝ) (670883395/5819675136:ℝ) (2027082344683/50000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0177).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_029 :
    (∫ x in (29/256:ℝ)..(15/128:ℝ), x^4*thetaFirstMode x) ≤ (46085372648704621987/1649267441664000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (29/256:ℝ) (15/128:ℝ) (411450623883/10000000000000:ℝ) (499636308793/12500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0174).2 (thetaFirstMode_refined_node_0180).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_030 :
    (1065519391764961631/34359738368000000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(31/256:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (15/128:ℝ) (31/256:ℝ) (792518405/6649575936:ℝ) (246126640481/6250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0183).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_030 :
    (∫ x in (15/128:ℝ)..(31/256:ℝ), x^4*thetaFirstMode x) ≤ (34099258803983933763/1099511627776000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (15/128:ℝ) (31/256:ℝ) (499636308793/12500000000000:ℝ) (3882084295049/100000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0180).2 (thetaFirstMode_refined_node_0186).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_lower_4_031 :
    (18835663646725172663/549755813888000000000000000:ℝ) ≤ ∫ x in (31/256:ℝ)..(1/8:ℝ), x^4*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 4 (31/256:ℝ) (1/8:ℝ) (310396905/2521743872:ℝ) (3824282035223/100000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_refined_node_0189).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_refined_cell_upper_4_031 :
    (∫ x in (31/256:ℝ)..(1/8:ℝ), x^4*thetaFirstMode x) ≤ (7534860209803524953/219902325555200000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 4 (31/256:ℝ) (1/8:ℝ) (3882084295049/100000000000000:ℝ) (1884733080709/50000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_refined_node_0186).2 (thetaFirstMode_refined_node_0192).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

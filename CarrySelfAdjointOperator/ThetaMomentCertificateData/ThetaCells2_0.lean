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

theorem thetaFirstMode_cell_lower_2_000 :
    (13921683289/1048576000000000000:ℝ) ≤ ∫ x in (0/1:ℝ)..(1/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (0/1:ℝ) (1/128:ℝ) (3/512:ℝ) (41765049867/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_002).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_000 :
    (∫ x in (0/1:ℝ)..(1/128:ℝ), x^2*thetaFirstMode x) ≤ (111387341709/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (0/1:ℝ) (1/128:ℝ) (10803486627/125000000000:ℝ) (82578044037/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_000).2 (thetaFirstMode_node_004).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_001 :
    (56205976309/629145600000000000:ℝ) ≤ ∫ x in (1/128:ℝ)..(1/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/128:ℝ) (1/64:ℝ) (45/3584:ℝ) (8029425187/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_006).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_001 :
    (∫ x in (1/128:ℝ)..(1/64:ℝ), x^2*thetaFirstMode x) ≤ (749536173153/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/128:ℝ) (1/64:ℝ) (82578044037/1000000000000:ℝ) (19709559339/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_004).2 (thetaFirstMode_node_008).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_002 :
    (364661690507/1572864000000000000:ℝ) ≤ ∫ x in (1/64:ℝ)..(3/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/64:ℝ) (3/128:ℝ) (195/9728:ℝ) (19192720553/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_010).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_002 :
    (∫ x in (1/64:ℝ)..(3/128:ℝ), x^2*thetaFirstMode x) ≤ (972602833437/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/64:ℝ) (3/128:ℝ) (19709559339/250000000000:ℝ) (37604129859/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_008).2 (thetaFirstMode_node_012).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_003 :
    (542182398617/1258291200000000000:ℝ) ≤ ∫ x in (3/128:ℝ)..(1/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/128:ℝ) (1/32:ℝ) (525/18944:ℝ) (14653578341/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_014).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_003 :
    (∫ x in (3/128:ℝ)..(1/32:ℝ), x^2*thetaFirstMode x) ≤ (3615220966659/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/128:ℝ) (1/32:ℝ) (37604129859/500000000000:ℝ) (71687771591/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_012).2 (thetaFirstMode_node_016).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_004 :
    (4260399393793/6291456000000000000:ℝ) ≤ ∫ x in (1/32:ℝ)..(5/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/32:ℝ) (5/128:ℝ) (1107/31232:ℝ) (69842613013/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_018).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_004 :
    (∫ x in (1/32:ℝ)..(5/128:ℝ), x^2*thetaFirstMode x) ≤ (17044914599353/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/32:ℝ) (5/128:ℝ) (71687771591/1000000000000:ℝ) (6827630847/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_016).2 (thetaFirstMode_node_020).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_005 :
    (94570958573/98304000000000000:ℝ) ≤ ∫ x in (5/128:ℝ)..(3/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/128:ℝ) (3/64:ℝ) (2013/46592:ℝ) (1039241303/15625000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_022).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_005 :
    (∫ x in (5/128:ℝ)..(3/64:ℝ), x^2*thetaFirstMode x) ≤ (756721634297/786432000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/128:ℝ) (3/64:ℝ) (6827630847/100000000000:ℝ) (32486641319/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_020).2 (thetaFirstMode_node_024).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_006 :
    (334858854157/262144000000000000:ℝ) ≤ ∫ x in (3/64:ℝ)..(7/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/64:ℝ) (7/128:ℝ) (3315/65024:ℝ) (7910051673/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_026).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_006 :
    (∫ x in (3/64:ℝ)..(7/128:ℝ), x^2*thetaFirstMode x) ≤ (3215328317911/2516582400000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/64:ℝ) (7/128:ℝ) (32486641319/500000000000:ℝ) (7722248157/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_024).2 (thetaFirstMode_node_028).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_007 :
    (5082836440123/3145728000000000000:ℝ) ≤ ∫ x in (7/128:ℝ)..(1/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/128:ℝ) (1/16:ℝ) (5085/86528:ℝ) (30075955267/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_030).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_007 :
    (∫ x in (7/128:ℝ)..(1/16:ℝ), x^2*thetaFirstMode x) ≤ (20335857006391/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/128:ℝ) (1/16:ℝ) (7722248157/125000000000:ℝ) (29344794299/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_028).2 (thetaFirstMode_node_032).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_008 :
    (4132166911327/2097152000000000000:ℝ) ≤ ∫ x in (1/16:ℝ)..(9/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/16:ℝ) (9/128:ℝ) (7395/111104:ℝ) (57126731493/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_034).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_008 :
    (∫ x in (1/16:ℝ)..(9/128:ℝ), x^2*thetaFirstMode x) ≤ (49597482537479/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/16:ℝ) (9/128:ℝ) (29344794299/500000000000:ℝ) (55707148763/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_032).2 (thetaFirstMode_node_036).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_009 :
    (612063142993/262144000000000000:ℝ) ≤ ∫ x in (9/128:ℝ)..(5/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/128:ℝ) (5/64:ℝ) (10317/138752:ℝ) (6775606749/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_038).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_009 :
    (∫ x in (9/128:ℝ)..(5/64:ℝ), x^2*thetaFirstMode x) ≤ (14693062305089/6291456000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/128:ℝ) (5/64:ℝ) (55707148763/1000000000000:ℝ) (52829608587/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_036).2 (thetaFirstMode_node_040).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_010 :
    (5669563635233/2097152000000000000:ℝ) ≤ ∫ x in (5/64:ℝ)..(11/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/64:ℝ) (11/128:ℝ) (13923/169472:ℝ) (51385773129/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_042).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_010 :
    (∫ x in (5/64:ℝ)..(11/128:ℝ), x^2*thetaFirstMode x) ≤ (22683963705867/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/64:ℝ) (11/128:ℝ) (52829608587/1000000000000:ℝ) (25027900449/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_040).2 (thetaFirstMode_node_044).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_011 :
    (9660730035451/3145728000000000000:ℝ) ≤ ∫ x in (11/128:ℝ)..(3/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/128:ℝ) (3/32:ℝ) (18285/203264:ℝ) (24334332583/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_046).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_011 :
    (∫ x in (11/128:ℝ)..(3/32:ℝ), x^2*thetaFirstMode x) ≤ (1207908121429/393216000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/128:ℝ) (3/32:ℝ) (25027900449/500000000000:ℝ) (23692225997/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_044).2 (thetaFirstMode_node_048).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_012 :
    (21598610840191/6291456000000000000:ℝ) ≤ ∫ x in (3/32:ℝ)..(13/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/32:ℝ) (13/128:ℝ) (23475/240128:ℝ) (46052475139/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_050).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_012 :
    (∫ x in (3/32:ℝ)..(13/128:ℝ), x^2*thetaFirstMode x) ≤ (86418065281021/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/32:ℝ) (13/128:ℝ) (23692225997/500000000000:ℝ) (44814185473/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_048).2 (thetaFirstMode_node_052).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_013 :
    (7938058053563/2097152000000000000:ℝ) ≤ ∫ x in (13/128:ℝ)..(7/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/128:ℝ) (7/64:ℝ) (29565/280064:ℝ) (43535967387/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_054).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_013 :
    (∫ x in (13/128:ℝ)..(7/64:ℝ), x^2*thetaFirstMode x) ≤ (95283828778859/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/128:ℝ) (7/64:ℝ) (44814185473/1000000000000:ℝ) (661617597/15625000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_052).2 (thetaFirstMode_node_056).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_014 :
    (2594530486261/629145600000000000:ℝ) ≤ ∫ x in (7/64:ℝ)..(15/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/64:ℝ) (15/128:ℝ) (36627/323072:ℝ) (4111775731/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_058).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_014 :
    (∫ x in (7/64:ℝ)..(15/128:ℝ), x^2*thetaFirstMode x) ≤ (20762401159273/5033164800000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/64:ℝ) (15/128:ℝ) (661617597/15625000000:ℝ) (39970904711/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_056).2 (thetaFirstMode_node_060).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_015 :
    (13986077887159/3145728000000000000:ℝ) ≤ ∫ x in (15/128:ℝ)..(1/8:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/128:ℝ) (1/8:ℝ) (44733/369152:ℝ) (19398166279/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_062).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_015 :
    (∫ x in (15/128:ℝ)..(1/8:ℝ), x^2*thetaFirstMode x) ≤ (55961591560423/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/128:ℝ) (1/8:ℝ) (39970904711/1000000000000:ℝ) (301557293/8000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_060).2 (thetaFirstMode_node_064).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_016 :
    (29877745966951/6291456000000000000:ℝ) ≤ ∫ x in (1/8:ℝ)..(17/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (1/8:ℝ) (17/128:ℝ) (53955/418304:ℝ) (36570068503/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_066).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_016 :
    (∫ x in (1/8:ℝ)..(17/128:ℝ), x^2*thetaFirstMode x) ≤ (4781976467831/1006632960000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (1/8:ℝ) (17/128:ℝ) (301557293/8000000000:ℝ) (710261049/20000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_064).2 (thetaFirstMode_node_068).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_017 :
    (1318659317757/262144000000000000:ℝ) ≤ ∫ x in (17/128:ℝ)..(9/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (17/128:ℝ) (9/64:ℝ) (64365/470528:ℝ) (4304655009/125000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_070).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_017 :
    (∫ x in (17/128:ℝ)..(9/64:ℝ), x^2*thetaFirstMode x) ≤ (123665682169/24576000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (17/128:ℝ) (9/64:ℝ) (710261049/20000000000:ℝ) (16712126261/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_068).2 (thetaFirstMode_node_072).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_018 :
    (8317681124597/1572864000000000000:ℝ) ≤ ∫ x in (9/64:ℝ)..(19/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (9/64:ℝ) (19/128:ℝ) (76035/525824:ℝ) (8099007911/250000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_074).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_018 :
    (∫ x in (9/64:ℝ)..(19/128:ℝ), x^2*thetaFirstMode x) ≤ (66564620269079/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (9/64:ℝ) (19/128:ℝ) (16712126261/500000000000:ℝ) (7856590531/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_072).2 (thetaFirstMode_node_076).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_019 :
    (34737226412077/6291456000000000000:ℝ) ≤ ∫ x in (19/128:ℝ)..(5/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (19/128:ℝ) (5/32:ℝ) (89037/584192:ℝ) (30444545497/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_078).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_019 :
    (∫ x in (19/128:ℝ)..(5/32:ℝ), x^2*thetaFirstMode x) ≤ (5791635122849/1048576000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (19/128:ℝ) (5/32:ℝ) (7856590531/250000000000:ℝ) (7379352941/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_076).2 (thetaFirstMode_node_080).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_020 :
    (7208080184903/1258291200000000000:ℝ) ≤ ∫ x in (5/32:ℝ)..(21/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (5/32:ℝ) (21/128:ℝ) (103443/645632:ℝ) (5716161923/200000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_082).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_020 :
    (∫ x in (5/32:ℝ)..(21/128:ℝ), x^2*thetaFirstMode x) ≤ (12017993817233/2097152000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (5/32:ℝ) (21/128:ℝ) (7379352941/250000000000:ℝ) (3461920953/125000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_080).2 (thetaFirstMode_node_084).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_021 :
    (2323466408737/393216000000000000:ℝ) ≤ ∫ x in (21/128:ℝ)..(11/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (21/128:ℝ) (11/64:ℝ) (119325/710144:ℝ) (1675174051/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_086).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_021 :
    (∫ x in (21/128:ℝ)..(11/64:ℝ), x^2*thetaFirstMode x) ≤ (9917341418987/1677721600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (21/128:ℝ) (11/64:ℝ) (3461920953/125000000000:ℝ) (25958137133/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_084).2 (thetaFirstMode_node_088).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_022 :
    (19069808240833/3145728000000000000:ℝ) ≤ ∫ x in (11/64:ℝ)..(23/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (11/64:ℝ) (23/128:ℝ) (136755/777728:ℝ) (12554185807/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_090).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_022 :
    (∫ x in (11/64:ℝ)..(23/128:ℝ), x^2*thetaFirstMode x) ≤ (152620625011027/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (11/64:ℝ) (23/128:ℝ) (25958137133/1000000000000:ℝ) (12151787313/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_088).2 (thetaFirstMode_node_092).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_023 :
    (19465952899993/3145728000000000000:ℝ) ≤ ∫ x in (23/128:ℝ)..(3/16:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (23/128:ℝ) (3/16:ℝ) (155805/848384:ℝ) (11747708449/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_094).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_023 :
    (∫ x in (23/128:ℝ)..(3/16:ℝ), x^2*thetaFirstMode x) ≤ (12982798695451/2097152000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (23/128:ℝ) (3/16:ℝ) (12151787313/500000000000:ℝ) (2272948707/100000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_092).2 (thetaFirstMode_node_096).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_024 :
    (988826459209/157286400000000000:ℝ) ≤ ∫ x in (3/16:ℝ)..(25/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (3/16:ℝ) (25/128:ℝ) (176547/922112:ℝ) (549043009/25000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_098).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_024 :
    (∫ x in (3/16:ℝ)..(25/128:ℝ), x^2*thetaFirstMode x) ≤ (26380314482171/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (3/16:ℝ) (25/128:ℝ) (2272948707/100000000000:ℝ) (5308409979/250000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_096).2 (thetaFirstMode_node_100).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_025 :
    (1333511159213/209715200000000000:ℝ) ≤ ∫ x in (25/128:ℝ)..(13/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (25/128:ℝ) (13/64:ℝ) (199053/998912:ℝ) (2050504089/100000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_102).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_025 :
    (∫ x in (25/128:ℝ)..(13/64:ℝ), x^2*thetaFirstMode x) ≤ (80047276041967/12582912000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (25/128:ℝ) (13/64:ℝ) (5308409979/250000000000:ℝ) (9906881453/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_100).2 (thetaFirstMode_node_104).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_026 :
    (40292377660703/6291456000000000000:ℝ) ≤ ∫ x in (13/64:ℝ)..(27/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (13/64:ℝ) (27/128:ℝ) (223395/1078784:ℝ) (19123102829/1000000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_106).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_026 :
    (∫ x in (13/64:ℝ)..(27/128:ℝ), x^2*thetaFirstMode x) ≤ (13437177393721/2097152000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (13/64:ℝ) (27/128:ℝ) (9906881453/500000000000:ℝ) (9233777979/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_104).2 (thetaFirstMode_node_108).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_027 :
    (105257977441/16384000000000000:ℝ) ≤ ∫ x in (27/128:ℝ)..(7/32:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (27/128:ℝ) (7/32:ℝ) (249645/1161728:ℝ) (139168767/7812500000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_110).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_027 :
    (∫ x in (27/128:ℝ)..(7/32:ℝ), x^2*thetaFirstMode x) ≤ (10783740098729/1677721600000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (27/128:ℝ) (7/32:ℝ) (9233777979/500000000000:ℝ) (17192694997/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_108).2 (thetaFirstMode_node_112).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_028 :
    (20195678109151/3145728000000000000:ℝ) ≤ ∫ x in (7/32:ℝ)..(29/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (7/32:ℝ) (29/128:ℝ) (277875/1247744:ℝ) (8287106323/500000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_114).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_028 :
    (∫ x in (7/32:ℝ)..(29/128:ℝ), x^2*thetaFirstMode x) ≤ (26941384827949/4194304000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (7/32:ℝ) (29/128:ℝ) (17192694997/1000000000000:ℝ) (3197367559/200000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_112).2 (thetaFirstMode_node_116).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_029 :
    (837836810797/131072000000000000:ℝ) ≤ ∫ x in (29/128:ℝ)..(15/64:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (29/128:ℝ) (15/64:ℝ) (308157/1336832:ℝ) (962661981/62500000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_118).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_029 :
    (∫ x in (29/128:ℝ)..(15/64:ℝ), x^2*thetaFirstMode x) ≤ (1676566417957/262144000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (29/128:ℝ) (15/64:ℝ) (3197367559/200000000000:ℝ) (14847629727/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_116).2 (thetaFirstMode_node_120).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_030 :
    (49876518053/7864320000000000:ℝ) ≤ ∫ x in (15/64:ℝ)..(31/128:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (15/64:ℝ) (31/128:ℝ) (340563/1428992:ℝ) (17870483/1250000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_122).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_030 :
    (∫ x in (15/64:ℝ)..(31/128:ℝ), x^2*thetaFirstMode x) ≤ (53231054390563/8388608000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (15/64:ℝ) (31/128:ℝ) (14847629727/1000000000000:ℝ) (6886354727/500000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_120).2 (thetaFirstMode_node_124).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_lower_2_031 :
    (986372330437/157286400000000000:ℝ) ≤ ∫ x in (31/128:ℝ)..(1/4:ℝ), x^2*thetaFirstMode x := by
  have h := thetaFirstMode_weighted_cell_lower 2 (31/128:ℝ) (1/4:ℝ) (375165/1524224:ℝ) (331330981/25000000000:ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [thetaPowerMass]) (by norm_num [thetaPowerMass]) (thetaFirstMode_node_126).1
  norm_num [thetaPowerMass] at h ⊢
  exact h

theorem thetaFirstMode_cell_upper_2_031 :
    (∫ x in (31/128:ℝ)..(1/4:ℝ), x^2*thetaFirstMode x) ≤ (157910233714507/25165824000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_cell_upper 2 (31/128:ℝ) (1/4:ℝ) (6886354727/500000000000:ℝ) (12759714529/1000000000000:ℝ)
    (by norm_num) (by norm_num) (thetaFirstMode_node_124).2 (thetaFirstMode_node_128).2
  norm_num [thetaPowerMass] at h ⊢
  exact h

end
end CarrySelfAdjointOperator

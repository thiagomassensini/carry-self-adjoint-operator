import CarrySelfAdjointOperator.ThetaTenthSourceCertificateData.Curvature1

open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaSource_curvature_cell_upper_10_032 :
    (∫ x in (1/8:ℝ)..(33/256:ℝ), x^10*thetaFirstMode x) ≤ (9888795879/62500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (1/8:ℝ) (33/256:ℝ)
    (1884733080709/50000000000000:ℝ) (3659214001041/100000000000000:ℝ) (1505236804533694299/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_032 (thetaFirstMode_refined_node_0192).2 (thetaFirstMode_refined_node_0198).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_033 :
    (∫ x in (33/256:ℝ)..(17/128:ℝ), x^10*thetaFirstMode x) ≤ (103948672667/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (33/256:ℝ) (17/128:ℝ)
    (3659214001041/100000000000000:ℝ) (1775652622123/50000000000000:ℝ) (372626855380705201/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_033 (thetaFirstMode_refined_node_0198).2 (thetaFirstMode_refined_node_0204).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_034 :
    (∫ x in (17/128:ℝ)..(35/256:ℝ), x^10*thetaFirstMode x) ≤ (270683659701/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (17/128:ℝ) (35/256:ℝ)
    (1775652622123/50000000000000:ℝ) (3445716835953/100000000000000:ℝ) (737736862199491809/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_034 (thetaFirstMode_refined_node_0204).2 (thetaFirstMode_refined_node_0210).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_035 :
    (∫ x in (35/256:ℝ)..(9/64:ℝ), x^10*thetaFirstMode x) ≤ (2729683669/7812500000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (35/256:ℝ) (9/64:ℝ)
    (3445716835953/100000000000000:ℝ) (3342425251881/100000000000000:ℝ) (45629571400713733/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_035 (thetaFirstMode_refined_node_0210).2 (thetaFirstMode_refined_node_0216).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_036 :
    (∫ x in (9/64:ℝ)..(37/256:ℝ), x^10*thetaFirstMode x) ≤ (55916628839/125000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (9/64:ℝ) (37/256:ℝ)
    (3342425251881/100000000000000:ℝ) (3241406514929/100000000000000:ℝ) (288907166448900491/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_036 (thetaFirstMode_refined_node_0216).2 (thetaFirstMode_refined_node_0222).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_037 :
    (∫ x in (37/256:ℝ)..(19/128:ℝ), x^10*thetaFirstMode x) ≤ (568293873643/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (37/256:ℝ) (19/128:ℝ)
    (3241406514929/100000000000000:ℝ) (3142636211899/100000000000000:ℝ) (89290827741626873/62500000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_037 (thetaFirstMode_refined_node_0222).2 (thetaFirstMode_refined_node_0228).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_038 :
    (∫ x in (19/128:ℝ)..(39/256:ℝ), x^10*thetaFirstMode x) ≤ (716668923523/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (19/128:ℝ) (39/256:ℝ)
    (3142636211899/100000000000000:ℝ) (121843580413/4000000000000:ℝ) (1412509534683562307/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_038 (thetaFirstMode_refined_node_0228).2 (thetaFirstMode_refined_node_0234).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_039 :
    (∫ x in (39/256:ℝ)..(5/32:ℝ), x^10*thetaFirstMode x) ≤ (897480201049/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (39/256:ℝ) (5/32:ℝ)
    (121843580413/4000000000000:ℝ) (2951741175631/100000000000000:ℝ) (349028961673015303/250000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_039 (thetaFirstMode_refined_node_0234).2 (thetaFirstMode_refined_node_0240).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_040 :
    (∫ x in (5/32:ℝ)..(41/256:ℝ), x^10*thetaFirstMode x) ≤ (279111140611/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (5/32:ℝ) (41/256:ℝ)
    (2951741175631/100000000000000:ℝ) (2859565588393/100000000000000:ℝ) (1379483438729095073/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_040 (thetaFirstMode_refined_node_0240).2 (thetaFirstMode_refined_node_0246).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_041 :
    (∫ x in (41/256:ℝ)..(21/128:ℝ), x^10*thetaFirstMode x) ≤ (1380034757537/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (41/256:ℝ) (21/128:ℝ)
    (2859565588393/100000000000000:ℝ) (1384768380923/50000000000000:ℝ) (272524735160506569/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_041 (thetaFirstMode_refined_node_0246).2 (thetaFirstMode_refined_node_0252).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_042 :
    (∫ x in (21/128:ℝ)..(43/256:ℝ), x^10*thetaFirstMode x) ≤ (423885337313/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (21/128:ℝ) (43/256:ℝ)
    (1384768380923/50000000000000:ℝ) (2681628359527/100000000000000:ℝ) (168193502212474447/125000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_042 (thetaFirstMode_refined_node_0252).2 (thetaFirstMode_refined_node_0258).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_043 :
    (∫ x in (43/256:ℝ)..(11/64:ℝ), x^10*thetaFirstMode x) ≤ (1035567471763/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (43/256:ℝ) (11/64:ℝ)
    (2681628359527/100000000000000:ℝ) (2595813713037/100000000000000:ℝ) (664134004242976343/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_043 (thetaFirstMode_refined_node_0258).2 (thetaFirstMode_refined_node_0264).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_044 :
    (∫ x in (11/64:ℝ)..(45/256:ℝ), x^10*thetaFirstMode x) ≤ (1257964063579/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (11/64:ℝ) (45/256:ℝ)
    (2595813713037/100000000000000:ℝ) (2512065839989/100000000000000:ℝ) (655397632509854761/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_044 (thetaFirstMode_refined_node_0264).2 (thetaFirstMode_refined_node_0270).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_045 :
    (∫ x in (45/256:ℝ)..(23/128:ℝ), x^10*thetaFirstMode x) ≤ (3040036463067/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (45/256:ℝ) (23/128:ℝ)
    (2512065839989/100000000000000:ℝ) (1215178731007/50000000000000:ℝ) (10102667702120131/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_045 (thetaFirstMode_refined_node_0270).2 (thetaFirstMode_refined_node_0276).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_046 :
    (∫ x in (23/128:ℝ)..(47/256:ℝ), x^10*thetaFirstMode x) ≤ (365463784859/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (23/128:ℝ) (47/256:ℝ)
    (1215178731007/50000000000000:ℝ) (2350661022913/100000000000000:ℝ) (1275318339791649473/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_046 (thetaFirstMode_refined_node_0276).2 (thetaFirstMode_refined_node_0282).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_047 :
    (∫ x in (47/256:ℝ)..(3/16:ℝ), x^10*thetaFirstMode x) ≤ (1093007375873/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (47/256:ℝ) (3/16:ℝ)
    (2350661022913/100000000000000:ℝ) (5682371767/250000000000:ℝ) (628668827175261319/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_047 (thetaFirstMode_refined_node_0282).2 (thetaFirstMode_refined_node_0288).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_048 :
    (∫ x in (3/16:ℝ)..(49/256:ℝ), x^10*thetaFirstMode x) ≤ (5205681821189/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (3/16:ℝ) (49/256:ℝ)
    (5682371767/250000000000:ℝ) (219719245643/10000000000000:ℝ) (247842240871482451/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_048 (thetaFirstMode_refined_node_0288).2 (thetaFirstMode_refined_node_0294).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_049 :
    (∫ x in (49/256:ℝ)..(25/128:ℝ), x^10*thetaFirstMode x) ≤ (1234057657903/200000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (49/256:ℝ) (25/128:ℝ)
    (219719245643/10000000000000:ℝ) (530840997859/25000000000000:ℝ) (1220950800364612401/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_049 (thetaFirstMode_refined_node_0294).2 (thetaFirstMode_refined_node_0300).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_050 :
    (∫ x in (25/128:ℝ)..(51/256:ℝ), x^10*thetaFirstMode x) ≤ (4551131667/625000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (25/128:ℝ) (51/256:ℝ)
    (530840997859/25000000000000:ℝ) (2051434826679/100000000000000:ℝ) (1202568256922579683/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_050 (thetaFirstMode_refined_node_0300).2 (thetaFirstMode_refined_node_0306).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_051 :
    (∫ x in (51/256:ℝ)..(13/64:ℝ), x^10*thetaFirstMode x) ≤ (8557518589581/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (51/256:ℝ) (13/64:ℝ)
    (2051434826679/100000000000000:ℝ) (990688145289/50000000000000:ℝ) (592037690565412011/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_051 (thetaFirstMode_refined_node_0306).2 (thetaFirstMode_refined_node_0312).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_052 :
    (∫ x in (13/64:ℝ)..(53/256:ℝ), x^10*thetaFirstMode x) ≤ (2504005692973/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (13/64:ℝ) (53/256:ℝ)
    (990688145289/50000000000000:ℝ) (1913159543403/100000000000000:ℝ) (1165483960852216633/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_052 (thetaFirstMode_refined_node_0312).2 (thetaFirstMode_refined_node_0318).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_053 :
    (∫ x in (53/256:ℝ)..(27/128:ℝ), x^10*thetaFirstMode x) ≤ (1167730098197/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (53/256:ℝ) (27/128:ℝ)
    (1913159543403/100000000000000:ℝ) (1846755595551/100000000000000:ℝ) (1146805753150462477/1000000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_053 (thetaFirstMode_refined_node_0318).2 (thetaFirstMode_refined_node_0324).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_054 :
    (∫ x in (27/128:ℝ)..(55/256:ℝ), x^10*thetaFirstMode x) ≤ (13562715966327/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (27/128:ℝ) (55/256:ℝ)
    (1846755595551/100000000000000:ℝ) (1782135325809/100000000000000:ℝ) (564026236416942689/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_054 (thetaFirstMode_refined_node_0324).2 (thetaFirstMode_refined_node_0330).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_055 :
    (∫ x in (55/256:ℝ)..(7/32:ℝ), x^10*thetaFirstMode x) ≤ (15695024533987/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (55/256:ℝ) (7/32:ℝ)
    (1782135325809/100000000000000:ℝ) (1719269499473/100000000000000:ℝ) (221847156154640409/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_055 (thetaFirstMode_refined_node_0330).2 (thetaFirstMode_refined_node_0336).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_056 :
    (∫ x in (7/32:ℝ)..(57/256:ℝ), x^10*thetaFirstMode x) ≤ (1809837703267/100000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (7/32:ℝ) (57/256:ℝ)
    (1719269499473/100000000000000:ℝ) (1658128786473/100000000000000:ℝ) (545183636290087911/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_056 (thetaFirstMode_refined_node_0336).2 (thetaFirstMode_refined_node_0342).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_057 :
    (∫ x in (57/256:ℝ)..(29/128:ℝ), x^10*thetaFirstMode x) ≤ (20798306490603/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (57/256:ℝ) (29/128:ℝ)
    (1658128786473/100000000000000:ℝ) (1598683779299/100000000000000:ℝ) (214291693428588019/200000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_057 (thetaFirstMode_refined_node_0342).2 (thetaFirstMode_refined_node_0348).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_058 :
    (∫ x in (29/128:ℝ)..(59/256:ℝ), x^10*thetaFirstMode x) ≤ (5955426686343/250000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (29/128:ℝ) (59/256:ℝ)
    (1598683779299/100000000000000:ℝ) (1540905010899/100000000000000:ℝ) (8222818714789663/7812500000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_058 (thetaFirstMode_refined_node_0348).2 (thetaFirstMode_refined_node_0354).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_059 :
    (∫ x in (59/256:ℝ)..(15/64:ℝ), x^10*thetaFirstMode x) ≤ (339959986729/12500000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (59/256:ℝ) (15/64:ℝ)
    (1540905010899/100000000000000:ℝ) (148476297237/10000000000000:ℝ) (516782794844143017/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_059 (thetaFirstMode_refined_node_0354).2 (thetaFirstMode_refined_node_0360).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_060 :
    (∫ x in (15/64:ℝ)..(61/256:ℝ), x^10*thetaFirstMode x) ≤ (30953085818169/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (15/64:ℝ) (61/256:ℝ)
    (148476297237/10000000000000:ℝ) (35755703263/2500000000000:ℝ) (31706377237718811/31250000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_060 (thetaFirstMode_refined_node_0360).2 (thetaFirstMode_refined_node_0366).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_061 :
    (∫ x in (61/256:ℝ)..(31/128:ℝ), x^10*thetaFirstMode x) ≤ (35121293372819/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (61/256:ℝ) (31/128:ℝ)
    (35755703263/2500000000000:ℝ) (537996463/39062500000:ℝ) (497823671186989721/500000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_061 (thetaFirstMode_refined_node_0366).2 (thetaFirstMode_refined_node_0372).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_062 :
    (∫ x in (31/128:ℝ)..(63/256:ℝ), x^10*thetaFirstMode x) ≤ (39733299389357/1000000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (31/128:ℝ) (63/256:ℝ)
    (537996463/39062500000:ℝ) (1325861886877/100000000000000:ℝ) (97670637171555123/100000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_062 (thetaFirstMode_refined_node_0372).2 (thetaFirstMode_refined_node_0378).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

theorem thetaSource_curvature_cell_upper_10_063 :
    (∫ x in (63/256:ℝ)..(1/4:ℝ), x^10*thetaFirstMode x) ≤ (22411024316303/500000000000000000000000:ℝ) := by
  have h := thetaFirstMode_weighted_curvature_cell_upper 10 (63/256:ℝ) (1/4:ℝ)
    (1325861886877/100000000000000:ℝ) (1275971452837/100000000000000:ℝ) (23944799682406223/25000000000000000:ℝ) (by norm_num) (by norm_num)
    thetaSource_cell_curvature_063 (thetaFirstMode_refined_node_0378).2 (thetaFirstMode_refined_node_0384).2
  norm_num [thetaPowerMass] at h
  linarith only [h]

end
end CarrySelfAdjointOperator

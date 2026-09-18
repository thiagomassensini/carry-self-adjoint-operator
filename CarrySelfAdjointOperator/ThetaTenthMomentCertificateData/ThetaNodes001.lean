import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaTenth_node_0032 :
    (82003210244951/1000000000000000:ℝ) ≤ thetaFirstMode (2275623/252891136:ℝ) ∧
      thetaFirstMode (2275623/252891136:ℝ) ≤ (10250401280619/125000000000000:ℝ) ∧
      (2788312737/500000000000000:ℝ) ≤ thetaSecondMode (2275623/252891136:ℝ) ∧
      thetaSecondMode (2275623/252891136:ℝ) ≤ (223065019/40000000000000:ℝ) := by
  have hfirst : (82003210244951/1000000000000000:ℝ) ≤ thetaFirstMode (2275623/252891136:ℝ) ∧
      thetaFirstMode (2275623/252891136:ℝ) ≤ (10250401280619/125000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (2275623/252891136:ℝ) (101815977787409/100000000000000:ℝ) (1018159777874091/1000000000000000:ℝ)
      (82003210244951/1000000000000000:ℝ) (10250401280619/125000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2788312737/500000000000000:ℝ) ≤ thetaSecondMode (2275623/252891136:ℝ) ∧
      thetaSecondMode (2275623/252891136:ℝ) ≤ (223065019/40000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (2275623/252891136:ℝ) (101815977787409/100000000000000:ℝ) (1018159777874091/1000000000000000:ℝ)
      (2788312737/500000000000000:ℝ) (223065019/40000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0033 :
    (20493170159309/250000000000000:ℝ) ≤ thetaFirstMode (78453441/8657822720:ℝ) ∧
      thetaFirstMode (78453441/8657822720:ℝ) ≤ (81972680637237/1000000000000000:ℝ) ∧
      (2783899059/500000000000000:ℝ) ≤ thetaSecondMode (78453441/8657822720:ℝ) ∧
      thetaSecondMode (78453441/8657822720:ℝ) ≤ (5567798119/1000000000000000:ℝ) := by
  have hfirst : (20493170159309/250000000000000:ℝ) ≤ thetaFirstMode (78453441/8657822720:ℝ) ∧
      thetaFirstMode (78453441/8657822720:ℝ) ≤ (81972680637237/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (78453441/8657822720:ℝ) (101828835467073/100000000000000:ℝ) (1018288354670731/1000000000000000:ℝ)
      (20493170159309/250000000000000:ℝ) (81972680637237/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2783899059/500000000000000:ℝ) ≤ thetaSecondMode (78453441/8657822720:ℝ) ∧
      thetaSecondMode (78453441/8657822720:ℝ) ≤ (5567798119/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (78453441/8657822720:ℝ) (101828835467073/100000000000000:ℝ) (1018288354670731/1000000000000000:ℝ)
      (2783899059/500000000000000:ℝ) (5567798119/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0034 :
    (8194440047389/100000000000000:ℝ) ≤ thetaFirstMode (833665833/91410065408:ℝ) ∧
      thetaFirstMode (833665833/91410065408:ℝ) ≤ (81944400473891/1000000000000000:ℝ) ∧
      (5559630773/1000000000000000:ℝ) ≤ thetaSecondMode (833665833/91410065408:ℝ) ∧
      thetaSecondMode (833665833/91410065408:ℝ) ≤ (2779815387/500000000000000:ℝ) := by
  have hfirst : (8194440047389/100000000000000:ℝ) ≤ thetaFirstMode (833665833/91410065408:ℝ) ∧
      thetaFirstMode (833665833/91410065408:ℝ) ≤ (81944400473891/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (833665833/91410065408:ℝ) (203681499867087/200000000000000:ℝ) (254601874833859/250000000000000:ℝ)
      (8194440047389/100000000000000:ℝ) (81944400473891/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5559630773/1000000000000000:ℝ) ≤ thetaSecondMode (833665833/91410065408:ℝ) ∧
      thetaSecondMode (833665833/91410065408:ℝ) ≤ (2779815387/500000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (833665833/91410065408:ℝ) (203681499867087/200000000000000:ℝ) (254601874833859/250000000000000:ℝ)
      (5559630773/1000000000000000:ℝ) (2779815387/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0035 :
    (16326545525921/200000000000000:ℝ) ≤ thetaFirstMode (5/512:ℝ) ∧
      thetaFirstMode (5/512:ℝ) ≤ (40816363814803/500000000000000:ℝ) ∧
      (170944657/31250000000000:ℝ) ≤ thetaSecondMode (5/512:ℝ) ∧
      thetaSecondMode (5/512:ℝ) ≤ (218809161/40000000000000:ℝ) := by
  have hfirst : (16326545525921/200000000000000:ℝ) ≤ thetaFirstMode (5/512:ℝ) ∧
      thetaFirstMode (5/512:ℝ) ≤ (40816363814803/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5/512:ℝ) (509861616356887/500000000000000:ℝ) (40788929308551/40000000000000:ℝ)
      (16326545525921/200000000000000:ℝ) (40816363814803/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (170944657/31250000000000:ℝ) ≤ thetaSecondMode (5/512:ℝ) ∧
      thetaSecondMode (5/512:ℝ) ≤ (218809161/40000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5/512:ℝ) (509861616356887/500000000000000:ℝ) (40788929308551/40000000000000:ℝ)
      (170944657/31250000000000:ℝ) (218809161/40000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0036 :
    (16232535081733/200000000000000:ℝ) ≤ thetaFirstMode (11/1024:ℝ) ∧
      thetaFirstMode (11/1024:ℝ) ≤ (40581337704333/500000000000000:ℝ) ∧
      (2668747749/500000000000000:ℝ) ≤ thetaSecondMode (11/1024:ℝ) ∧
      thetaSecondMode (11/1024:ℝ) ≤ (5337495499/1000000000000000:ℝ) := by
  have hfirst : (16232535081733/200000000000000:ℝ) ≤ thetaFirstMode (11/1024:ℝ) ∧
      thetaFirstMode (11/1024:ℝ) ≤ (40581337704333/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (11/1024:ℝ) (204343365177451/200000000000000:ℝ) (127714603235907/125000000000000:ℝ)
      (16232535081733/200000000000000:ℝ) (40581337704333/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2668747749/500000000000000:ℝ) ≤ thetaSecondMode (11/1024:ℝ) ∧
      thetaSecondMode (11/1024:ℝ) ≤ (5337495499/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (11/1024:ℝ) (204343365177451/200000000000000:ℝ) (127714603235907/125000000000000:ℝ)
      (2668747749/500000000000000:ℝ) (5337495499/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0037 :
    (81134320736229/1000000000000000:ℝ) ≤ thetaFirstMode (2013/186368:ℝ) ∧
      thetaFirstMode (2013/186368:ℝ) ≤ (81134320736231/1000000000000000:ℝ) ∧
      (5329568789/1000000000000000:ℝ) ≤ thetaSecondMode (2013/186368:ℝ) ∧
      thetaSecondMode (2013/186368:ℝ) ≤ (532956879/100000000000000:ℝ) := by
  have hfirst : (81134320736229/1000000000000000:ℝ) ≤ thetaFirstMode (2013/186368:ℝ) ∧
      thetaFirstMode (2013/186368:ℝ) ≤ (81134320736231/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (2013/186368:ℝ) (1021837442607547/1000000000000000:ℝ) (255459360651887/250000000000000:ℝ)
      (81134320736229/1000000000000000:ℝ) (81134320736231/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5329568789/1000000000000000:ℝ) ≤ thetaSecondMode (2013/186368:ℝ) ∧
      thetaSecondMode (2013/186368:ℝ) ≤ (532956879/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (2013/186368:ℝ) (1021837442607547/1000000000000000:ℝ) (255459360651887/250000000000000:ℝ)
      (5329568789/1000000000000000:ℝ) (532956879/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0038 :
    (81106463960877/1000000000000000:ℝ) ≤ thetaFirstMode (155155/14287872:ℝ) ∧
      thetaFirstMode (155155/14287872:ℝ) ≤ (40553231980439/500000000000000:ℝ) ∧
      (53217901/10000000000000:ℝ) ≤ thetaSecondMode (155155/14287872:ℝ) ∧
      thetaSecondMode (155155/14287872:ℝ) ≤ (5321790101/1000000000000000:ℝ) := by
  have hfirst : (81106463960877/1000000000000000:ℝ) ≤ thetaFirstMode (155155/14287872:ℝ) ∧
      thetaFirstMode (155155/14287872:ℝ) ≤ (40553231980439/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (155155/14287872:ℝ) (204391196245897/200000000000000:ℝ) (510977990614743/500000000000000:ℝ)
      (81106463960877/1000000000000000:ℝ) (40553231980439/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (53217901/10000000000000:ℝ) ≤ thetaSecondMode (155155/14287872:ℝ) ∧
      thetaSecondMode (155155/14287872:ℝ) ≤ (5321790101/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (155155/14287872:ℝ) (204391196245897/200000000000000:ℝ) (510977990614743/500000000000000:ℝ)
      (53217901/10000000000000:ℝ) (5321790101/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0039 :
    (40539719901403/500000000000000:ℝ) ≤ thetaFirstMode (9022937/826617856:ℝ) ∧
      thetaFirstMode (9022937/826617856:ℝ) ≤ (81079439802807/1000000000000000:ℝ) ∧
      (2657126133/500000000000000:ℝ) ≤ thetaSecondMode (9022937/826617856:ℝ) ∧
      thetaSecondMode (9022937/826617856:ℝ) ≤ (5314252267/1000000000000000:ℝ) := by
  have hfirst : (40539719901403/500000000000000:ℝ) ≤ thetaFirstMode (9022937/826617856:ℝ) ∧
      thetaFirstMode (9022937/826617856:ℝ) ≤ (81079439802807/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9022937/826617856:ℝ) (511035507313451/500000000000000:ℝ) (1022071014626903/1000000000000000:ℝ)
      (40539719901403/500000000000000:ℝ) (81079439802807/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2657126133/500000000000000:ℝ) ≤ thetaSecondMode (9022937/826617856:ℝ) ∧
      thetaSecondMode (9022937/826617856:ℝ) ≤ (5314252267/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9022937/826617856:ℝ) (511035507313451/500000000000000:ℝ) (1022071014626903/1000000000000000:ℝ)
      (2657126133/500000000000000:ℝ) (5314252267/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0040 :
    (5065845853119/62500000000000:ℝ) ≤ thetaFirstMode (456304959/41597803520:ℝ) ∧
      thetaFirstMode (456304959/41597803520:ℝ) ≤ (16210706729981/200000000000000:ℝ) ∧
      (5307033999/1000000000000000:ℝ) ≤ thetaSecondMode (456304959/41597803520:ℝ) ∧
      thetaSecondMode (456304959/41597803520:ℝ) ≤ (2653517/500000000000:ℝ) := by
  have hfirst : (5065845853119/62500000000000:ℝ) ≤ thetaFirstMode (456304959/41597803520:ℝ) ∧
      thetaFirstMode (456304959/41597803520:ℝ) ≤ (16210706729981/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (456304959/41597803520:ℝ) (1022181323999241/1000000000000000:ℝ) (511090661999621/500000000000000:ℝ)
      (5065845853119/62500000000000:ℝ) (16210706729981/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5307033999/1000000000000000:ℝ) ≤ thetaSecondMode (456304959/41597803520:ℝ) ∧
      thetaSecondMode (456304959/41597803520:ℝ) ≤ (2653517/500000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (456304959/41597803520:ℝ) (1022181323999241/1000000000000000:ℝ) (511090661999621/500000000000000:ℝ)
      (5307033999/1000000000000000:ℝ) (2653517/500000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0041 :
    (81028969871937/1000000000000000:ℝ) ≤ thetaFirstMode (21259058821/1929025112064:ℝ) ∧
      thetaFirstMode (21259058821/1929025112064:ℝ) ≤ (40514484935969/500000000000000:ℝ) ∧
      (2650098367/500000000000000:ℝ) ≤ thetaSecondMode (21259058821/1929025112064:ℝ) ∧
      thetaSecondMode (21259058821/1929025112064:ℝ) ≤ (1060039347/200000000000000:ℝ) := by
  have hfirst : (81028969871937/1000000000000000:ℝ) ≤ thetaFirstMode (21259058821/1929025112064:ℝ) ∧
      thetaFirstMode (21259058821/1929025112064:ℝ) ≤ (40514484935969/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (21259058821/1929025112064:ℝ) (204457189825741/200000000000000:ℝ) (511142974564353/500000000000000:ℝ)
      (81028969871937/1000000000000000:ℝ) (40514484935969/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2650098367/500000000000000:ℝ) ≤ thetaSecondMode (21259058821/1929025112064:ℝ) ∧
      thetaSecondMode (21259058821/1929025112064:ℝ) ≤ (1060039347/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (21259058821/1929025112064:ℝ) (204457189825741/200000000000000:ℝ) (511142974564353/500000000000000:ℝ)
      (2650098367/500000000000000:ℝ) (1060039347/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0042 :
    (80694341744651/1000000000000000:ℝ) ≤ thetaFirstMode (3/256:ℝ) ∧
      thetaFirstMode (3/256:ℝ) ≤ (20173585436163/250000000000000:ℝ) ∧
      (1301931911/250000000000000:ℝ) ≤ thetaSecondMode (3/256:ℝ) ∧
      thetaSecondMode (3/256:ℝ) ≤ (1041545529/200000000000000:ℝ) := by
  have hfirst : (80694341744651/1000000000000000:ℝ) ≤ thetaFirstMode (3/256:ℝ) ∧
      thetaFirstMode (3/256:ℝ) ≤ (20173585436163/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/256:ℝ) (1023714316602357/1000000000000000:ℝ) (511857158301179/500000000000000:ℝ)
      (80694341744651/1000000000000000:ℝ) (20173585436163/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1301931911/250000000000000:ℝ) ≤ thetaSecondMode (3/256:ℝ) ∧
      thetaSecondMode (3/256:ℝ) ≤ (1041545529/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/256:ℝ) (1023714316602357/1000000000000000:ℝ) (511857158301179/500000000000000:ℝ)
      (1301931911/250000000000000:ℝ) (1041545529/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0043 :
    (8022772623629/100000000000000:ℝ) ≤ thetaFirstMode (13/1024:ℝ) ∧
      thetaFirstMode (13/1024:ℝ) ≤ (80227726236291/1000000000000000:ℝ) ∧
      (5080865427/1000000000000000:ℝ) ≤ thetaSecondMode (13/1024:ℝ) ∧
      thetaSecondMode (13/1024:ℝ) ≤ (1270216357/250000000000000:ℝ) := by
  have hfirst : (8022772623629/100000000000000:ℝ) ≤ thetaFirstMode (13/1024:ℝ) ∧
      thetaFirstMode (13/1024:ℝ) ≤ (80227726236291/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (13/1024:ℝ) (512857856239453/500000000000000:ℝ) (1025715712478907/1000000000000000:ℝ)
      (8022772623629/100000000000000:ℝ) (80227726236291/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5080865427/1000000000000000:ℝ) ≤ thetaSecondMode (13/1024:ℝ) ∧
      thetaSecondMode (13/1024:ℝ) ≤ (1270216357/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (13/1024:ℝ) (512857856239453/500000000000000:ℝ) (1025715712478907/1000000000000000:ℝ)
      (5080865427/1000000000000000:ℝ) (1270216357/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0044 :
    (80203890551287/1000000000000000:ℝ) ≤ thetaFirstMode (3315/260096:ℝ) ∧
      thetaFirstMode (3315/260096:ℝ) ≤ (10025486318911/125000000000000:ℝ) ∧
      (317153097/62500000000000:ℝ) ≤ thetaSecondMode (3315/260096:ℝ) ∧
      thetaSecondMode (3315/260096:ℝ) ≤ (5074449553/1000000000000000:ℝ) := by
  have hfirst : (80203890551287/1000000000000000:ℝ) ≤ thetaFirstMode (3315/260096:ℝ) ∧
      thetaFirstMode (3315/260096:ℝ) ≤ (10025486318911/125000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3315/260096:ℝ) (256454562829129/250000000000000:ℝ) (1025818251316517/1000000000000000:ℝ)
      (80203890551287/1000000000000000:ℝ) (10025486318911/125000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (317153097/62500000000000:ℝ) ≤ thetaSecondMode (3315/260096:ℝ) ∧
      thetaSecondMode (3315/260096:ℝ) ≤ (5074449553/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3315/260096:ℝ) (256454562829129/250000000000000:ℝ) (1025818251316517/1000000000000000:ℝ)
      (317153097/62500000000000:ℝ) (5074449553/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0045 :
    (40090178322589/500000000000000:ℝ) ≤ thetaFirstMode (354965/27743232:ℝ) ∧
      thetaFirstMode (354965/27743232:ℝ) ≤ (80180356645179/1000000000000000:ℝ) ∧
      (5068121029/1000000000000000:ℝ) ≤ thetaSecondMode (354965/27743232:ℝ) ∧
      thetaSecondMode (354965/27743232:ℝ) ≤ (506812103/100000000000000:ℝ) := by
  have hfirst : (40090178322589/500000000000000:ℝ) ≤ thetaFirstMode (354965/27743232:ℝ) ∧
      thetaFirstMode (354965/27743232:ℝ) ≤ (80180356645179/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (354965/27743232:ℝ) (1025919520985601/1000000000000000:ℝ) (512959760492801/500000000000000:ℝ)
      (40090178322589/500000000000000:ℝ) (80180356645179/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5068121029/1000000000000000:ℝ) ≤ thetaSecondMode (354965/27743232:ℝ) ∧
      thetaSecondMode (354965/27743232:ℝ) ≤ (506812103/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (354965/27743232:ℝ) (1025919520985601/1000000000000000:ℝ) (512959760492801/500000000000000:ℝ)
      (5068121029/1000000000000000:ℝ) (506812103/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0046 :
    (20039333144601/250000000000000:ℝ) ≤ thetaFirstMode (28596295/2226614272:ℝ) ∧
      thetaFirstMode (28596295/2226614272:ℝ) ≤ (16031466515681/200000000000000:ℝ) ∧
      (506193549/100000000000000:ℝ) ≤ thetaSecondMode (28596295/2226614272:ℝ) ∧
      thetaSecondMode (28596295/2226614272:ℝ) ≤ (5061935491/1000000000000000:ℝ) := by
  have hfirst : (20039333144601/250000000000000:ℝ) ≤ thetaFirstMode (28596295/2226614272:ℝ) ∧
      thetaFirstMode (28596295/2226614272:ℝ) ≤ (16031466515681/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (28596295/2226614272:ℝ) (513009312350189/500000000000000:ℝ) (1026018624700379/1000000000000000:ℝ)
      (20039333144601/250000000000000:ℝ) (16031466515681/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (506193549/100000000000000:ℝ) ≤ thetaSecondMode (28596295/2226614272:ℝ) ∧
      thetaSecondMode (28596295/2226614272:ℝ) ≤ (5061935491/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (28596295/2226614272:ℝ) (513009312350189/500000000000000:ℝ) (1026018624700379/1000000000000000:ℝ)
      (506193549/100000000000000:ℝ) (5061935491/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0047 :
    (80135004251471/1000000000000000:ℝ) ≤ thetaFirstMode (1998081657/155012664320:ℝ) ∧
      thetaFirstMode (1998081657/155012664320:ℝ) ≤ (5008437765717/62500000000000:ℝ) ∧
      (2527971209/500000000000000:ℝ) ≤ thetaSecondMode (1998081657/155012664320:ℝ) ∧
      thetaSecondMode (1998081657/155012664320:ℝ) ≤ (5055942419/1000000000000000:ℝ) := by
  have hfirst : (80135004251471/1000000000000000:ℝ) ≤ thetaFirstMode (1998081657/155012664320:ℝ) ∧
      thetaFirstMode (1998081657/155012664320:ℝ) ≤ (5008437765717/62500000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1998081657/155012664320:ℝ) (102611476012871/100000000000000:ℝ) (1026114760128711/1000000000000000:ℝ)
      (80135004251471/1000000000000000:ℝ) (5008437765717/62500000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2527971209/500000000000000:ℝ) ≤ thetaSecondMode (1998081657/155012664320:ℝ) ∧
      thetaSecondMode (1998081657/155012664320:ℝ) ≤ (5055942419/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1998081657/155012664320:ℝ) (102611476012871/100000000000000:ℝ) (1026114760128711/1000000000000000:ℝ)
      (2527971209/500000000000000:ℝ) (5055942419/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0048 :
    (80113529118103/1000000000000000:ℝ) ≤ thetaFirstMode (128309553515/9919670396928:ℝ) ∧
      thetaFirstMode (128309553515/9919670396928:ℝ) ≤ (10014191139763/125000000000000:ℝ) ∧
      (315636469/62500000000000:ℝ) ≤ thetaSecondMode (128309553515/9919670396928:ℝ) ∧
      thetaSecondMode (128309553515/9919670396928:ℝ) ≤ (1010036701/200000000000000:ℝ) := by
  have hfirst : (80113529118103/1000000000000000:ℝ) ≤ thetaFirstMode (128309553515/9919670396928:ℝ) ∧
      thetaFirstMode (128309553515/9919670396928:ℝ) ≤ (10014191139763/125000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (128309553515/9919670396928:ℝ) (513103623330219/500000000000000:ℝ) (1026207246660439/1000000000000000:ℝ)
      (80113529118103/1000000000000000:ℝ) (10014191139763/125000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (315636469/62500000000000:ℝ) ≤ thetaSecondMode (128309553515/9919670396928:ℝ) ∧
      thetaSecondMode (128309553515/9919670396928:ℝ) ≤ (1010036701/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (128309553515/9919670396928:ℝ) (513103623330219/500000000000000:ℝ) (1026207246660439/1000000000000000:ℝ)
      (315636469/62500000000000:ℝ) (1010036701/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0049 :
    (15952565690263/200000000000000:ℝ) ≤ thetaFirstMode (7/512:ℝ) ∧
      thetaFirstMode (7/512:ℝ) ≤ (19940707112829/250000000000000:ℝ) ∧
      (4956849889/1000000000000000:ℝ) ≤ thetaSecondMode (7/512:ℝ) ∧
      thetaSecondMode (7/512:ℝ) ≤ (495684989/100000000000000:ℝ) := by
  have hfirst : (15952565690263/200000000000000:ℝ) ≤ thetaFirstMode (7/512:ℝ) ∧
      thetaFirstMode (7/512:ℝ) ≤ (19940707112829/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (7/512:ℝ) (1027721021151621/1000000000000000:ℝ) (513860510575811/500000000000000:ℝ)
      (15952565690263/200000000000000:ℝ) (19940707112829/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4956849889/1000000000000000:ℝ) ≤ thetaSecondMode (7/512:ℝ) ∧
      thetaSecondMode (7/512:ℝ) ≤ (495684989/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (7/512:ℝ) (1027721021151621/1000000000000000:ℝ) (513860510575811/500000000000000:ℝ)
      (4956849889/1000000000000000:ℝ) (495684989/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0050 :
    (2478113997703/31250000000000:ℝ) ≤ thetaFirstMode (15/1024:ℝ) ∧
      thetaFirstMode (15/1024:ℝ) ≤ (79299647926497/1000000000000000:ℝ) ∧
      (4835623129/1000000000000000:ℝ) ≤ thetaSecondMode (15/1024:ℝ) ∧
      thetaSecondMode (15/1024:ℝ) ≤ (483562313/100000000000000:ℝ) := by
  have hfirst : (2478113997703/31250000000000:ℝ) ≤ thetaFirstMode (15/1024:ℝ) ∧
      thetaFirstMode (15/1024:ℝ) ≤ (79299647926497/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (15/1024:ℝ) (128716281283769/125000000000000:ℝ) (1029730250270153/1000000000000000:ℝ)
      (2478113997703/31250000000000:ℝ) (79299647926497/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4835623129/1000000000000000:ℝ) ≤ thetaSecondMode (15/1024:ℝ) ∧
      thetaSecondMode (15/1024:ℝ) ≤ (483562313/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (15/1024:ℝ) (128716281283769/125000000000000:ℝ) (1029730250270153/1000000000000000:ℝ)
      (4835623129/1000000000000000:ℝ) (483562313/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0051 :
    (19819783091501/250000000000000:ℝ) ≤ thetaFirstMode (5085/346112:ℝ) ∧
      thetaFirstMode (5085/346112:ℝ) ≤ (39639566183003/500000000000000:ℝ) ∧
      (4830306969/1000000000000000:ℝ) ≤ thetaSecondMode (5085/346112:ℝ) ∧
      thetaSecondMode (5085/346112:ℝ) ≤ (483030697/100000000000000:ℝ) := by
  have hfirst : (19819783091501/250000000000000:ℝ) ≤ thetaFirstMode (5085/346112:ℝ) ∧
      thetaFirstMode (5085/346112:ℝ) ≤ (39639566183003/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5085/346112:ℝ) (1029819508216591/1000000000000000:ℝ) (64363719263537/62500000000000:ℝ)
      (19819783091501/250000000000000:ℝ) (39639566183003/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4830306969/1000000000000000:ℝ) ≤ thetaSecondMode (5085/346112:ℝ) ∧
      thetaSecondMode (5085/346112:ℝ) ≤ (483030697/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5085/346112:ℝ) (1029819508216591/1000000000000000:ℝ) (64363719263537/62500000000000:ℝ)
      (4830306969/1000000000000000:ℝ) (483030697/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0052 :
    (15851762588483/200000000000000:ℝ) ≤ thetaFirstMode (240825/16344064:ℝ) ∧
      thetaFirstMode (240825/16344064:ℝ) ≤ (4953675808901/62500000000000:ℝ) ∧
      (4825046069/1000000000000000:ℝ) ≤ thetaSecondMode (240825/16344064:ℝ) ∧
      thetaSecondMode (240825/16344064:ℝ) ≤ (482504607/100000000000000:ℝ) := by
  have hfirst : (15851762588483/200000000000000:ℝ) ≤ thetaFirstMode (240825/16344064:ℝ) ∧
      thetaFirstMode (240825/16344064:ℝ) ≤ (4953675808901/62500000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (240825/16344064:ℝ) (1029907934953347/1000000000000000:ℝ) (257476983738337/250000000000000:ℝ)
      (15851762588483/200000000000000:ℝ) (4953675808901/62500000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4825046069/1000000000000000:ℝ) ≤ thetaSecondMode (240825/16344064:ℝ) ∧
      thetaSecondMode (240825/16344064:ℝ) ≤ (482504607/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (240825/16344064:ℝ) (1029907934953347/1000000000000000:ℝ) (257476983738337/250000000000000:ℝ)
      (4825046069/1000000000000000:ℝ) (482504607/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0053 :
    (79238826903903/1000000000000000:ℝ) ≤ thetaFirstMode (77086905/5216702464:ℝ) ∧
      thetaFirstMode (77086905/5216702464:ℝ) ≤ (15847765380781/200000000000000:ℝ) ∧
      (4819875791/1000000000000000:ℝ) ≤ thetaSecondMode (77086905/5216702464:ℝ) ∧
      thetaSecondMode (77086905/5216702464:ℝ) ≤ (301242237/62500000000000:ℝ) := by
  have hfirst : (79238826903903/1000000000000000:ℝ) ≤ thetaFirstMode (77086905/5216702464:ℝ) ∧
      thetaFirstMode (77086905/5216702464:ℝ) ≤ (15847765380781/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (77086905/5216702464:ℝ) (1029994932351213/1000000000000000:ℝ) (514997466175607/500000000000000:ℝ)
      (79238826903903/1000000000000000:ℝ) (15847765380781/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4819875791/1000000000000000:ℝ) ≤ thetaSecondMode (77086905/5216702464:ℝ) ∧
      thetaSecondMode (77086905/5216702464:ℝ) ≤ (301242237/62500000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (77086905/5216702464:ℝ) (1029994932351213/1000000000000000:ℝ) (514997466175607/500000000000000:ℝ)
      (4819875791/1000000000000000:ℝ) (301242237/62500000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0054 :
    (990241255591/12500000000000:ℝ) ≤ thetaFirstMode (1424279835/96116859904:ℝ) ∧
      thetaFirstMode (1424279835/96116859904:ℝ) ≤ (79219300447281/1000000000000000:ℝ) ∧
      (4814828523/1000000000000000:ℝ) ≤ thetaSecondMode (1424279835/96116859904:ℝ) ∧
      thetaSecondMode (1424279835/96116859904:ℝ) ≤ (1203707131/250000000000000:ℝ) := by
  have hfirst : (990241255591/12500000000000:ℝ) ≤ thetaFirstMode (1424279835/96116859904:ℝ) ∧
      thetaFirstMode (1424279835/96116859904:ℝ) ≤ (79219300447281/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1424279835/96116859904:ℝ) (128759993728901/125000000000000:ℝ) (1030079949831209/1000000000000000:ℝ)
      (990241255591/12500000000000:ℝ) (79219300447281/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4814828523/1000000000000000:ℝ) ≤ thetaSecondMode (1424279835/96116859904:ℝ) ∧
      thetaSecondMode (1424279835/96116859904:ℝ) ≤ (1203707131/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1424279835/96116859904:ℝ) (128759993728901/125000000000000:ℝ) (1030079949831209/1000000000000000:ℝ)
      (4814828523/1000000000000000:ℝ) (1203707131/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0055 :
    (79200345247029/1000000000000000:ℝ) ≤ thetaFirstMode (201220028295/13542620874752:ℝ) ∧
      thetaFirstMode (201220028295/13542620874752:ℝ) ≤ (7920034524703/100000000000000:ℝ) ∧
      (4809932809/1000000000000000:ℝ) ≤ thetaSecondMode (201220028295/13542620874752:ℝ) ∧
      thetaSecondMode (201220028295/13542620874752:ℝ) ≤ (480993281/100000000000000:ℝ) := by
  have hfirst : (79200345247029/1000000000000000:ℝ) ≤ thetaFirstMode (201220028295/13542620874752:ℝ) ∧
      thetaFirstMode (201220028295/13542620874752:ℝ) ≤ (7920034524703/100000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (201220028295/13542620874752:ℝ) (515081249783509/500000000000000:ℝ) (1030162499567019/1000000000000000:ℝ)
      (79200345247029/1000000000000000:ℝ) (7920034524703/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4809932809/1000000000000000:ℝ) ≤ thetaSecondMode (201220028295/13542620874752:ℝ) ∧
      thetaSecondMode (201220028295/13542620874752:ℝ) ≤ (480993281/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (201220028295/13542620874752:ℝ) (515081249783509/500000000000000:ℝ) (1030162499567019/1000000000000000:ℝ)
      (4809932809/1000000000000000:ℝ) (480993281/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0056 :
    (39419092083839/500000000000000:ℝ) ≤ thetaFirstMode (1/64:ℝ) ∧
      thetaFirstMode (1/64:ℝ) ≤ (78838184167679/1000000000000000:ℝ) ∧
      (147410259/31250000000000:ℝ) ≤ thetaSecondMode (1/64:ℝ) ∧
      thetaSecondMode (1/64:ℝ) ≤ (4717128289/1000000000000000:ℝ) := by
  have hfirst : (39419092083839/500000000000000:ℝ) ≤ thetaFirstMode (1/64:ℝ) ∧
      thetaFirstMode (1/64:ℝ) ≤ (78838184167679/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/64:ℝ) (515871703749551/500000000000000:ℝ) (1031743407499103/1000000000000000:ℝ)
      (39419092083839/500000000000000:ℝ) (78838184167679/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (147410259/31250000000000:ℝ) ≤ thetaSecondMode (1/64:ℝ) ∧
      thetaSecondMode (1/64:ℝ) ≤ (4717128289/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/64:ℝ) (515871703749551/500000000000000:ℝ) (1031743407499103/1000000000000000:ℝ)
      (147410259/31250000000000:ℝ) (4717128289/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0057 :
    (9797304581227/125000000000000:ℝ) ≤ thetaFirstMode (17/1024:ℝ) ∧
      thetaFirstMode (17/1024:ℝ) ≤ (78378436649817/1000000000000000:ℝ) ∧
      (4601309531/1000000000000000:ℝ) ≤ thetaSecondMode (17/1024:ℝ) ∧
      thetaSecondMode (17/1024:ℝ) ≤ (1150327383/250000000000000:ℝ) := by
  have hfirst : (9797304581227/125000000000000:ℝ) ≤ thetaFirstMode (17/1024:ℝ) ∧
      thetaFirstMode (17/1024:ℝ) ≤ (78378436649817/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (17/1024:ℝ) (1033760500518059/1000000000000000:ℝ) (51688025025903/50000000000000:ℝ)
      (9797304581227/125000000000000:ℝ) (78378436649817/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (4601309531/1000000000000000:ℝ) ≤ thetaSecondMode (17/1024:ℝ) ∧
      thetaSecondMode (17/1024:ℝ) ≤ (1150327383/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (17/1024:ℝ) (1033760500518059/1000000000000000:ℝ) (51688025025903/50000000000000:ℝ)
      (4601309531/1000000000000000:ℝ) (1150327383/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0058 :
    (15672092605711/200000000000000:ℝ) ≤ thetaFirstMode (7395/444416:ℝ) ∧
      thetaFirstMode (7395/444416:ℝ) ≤ (19590115757139/250000000000000:ℝ) ∧
      (919365311/200000000000000:ℝ) ≤ thetaSecondMode (7395/444416:ℝ) ∧
      thetaSecondMode (7395/444416:ℝ) ≤ (1149206639/250000000000000:ℝ) := by
  have hfirst : (15672092605711/200000000000000:ℝ) ≤ thetaFirstMode (7395/444416:ℝ) ∧
      thetaFirstMode (7395/444416:ℝ) ≤ (19590115757139/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (7395/444416:ℝ) (51691979564167/50000000000000:ℝ) (1033839591283341/1000000000000000:ℝ)
      (15672092605711/200000000000000:ℝ) (19590115757139/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (919365311/200000000000000:ℝ) ≤ thetaSecondMode (7395/444416:ℝ) ∧
      thetaSecondMode (7395/444416:ℝ) ≤ (1149206639/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (7395/444416:ℝ) (51691979564167/50000000000000:ℝ) (1033839591283341/1000000000000000:ℝ)
      (919365311/200000000000000:ℝ) (1149206639/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0059 :
    (78342623775877/1000000000000000:ℝ) ≤ thetaFirstMode (1346485/80735232:ℝ) ∧
      thetaFirstMode (1346485/80735232:ℝ) ≤ (39171311887939/500000000000000:ℝ) ∧
      (2296190209/500000000000000:ℝ) ≤ thetaSecondMode (1346485/80735232:ℝ) ∧
      thetaSecondMode (1346485/80735232:ℝ) ≤ (4592380419/1000000000000000:ℝ) := by
  have hfirst : (78342623775877/1000000000000000:ℝ) ≤ thetaFirstMode (1346485/80735232:ℝ) ∧
      thetaFirstMode (1346485/80735232:ℝ) ≤ (39171311887939/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1346485/80735232:ℝ) (258479527054233/250000000000000:ℝ) (1033918108216933/1000000000000000:ℝ)
      (78342623775877/1000000000000000:ℝ) (39171311887939/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2296190209/500000000000000:ℝ) ≤ thetaSecondMode (1346485/80735232:ℝ) ∧
      thetaSecondMode (1346485/80735232:ℝ) ≤ (4592380419/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1346485/80735232:ℝ) (258479527054233/250000000000000:ℝ) (1033918108216933/1000000000000000:ℝ)
      (2296190209/500000000000000:ℝ) (4592380419/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0060 :
    (78325013774261/1000000000000000:ℝ) ≤ thetaFirstMode (183886535/11001106432:ℝ) ∧
      thetaFirstMode (183886535/11001106432:ℝ) ≤ (39162506887131/500000000000000:ℝ) ∧
      (917598933/200000000000000:ℝ) ≤ thetaSecondMode (183886535/11001106432:ℝ) ∧
      thetaSecondMode (183886535/11001106432:ℝ) ≤ (2293997333/500000000000000:ℝ) := by
  have hfirst : (78325013774261/1000000000000000:ℝ) ≤ thetaFirstMode (183886535/11001106432:ℝ) ∧
      thetaFirstMode (183886535/11001106432:ℝ) ≤ (39162506887131/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (183886535/11001106432:ℝ) (1033995633184507/1000000000000000:ℝ) (258498908296127/250000000000000:ℝ)
      (78325013774261/1000000000000000:ℝ) (39162506887131/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (917598933/200000000000000:ℝ) ≤ thetaSecondMode (183886535/11001106432:ℝ) ∧
      thetaSecondMode (183886535/11001106432:ℝ) ≤ (2293997333/500000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (183886535/11001106432:ℝ) (1033995633184507/1000000000000000:ℝ) (258498908296127/250000000000000:ℝ)
      (917598933/200000000000000:ℝ) (2293997333/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0061 :
    (78307721929171/1000000000000000:ℝ) ≤ thetaFirstMode (21717383193/1296398136320:ℝ) ∧
      thetaFirstMode (21717383193/1296398136320:ℝ) ≤ (19576930482293/250000000000000:ℝ) ∧
      (2291845643/500000000000000:ℝ) ≤ thetaSecondMode (21717383193/1296398136320:ℝ) ∧
      thetaSecondMode (21717383193/1296398136320:ℝ) ≤ (4583691287/1000000000000000:ℝ) := by
  have hfirst : (78307721929171/1000000000000000:ℝ) ≤ thetaFirstMode (21717383193/1296398136320:ℝ) ∧
      thetaFirstMode (21717383193/1296398136320:ℝ) ≤ (19576930482293/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (21717383193/1296398136320:ℝ) (41362870960563/40000000000000:ℝ) (258517943503519/250000000000000:ℝ)
      (78307721929171/1000000000000000:ℝ) (19576930482293/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2291845643/500000000000000:ℝ) ≤ thetaSecondMode (21717383193/1296398136320:ℝ) ∧
      thetaSecondMode (21717383193/1296398136320:ℝ) ≤ (4583691287/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (21717383193/1296398136320:ℝ) (41362870960563/40000000000000:ℝ) (258517943503519/250000000000000:ℝ)
      (2291845643/500000000000000:ℝ) (4583691287/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0062 :
    (19572707292069/250000000000000:ℝ) ≤ thetaFirstMode (2350810657195/140028672104448:ℝ) ∧
      thetaFirstMode (2350810657195/140028672104448:ℝ) ≤ (78290829168277/1000000000000000:ℝ) ∧
      (1144872557/250000000000000:ℝ) ≤ thetaSecondMode (2350810657195/140028672104448:ℝ) ∧
      thetaSecondMode (2350810657195/140028672104448:ℝ) ≤ (4579490229/1000000000000000:ℝ) := by
  have hfirst : (19572707292069/250000000000000:ℝ) ≤ thetaFirstMode (2350810657195/140028672104448:ℝ) ∧
      thetaFirstMode (2350810657195/140028672104448:ℝ) ≤ (78290829168277/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (2350810657195/140028672104448:ℝ) (1034146173350337/1000000000000000:ℝ) (517073086675169/500000000000000:ℝ)
      (19572707292069/250000000000000:ℝ) (78290829168277/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1144872557/250000000000000:ℝ) ≤ thetaSecondMode (2350810657195/140028672104448:ℝ) ∧
      thetaSecondMode (2350810657195/140028672104448:ℝ) ≤ (4579490229/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (2350810657195/140028672104448:ℝ) (1034146173350337/1000000000000000:ℝ) (517073086675169/500000000000000:ℝ)
      (1144872557/250000000000000:ℝ) (4579490229/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0063 :
    (77920404817013/1000000000000000:ℝ) ≤ thetaFirstMode (9/512:ℝ) ∧
      thetaFirstMode (9/512:ℝ) ≤ (15584080963403/200000000000000:ℝ) ∧
      (897622407/200000000000000:ℝ) ≤ thetaSecondMode (9/512:ℝ) ∧
      thetaSecondMode (9/512:ℝ) ≤ (1122028009/250000000000000:ℝ) := by
  have hfirst : (77920404817013/1000000000000000:ℝ) ≤ thetaFirstMode (9/512:ℝ) ∧
      thetaFirstMode (9/512:ℝ) ≤ (15584080963403/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9/512:ℝ) (1035781537021623/1000000000000000:ℝ) (129472692127703/125000000000000:ℝ)
      (77920404817013/1000000000000000:ℝ) (15584080963403/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (897622407/200000000000000:ℝ) ≤ thetaSecondMode (9/512:ℝ) ∧
      thetaSecondMode (9/512:ℝ) ≤ (1122028009/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9/512:ℝ) (1035781537021623/1000000000000000:ℝ) (129472692127703/125000000000000:ℝ)
      (897622407/200000000000000:ℝ) (1122028009/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

end
end CarrySelfAdjointOperator

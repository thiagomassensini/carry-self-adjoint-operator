import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaTenth_node_0000 :
    (10803479565943/125000000000000:ℝ) ≤ thetaFirstMode (0/1:ℝ) ∧
      thetaFirstMode (0/1:ℝ) ≤ (17285567305509/200000000000000:ℝ) ∧
      (871835589/125000000000000:ℝ) ≤ thetaSecondMode (0/1:ℝ) ∧
      thetaSecondMode (0/1:ℝ) ≤ (6974684713/1000000000000000:ℝ) := by
  have hfirst : (10803479565943/125000000000000:ℝ) ≤ thetaFirstMode (0/1:ℝ) ∧
      thetaFirstMode (0/1:ℝ) ≤ (17285567305509/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (0/1:ℝ) (1/1:ℝ) (1/1:ℝ)
      (10803479565943/125000000000000:ℝ) (17285567305509/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (871835589/125000000000000:ℝ) ≤ thetaSecondMode (0/1:ℝ) ∧
      thetaSecondMode (0/1:ℝ) ≤ (6974684713/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (0/1:ℝ) (1/1:ℝ) (1/1:ℝ)
      (871835589/125000000000000:ℝ) (6974684713/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0001 :
    (21485145876951/250000000000000:ℝ) ≤ thetaFirstMode (1/1024:ℝ) ∧
      thetaFirstMode (1/1024:ℝ) ≤ (17188116701561/200000000000000:ℝ) ∧
      (680874441/100000000000000:ℝ) ≤ thetaSecondMode (1/1024:ℝ) ∧
      thetaSecondMode (1/1024:ℝ) ≤ (6808744411/1000000000000000:ℝ) := by
  have hfirst : (21485145876951/250000000000000:ℝ) ≤ thetaFirstMode (1/1024:ℝ) ∧
      thetaFirstMode (1/1024:ℝ) ≤ (17188116701561/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/1024:ℝ) (500977516795501/500000000000000:ℝ) (1001955033591003/1000000000000000:ℝ)
      (21485145876951/250000000000000:ℝ) (17188116701561/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (680874441/100000000000000:ℝ) ≤ thetaSecondMode (1/1024:ℝ) ∧
      thetaSecondMode (1/1024:ℝ) ≤ (6808744411/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/1024:ℝ) (500977516795501/500000000000000:ℝ) (1001955033591003/1000000000000000:ℝ)
      (680874441/100000000000000:ℝ) (6808744411/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0002 :
    (85697602324709/1000000000000000:ℝ) ≤ thetaFirstMode (3/2048:ℝ) ∧
      thetaFirstMode (3/2048:ℝ) ≤ (8569760232471/100000000000000:ℝ) ∧
      (3363569781/500000000000000:ℝ) ≤ thetaSecondMode (3/2048:ℝ) ∧
      thetaSecondMode (3/2048:ℝ) ≤ (6727139563/1000000000000000:ℝ) := by
  have hfirst : (85697602324709/1000000000000000:ℝ) ≤ thetaFirstMode (3/2048:ℝ) ∧
      thetaFirstMode (3/2048:ℝ) ≤ (8569760232471/100000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/2048:ℝ) (501466991614223/500000000000000:ℝ) (1002933983228447/1000000000000000:ℝ)
      (85697602324709/1000000000000000:ℝ) (8569760232471/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (3363569781/500000000000000:ℝ) ≤ thetaSecondMode (3/2048:ℝ) ∧
      thetaSecondMode (3/2048:ℝ) ≤ (6727139563/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/2048:ℝ) (501466991614223/500000000000000:ℝ) (1002933983228447/1000000000000000:ℝ)
      (3363569781/500000000000000:ℝ) (6727139563/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0003 :
    (1712334083973/20000000000000:ℝ) ≤ thetaFirstMode (5/3072:ℝ) ∧
      thetaFirstMode (5/3072:ℝ) ≤ (21404176049663/250000000000000:ℝ) ∧
      (3350068991/500000000000000:ℝ) ≤ thetaSecondMode (5/3072:ℝ) ∧
      thetaSecondMode (5/3072:ℝ) ≤ (6700137983/1000000000000000:ℝ) := by
  have hfirst : (1712334083973/20000000000000:ℝ) ≤ thetaFirstMode (5/3072:ℝ) ∧
      thetaFirstMode (5/3072:ℝ) ≤ (21404176049663/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5/3072:ℝ) (501630256138783/500000000000000:ℝ) (1003260512277567/1000000000000000:ℝ)
      (1712334083973/20000000000000:ℝ) (21404176049663/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (3350068991/500000000000000:ℝ) ≤ thetaSecondMode (5/3072:ℝ) ∧
      thetaSecondMode (5/3072:ℝ) ≤ (6700137983/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5/3072:ℝ) (501630256138783/500000000000000:ℝ) (1003260512277567/1000000000000000:ℝ)
      (3350068991/500000000000000:ℝ) (6700137983/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0004 :
    (85576273060697/1000000000000000:ℝ) ≤ thetaFirstMode (7/4096:ℝ) ∧
      thetaFirstMode (7/4096:ℝ) ≤ (42788136530349/500000000000000:ℝ) ∧
      (417917157/62500000000000:ℝ) ≤ thetaSecondMode (7/4096:ℝ) ∧
      thetaSecondMode (7/4096:ℝ) ≤ (6686674513/1000000000000000:ℝ) := by
  have hfirst : (85576273060697/1000000000000000:ℝ) ≤ thetaFirstMode (7/4096:ℝ) ∧
      thetaFirstMode (7/4096:ℝ) ≤ (42788136530349/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (7/4096:ℝ) (501711908332977/500000000000000:ℝ) (200684763333191/200000000000000:ℝ)
      (85576273060697/1000000000000000:ℝ) (42788136530349/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (417917157/62500000000000:ℝ) ≤ thetaSecondMode (7/4096:ℝ) ∧
      thetaSecondMode (7/4096:ℝ) ≤ (6686674513/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (7/4096:ℝ) (501711908332977/500000000000000:ℝ) (200684763333191/200000000000000:ℝ)
      (417917157/62500000000000:ℝ) (6686674513/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0005 :
    (85552020113917/1000000000000000:ℝ) ≤ thetaFirstMode (9/5120:ℝ) ∧
      thetaFirstMode (9/5120:ℝ) ≤ (42776010056959/500000000000000:ℝ) ∧
      (6678608349/1000000000000000:ℝ) ≤ thetaSecondMode (9/5120:ℝ) ∧
      thetaSecondMode (9/5120:ℝ) ≤ (133572167/20000000000000:ℝ) := by
  have hfirst : (85552020113917/1000000000000000:ℝ) ≤ thetaFirstMode (9/5120:ℝ) ∧
      thetaFirstMode (9/5120:ℝ) ≤ (42776010056959/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9/5120:ℝ) (62720113253619/62500000000000:ℝ) (200704362411581/200000000000000:ℝ)
      (85552020113917/1000000000000000:ℝ) (42776010056959/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6678608349/1000000000000000:ℝ) ≤ thetaSecondMode (9/5120:ℝ) ∧
      thetaSecondMode (9/5120:ℝ) ≤ (133572167/20000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9/5120:ℝ) (62720113253619/62500000000000:ℝ) (200704362411581/200000000000000:ℝ)
      (6678608349/1000000000000000:ℝ) (133572167/20000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0006 :
    (85535853872719/1000000000000000:ℝ) ≤ thetaFirstMode (11/6144:ℝ) ∧
      thetaFirstMode (11/6144:ℝ) ≤ (1069198173409/12500000000000:ℝ) ∧
      (6673235867/1000000000000000:ℝ) ≤ thetaSecondMode (11/6144:ℝ) ∧
      thetaSecondMode (11/6144:ℝ) ≤ (1668308967/250000000000000:ℝ) := by
  have hfirst : (85535853872719/1000000000000000:ℝ) ≤ thetaFirstMode (11/6144:ℝ) ∧
      thetaFirstMode (11/6144:ℝ) ≤ (1069198173409/12500000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (11/6144:ℝ) (250896786908999/250000000000000:ℝ) (1003587147635997/1000000000000000:ℝ)
      (85535853872719/1000000000000000:ℝ) (1069198173409/12500000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6673235867/1000000000000000:ℝ) ≤ thetaSecondMode (11/6144:ℝ) ∧
      thetaSecondMode (11/6144:ℝ) ≤ (1668308967/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (11/6144:ℝ) (250896786908999/250000000000000:ℝ) (1003587147635997/1000000000000000:ℝ)
      (6673235867/1000000000000000:ℝ) (1668308967/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0007 :
    (2670470354577/31250000000000:ℝ) ≤ thetaFirstMode (1/512:ℝ) ∧
      thetaFirstMode (1/512:ℝ) ≤ (17091010269293/200000000000000:ℝ) ∧
      (3323216443/500000000000000:ℝ) ≤ thetaSecondMode (1/512:ℝ) ∧
      thetaSecondMode (1/512:ℝ) ≤ (6646432887/1000000000000000:ℝ) := by
  have hfirst : (2670470354577/31250000000000:ℝ) ≤ thetaFirstMode (1/512:ℝ) ∧
      thetaFirstMode (1/512:ℝ) ≤ (17091010269293/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/512:ℝ) (1003913889338347/1000000000000000:ℝ) (250978472334587/250000000000000:ℝ)
      (2670470354577/31250000000000:ℝ) (17091010269293/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (3323216443/500000000000000:ℝ) ≤ thetaSecondMode (1/512:ℝ) ∧
      thetaSecondMode (1/512:ℝ) ≤ (6646432887/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/512:ℝ) (1003913889338347/1000000000000000:ℝ) (250978472334587/250000000000000:ℝ)
      (3323216443/500000000000000:ℝ) (6646432887/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0008 :
    (84971239953787/1000000000000000:ℝ) ≤ thetaFirstMode (3/1024:ℝ) ∧
      thetaFirstMode (3/1024:ℝ) ≤ (21242809988447/250000000000000:ℝ) ∧
      (202739951/31250000000000:ℝ) ≤ thetaSecondMode (3/1024:ℝ) ∧
      thetaSecondMode (3/1024:ℝ) ≤ (6487678433/1000000000000000:ℝ) := by
  have hfirst : (84971239953787/1000000000000000:ℝ) ≤ thetaFirstMode (3/1024:ℝ) ∧
      thetaFirstMode (3/1024:ℝ) ≤ (21242809988447/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/1024:ℝ) (502938287357239/500000000000000:ℝ) (1005876574714479/1000000000000000:ℝ)
      (84971239953787/1000000000000000:ℝ) (21242809988447/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (202739951/31250000000000:ℝ) ≤ thetaSecondMode (3/1024:ℝ) ∧
      thetaSecondMode (3/1024:ℝ) ≤ (6487678433/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/1024:ℝ) (502938287357239/500000000000000:ℝ) (1005876574714479/1000000000000000:ℝ)
      (202739951/31250000000000:ℝ) (6487678433/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0009 :
    (84867789948413/1000000000000000:ℝ) ≤ thetaFirstMode (45/14336:ℝ) ∧
      thetaFirstMode (45/14336:ℝ) ≤ (42433894974207/500000000000000:ℝ) ∧
      (1613528903/250000000000000:ℝ) ≤ thetaSecondMode (45/14336:ℝ) ∧
      thetaSecondMode (45/14336:ℝ) ≤ (6454115613/1000000000000000:ℝ) := by
  have hfirst : (84867789948413/1000000000000000:ℝ) ≤ thetaFirstMode (45/14336:ℝ) ∧
      thetaFirstMode (45/14336:ℝ) ≤ (42433894974207/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (45/14336:ℝ) (1006297649113429/1000000000000000:ℝ) (100629764911343/100000000000000:ℝ)
      (84867789948413/1000000000000000:ℝ) (42433894974207/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1613528903/250000000000000:ℝ) ≤ thetaSecondMode (45/14336:ℝ) ∧
      thetaSecondMode (45/14336:ℝ) ≤ (6454115613/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (45/14336:ℝ) (1006297649113429/1000000000000000:ℝ) (100629764911343/100000000000000:ℝ)
      (1613528903/250000000000000:ℝ) (6454115613/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0010 :
    (21196105018723/250000000000000:ℝ) ≤ thetaFirstMode (105/31744:ℝ) ∧
      thetaFirstMode (105/31744:ℝ) ≤ (84784420074893/1000000000000000:ℝ) ∧
      (642716497/100000000000000:ℝ) ≤ thetaSecondMode (105/31744:ℝ) ∧
      thetaSecondMode (105/31744:ℝ) ≤ (6427164971/1000000000000000:ℝ) := by
  have hfirst : (21196105018723/250000000000000:ℝ) ≤ thetaFirstMode (105/31744:ℝ) ∧
      thetaFirstMode (105/31744:ℝ) ≤ (84784420074893/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (105/31744:ℝ) (1006637353633007/1000000000000000:ℝ) (62914834602063/62500000000000:ℝ)
      (21196105018723/250000000000000:ℝ) (84784420074893/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (642716497/100000000000000:ℝ) ≤ thetaSecondMode (105/31744:ℝ) ∧
      thetaSecondMode (105/31744:ℝ) ≤ (6427164971/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (105/31744:ℝ) (1006637353633007/1000000000000000:ℝ) (62914834602063/62500000000000:ℝ)
      (642716497/100000000000000:ℝ) (6427164971/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0011 :
    (84723336689833/1000000000000000:ℝ) ≤ thetaFirstMode (1785/520192:ℝ) ∧
      thetaFirstMode (1785/520192:ℝ) ≤ (42361668344917/500000000000000:ℝ) ∧
      (200233559/31250000000000:ℝ) ≤ thetaSecondMode (1785/520192:ℝ) ∧
      thetaSecondMode (1785/520192:ℝ) ≤ (6407473889/1000000000000000:ℝ) := by
  have hfirst : (84723336689833/1000000000000000:ℝ) ≤ thetaFirstMode (1785/520192:ℝ) ∧
      thetaFirstMode (1785/520192:ℝ) ≤ (42361668344917/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1785/520192:ℝ) (1006886453963683/1000000000000000:ℝ) (251721613490921/250000000000000:ℝ)
      (84723336689833/1000000000000000:ℝ) (42361668344917/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (200233559/31250000000000:ℝ) ≤ thetaSecondMode (1785/520192:ℝ) ∧
      thetaSecondMode (1785/520192:ℝ) ≤ (6407473889/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1785/520192:ℝ) (1006886453963683/1000000000000000:ℝ) (251721613490921/250000000000000:ℝ)
      (200233559/31250000000000:ℝ) (6407473889/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0012 :
    (84680081487863/1000000000000000:ℝ) ≤ thetaFirstMode (9207/2616320:ℝ) ∧
      thetaFirstMode (9207/2616320:ℝ) ≤ (10585010185983/125000000000000:ℝ) ∧
      (799194763/125000000000000:ℝ) ≤ thetaSecondMode (9207/2616320:ℝ) ∧
      thetaSecondMode (9207/2616320:ℝ) ≤ (1278711621/200000000000000:ℝ) := by
  have hfirst : (84680081487863/1000000000000000:ℝ) ≤ thetaFirstMode (9207/2616320:ℝ) ∧
      thetaFirstMode (9207/2616320:ℝ) ≤ (10585010185983/125000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9207/2616320:ℝ) (1007062955736889/1000000000000000:ℝ) (100706295573689/100000000000000:ℝ)
      (84680081487863/1000000000000000:ℝ) (10585010185983/125000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (799194763/125000000000000:ℝ) ≤ thetaSecondMode (9207/2616320:ℝ) ∧
      thetaSecondMode (9207/2616320:ℝ) ≤ (1278711621/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9207/2616320:ℝ) (1007062955736889/1000000000000000:ℝ) (100706295573689/100000000000000:ℝ)
      (799194763/125000000000000:ℝ) (1278711621/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0013 :
    (4232461171853/50000000000000:ℝ) ≤ thetaFirstMode (15015/4192256:ℝ) ∧
      thetaFirstMode (15015/4192256:ℝ) ≤ (84649223437061/1000000000000000:ℝ) ∧
      (6383644889/1000000000000000:ℝ) ≤ thetaSecondMode (15015/4192256:ℝ) ∧
      thetaSecondMode (15015/4192256:ℝ) ≤ (638364489/100000000000000:ℝ) := by
  have hfirst : (4232461171853/50000000000000:ℝ) ≤ thetaFirstMode (15015/4192256:ℝ) ∧
      thetaFirstMode (15015/4192256:ℝ) ≤ (84649223437061/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (15015/4192256:ℝ) (1007188924730933/1000000000000000:ℝ) (503594462365467/500000000000000:ℝ)
      (4232461171853/50000000000000:ℝ) (84649223437061/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6383644889/1000000000000000:ℝ) ≤ thetaSecondMode (15015/4192256:ℝ) ∧
      thetaSecondMode (15015/4192256:ℝ) ≤ (638364489/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (15015/4192256:ℝ) (1007188924730933/1000000000000000:ℝ) (503594462365467/500000000000000:ℝ)
      (6383644889/1000000000000000:ℝ) (638364489/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0014 :
    (84489149208771/1000000000000000:ℝ) ≤ thetaFirstMode (1/256:ℝ) ∧
      thetaFirstMode (1/256:ℝ) ≤ (21122287302193/250000000000000:ℝ) ∧
      (1266482117/200000000000000:ℝ) ≤ thetaSecondMode (1/256:ℝ) ∧
      thetaSecondMode (1/256:ℝ) ≤ (3166205293/500000000000000:ℝ) := by
  have hfirst : (84489149208771/1000000000000000:ℝ) ≤ thetaFirstMode (1/256:ℝ) ∧
      thetaFirstMode (1/256:ℝ) ≤ (21122287302193/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/256:ℝ) (1007843097206447/1000000000000000:ℝ) (62990193575403/62500000000000:ℝ)
      (84489149208771/1000000000000000:ℝ) (21122287302193/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1266482117/200000000000000:ℝ) ≤ thetaSecondMode (1/256:ℝ) ∧
      thetaSecondMode (1/256:ℝ) ≤ (3166205293/500000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/256:ℝ) (1007843097206447/1000000000000000:ℝ) (62990193575403/62500000000000:ℝ)
      (1266482117/200000000000000:ℝ) (3166205293/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0015 :
    (1312637171237/15625000000000:ℝ) ≤ thetaFirstMode (5/1024:ℝ) ∧
      thetaFirstMode (5/1024:ℝ) ≤ (84008778959169/1000000000000000:ℝ) ∧
      (3090280057/500000000000000:ℝ) ≤ thetaSecondMode (5/1024:ℝ) ∧
      thetaSecondMode (5/1024:ℝ) ≤ (1236112023/200000000000000:ℝ) := by
  have hfirst : (1312637171237/15625000000000:ℝ) ≤ thetaFirstMode (5/1024:ℝ) ∧
      thetaFirstMode (5/1024:ℝ) ≤ (84008778959169/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5/1024:ℝ) (504906732157973/500000000000000:ℝ) (1009813464315947/1000000000000000:ℝ)
      (1312637171237/15625000000000:ℝ) (84008778959169/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (3090280057/500000000000000:ℝ) ≤ thetaSecondMode (5/1024:ℝ) ∧
      thetaSecondMode (5/1024:ℝ) ≤ (1236112023/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5/1024:ℝ) (504906732157973/500000000000000:ℝ) (1009813464315947/1000000000000000:ℝ)
      (3090280057/500000000000000:ℝ) (1236112023/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0016 :
    (20986425105501/250000000000000:ℝ) ≤ thetaFirstMode (195/38912:ℝ) ∧
      thetaFirstMode (195/38912:ℝ) ≤ (16789140084401/200000000000000:ℝ) ∧
      (6160830587/1000000000000000:ℝ) ≤ thetaSecondMode (195/38912:ℝ) ∧
      thetaSecondMode (195/38912:ℝ) ≤ (1540207647/250000000000000:ℝ) := by
  have hfirst : (20986425105501/250000000000000:ℝ) ≤ thetaFirstMode (195/38912:ℝ) ∧
      thetaFirstMode (195/38912:ℝ) ≤ (16789140084401/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (195/38912:ℝ) (252518252439973/250000000000000:ℝ) (1010073009759893/1000000000000000:ℝ)
      (20986425105501/250000000000000:ℝ) (16789140084401/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6160830587/1000000000000000:ℝ) ≤ thetaSecondMode (195/38912:ℝ) ∧
      thetaSecondMode (195/38912:ℝ) ≤ (1540207647/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (195/38912:ℝ) (252518252439973/250000000000000:ℝ) (1010073009759893/1000000000000000:ℝ)
      (6160830587/1000000000000000:ℝ) (1540207647/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0017 :
    (83887630739193/1000000000000000:ℝ) ≤ thetaFirstMode (3325/648192:ℝ) ∧
      thetaFirstMode (3325/648192:ℝ) ≤ (16777526147839/200000000000000:ℝ) ∧
      (6142710639/1000000000000000:ℝ) ≤ thetaSecondMode (3325/648192:ℝ) ∧
      thetaSecondMode (3325/648192:ℝ) ≤ (76783883/12500000000000:ℝ) := by
  have hfirst : (83887630739193/1000000000000000:ℝ) ≤ thetaFirstMode (3325/648192:ℝ) ∧
      thetaFirstMode (3325/648192:ℝ) ≤ (16777526147839/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3325/648192:ℝ) (1010312112996901/1000000000000000:ℝ) (505156056498451/500000000000000:ℝ)
      (83887630739193/1000000000000000:ℝ) (16777526147839/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6142710639/1000000000000000:ℝ) ≤ thetaSecondMode (3325/648192:ℝ) ∧
      thetaSecondMode (3325/648192:ℝ) ≤ (76783883/12500000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3325/648192:ℝ) (1010312112996901/1000000000000000:ℝ) (505156056498451/500000000000000:ℝ)
      (6142710639/1000000000000000:ℝ) (76783883/12500000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0018 :
    (83836845948003/1000000000000000:ℝ) ≤ thetaFirstMode (44135/8433664:ℝ) ∧
      thetaFirstMode (44135/8433664:ℝ) ≤ (16767369189601/200000000000000:ℝ) ∧
      (6126897529/1000000000000000:ℝ) ≤ thetaSecondMode (44135/8433664:ℝ) ∧
      thetaSecondMode (44135/8433664:ℝ) ≤ (612689753/100000000000000:ℝ) := by
  have hfirst : (83836845948003/1000000000000000:ℝ) ≤ thetaFirstMode (44135/8433664:ℝ) ∧
      thetaFirstMode (44135/8433664:ℝ) ≤ (16767369189601/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (44135/8433664:ℝ) (1010521352268169/1000000000000000:ℝ) (101052135226817/100000000000000:ℝ)
      (83836845948003/1000000000000000:ℝ) (16767369189601/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6126897529/1000000000000000:ℝ) ≤ thetaSecondMode (44135/8433664:ℝ) ∧
      thetaSecondMode (44135/8433664:ℝ) ≤ (612689753/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (44135/8433664:ℝ) (1010521352268169/1000000000000000:ℝ) (101052135226817/100000000000000:ℝ)
      (6126897529/1000000000000000:ℝ) (612689753/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0019 :
    (1675881926499/20000000000000:ℝ) ≤ thetaFirstMode (104445/19631104:ℝ) ∧
      thetaFirstMode (104445/19631104:ℝ) ≤ (83794096324951/1000000000000000:ℝ) ∧
      (3056805347/500000000000000:ℝ) ≤ thetaSecondMode (104445/19631104:ℝ) ∧
      thetaSecondMode (104445/19631104:ℝ) ≤ (1222722139/200000000000000:ℝ) := by
  have hfirst : (1675881926499/20000000000000:ℝ) ≤ thetaFirstMode (104445/19631104:ℝ) ∧
      thetaFirstMode (104445/19631104:ℝ) ≤ (83794096324951/1000000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (104445/19631104:ℝ) (1010697581112053/1000000000000000:ℝ) (505348790556027/500000000000000:ℝ)
      (1675881926499/20000000000000:ℝ) (83794096324951/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (3056805347/500000000000000:ℝ) ≤ thetaSecondMode (104445/19631104:ℝ) ∧
      thetaSecondMode (104445/19631104:ℝ) ≤ (1222722139/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (104445/19631104:ℝ) (1010697581112053/1000000000000000:ℝ) (505348790556027/500000000000000:ℝ)
      (3056805347/500000000000000:ℝ) (1222722139/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0020 :
    (41879487808837/500000000000000:ℝ) ≤ thetaFirstMode (5800795/1075808256:ℝ) ∧
      thetaFirstMode (5800795/1075808256:ℝ) ≤ (3350359024707/40000000000000:ℝ) ∧
      (6102711587/1000000000000000:ℝ) ≤ thetaSecondMode (5800795/1075808256:ℝ) ∧
      thetaSecondMode (5800795/1075808256:ℝ) ≤ (1525677897/250000000000000:ℝ) := by
  have hfirst : (41879487808837/500000000000000:ℝ) ≤ thetaFirstMode (5800795/1075808256:ℝ) ∧
      thetaFirstMode (5800795/1075808256:ℝ) ≤ (3350359024707/40000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5800795/1075808256:ℝ) (1010842426225637/1000000000000000:ℝ) (505421213112819/500000000000000:ℝ)
      (41879487808837/500000000000000:ℝ) (3350359024707/40000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6102711587/1000000000000000:ℝ) ≤ thetaSecondMode (5800795/1075808256:ℝ) ∧
      thetaSecondMode (5800795/1075808256:ℝ) ≤ (1525677897/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5800795/1075808256:ℝ) (1010842426225637/1000000000000000:ℝ) (505421213112819/500000000000000:ℝ)
      (6102711587/1000000000000000:ℝ) (1525677897/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0021 :
    (83530129021509/1000000000000000:ℝ) ≤ thetaFirstMode (3/512:ℝ) ∧
      thetaFirstMode (3/512:ℝ) ≤ (8353012902151/100000000000000:ℝ) ∧
      (6032058997/1000000000000000:ℝ) ≤ thetaSecondMode (3/512:ℝ) ∧
      thetaSecondMode (3/512:ℝ) ≤ (3016029499/500000000000000:ℝ) := by
  have hfirst : (83530129021509/1000000000000000:ℝ) ≤ thetaFirstMode (3/512:ℝ) ∧
      thetaFirstMode (3/512:ℝ) ≤ (8353012902151/100000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/512:ℝ) (1011787683559331/1000000000000000:ℝ) (252946920889833/250000000000000:ℝ)
      (83530129021509/1000000000000000:ℝ) (8353012902151/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (6032058997/1000000000000000:ℝ) ≤ thetaSecondMode (3/512:ℝ) ∧
      thetaSecondMode (3/512:ℝ) ≤ (3016029499/500000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/512:ℝ) (1011787683559331/1000000000000000:ℝ) (252946920889833/250000000000000:ℝ)
      (6032058997/1000000000000000:ℝ) (3016029499/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0022 :
    (8305319918113/100000000000000:ℝ) ≤ thetaFirstMode (7/1024:ℝ) ∧
      thetaFirstMode (7/1024:ℝ) ≤ (20763299795283/250000000000000:ℝ) ∧
      (1177368081/200000000000000:ℝ) ≤ thetaSecondMode (7/1024:ℝ) ∧
      thetaSecondMode (7/1024:ℝ) ≤ (2943420203/500000000000000:ℝ) := by
  have hfirst : (8305319918113/100000000000000:ℝ) ≤ thetaFirstMode (7/1024:ℝ) ∧
      thetaFirstMode (7/1024:ℝ) ≤ (20763299795283/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (7/1024:ℝ) (253441440616913/250000000000000:ℝ) (1013765762467653/1000000000000000:ℝ)
      (8305319918113/100000000000000:ℝ) (20763299795283/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1177368081/200000000000000:ℝ) ≤ thetaSecondMode (7/1024:ℝ) ∧
      thetaSecondMode (7/1024:ℝ) ≤ (2943420203/500000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (7/1024:ℝ) (253441440616913/250000000000000:ℝ) (1013765762467653/1000000000000000:ℝ)
      (1177368081/200000000000000:ℝ) (2943420203/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0023 :
    (10376021654923/125000000000000:ℝ) ≤ thetaFirstMode (525/75776:ℝ) ∧
      thetaFirstMode (525/75776:ℝ) ≤ (16601634647877/200000000000000:ℝ) ∧
      (5873271069/1000000000000000:ℝ) ≤ thetaSecondMode (525/75776:ℝ) ∧
      thetaSecondMode (525/75776:ℝ) ≤ (587327107/100000000000000:ℝ) := by
  have hfirst : (10376021654923/125000000000000:ℝ) ≤ thetaFirstMode (525/75776:ℝ) ∧
      thetaFirstMode (525/75776:ℝ) ≤ (16601634647877/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (525/75776:ℝ) (1013953078132821/1000000000000000:ℝ) (506976539066411/500000000000000:ℝ)
      (10376021654923/125000000000000:ℝ) (16601634647877/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5873271069/1000000000000000:ℝ) ≤ thetaSecondMode (525/75776:ℝ) ∧
      thetaSecondMode (525/75776:ℝ) ≤ (587327107/100000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (525/75776:ℝ) (1013953078132821/1000000000000000:ℝ) (506976539066411/500000000000000:ℝ)
      (5873271069/1000000000000000:ℝ) (587327107/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0024 :
    (82965045022209/1000000000000000:ℝ) ≤ thetaFirstMode (16835/2399232:ℝ) ∧
      thetaFirstMode (16835/2399232:ℝ) ≤ (8296504502221/100000000000000:ℝ) ∧
      (2930148123/500000000000000:ℝ) ≤ thetaSecondMode (16835/2399232:ℝ) ∧
      thetaSecondMode (16835/2399232:ℝ) ≤ (5860296247/1000000000000000:ℝ) := by
  have hfirst : (82965045022209/1000000000000000:ℝ) ≤ thetaFirstMode (16835/2399232:ℝ) ∧
      thetaFirstMode (16835/2399232:ℝ) ≤ (8296504502221/100000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (16835/2399232:ℝ) (31691643483373/31250000000000:ℝ) (1014132591467937/1000000000000000:ℝ)
      (82965045022209/1000000000000000:ℝ) (8296504502221/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2930148123/500000000000000:ℝ) ≤ thetaSecondMode (16835/2399232:ℝ) ∧
      thetaSecondMode (16835/2399232:ℝ) ≤ (5860296247/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (16835/2399232:ℝ) (31691643483373/31250000000000:ℝ) (1014132591467937/1000000000000000:ℝ)
      (2930148123/500000000000000:ℝ) (5860296247/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0025 :
    (82924921996421/1000000000000000:ℝ) ≤ thetaFirstMode (412825/58150912:ℝ) ∧
      thetaFirstMode (412825/58150912:ℝ) ≤ (41462460998211/500000000000000:ℝ) ∧
      (1462061337/250000000000000:ℝ) ≤ thetaSecondMode (412825/58150912:ℝ) ∧
      thetaSecondMode (412825/58150912:ℝ) ≤ (5848245349/1000000000000000:ℝ) := by
  have hfirst : (82924921996421/1000000000000000:ℝ) ≤ thetaFirstMode (412825/58150912:ℝ) ∧
      thetaFirstMode (412825/58150912:ℝ) ≤ (41462460998211/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (412825/58150912:ℝ) (8114397420969/8000000000000:ℝ) (507149838810563/500000000000000:ℝ)
      (82924921996421/1000000000000000:ℝ) (41462460998211/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1462061337/250000000000000:ℝ) ≤ thetaSecondMode (412825/58150912:ℝ) ∧
      thetaSecondMode (412825/58150912:ℝ) ≤ (5848245349/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (412825/58150912:ℝ) (8114397420969/8000000000000:ℝ) (507149838810563/500000000000000:ℝ)
      (1462061337/250000000000000:ℝ) (5848245349/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0026 :
    (82888522935521/1000000000000000:ℝ) ≤ thetaFirstMode (8905743/1241400320:ℝ) ∧
      thetaFirstMode (8905743/1241400320:ℝ) ≤ (41444261467761/500000000000000:ℝ) ∧
      (5837329459/1000000000000000:ℝ) ≤ thetaSecondMode (8905743/1241400320:ℝ) ∧
      thetaSecondMode (8905743/1241400320:ℝ) ≤ (291866473/50000000000000:ℝ) := by
  have hfirst : (82888522935521/1000000000000000:ℝ) ≤ thetaFirstMode (8905743/1241400320:ℝ) ∧
      thetaFirstMode (8905743/1241400320:ℝ) ≤ (41444261467761/500000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (8905743/1241400320:ℝ) (1014451323820441/1000000000000000:ℝ) (507225661910221/500000000000000:ℝ)
      (82888522935521/1000000000000000:ℝ) (41444261467761/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5837329459/1000000000000000:ℝ) ≤ thetaSecondMode (8905743/1241400320:ℝ) ∧
      thetaSecondMode (8905743/1241400320:ℝ) ≤ (291866473/50000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (8905743/1241400320:ℝ) (1014451323820441/1000000000000000:ℝ) (507225661910221/500000000000000:ℝ)
      (5837329459/1000000000000000:ℝ) (291866473/50000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0027 :
    (5178510536143/62500000000000:ℝ) ≤ thetaFirstMode (178703525/24681412608:ℝ) ∧
      thetaFirstMode (178703525/24681412608:ℝ) ≤ (8285616857829/100000000000000:ℝ) ∧
      (2913819867/500000000000000:ℝ) ≤ thetaSecondMode (178703525/24681412608:ℝ) ∧
      thetaSecondMode (178703525/24681412608:ℝ) ≤ (1165527947/200000000000000:ℝ) := by
  have hfirst : (5178510536143/62500000000000:ℝ) ≤ thetaFirstMode (178703525/24681412608:ℝ) ∧
      thetaFirstMode (178703525/24681412608:ℝ) ≤ (8285616857829/100000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (178703525/24681412608:ℝ) (253646543305271/250000000000000:ℝ) (202917234644217/200000000000000:ℝ)
      (5178510536143/62500000000000:ℝ) (8285616857829/100000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2913819867/500000000000000:ℝ) ≤ thetaSecondMode (178703525/24681412608:ℝ) ∧
      thetaSecondMode (178703525/24681412608:ℝ) ≤ (1165527947/200000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (178703525/24681412608:ℝ) (253646543305271/250000000000000:ℝ) (202917234644217/200000000000000:ℝ)
      (2913819867/500000000000000:ℝ) (1165527947/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0028 :
    (41288994596097/500000000000000:ℝ) ≤ thetaFirstMode (1/128:ℝ) ∧
      thetaFirstMode (1/128:ℝ) ≤ (20644497298049/250000000000000:ℝ) ∧
      (1148967737/200000000000000:ℝ) ≤ thetaSecondMode (1/128:ℝ) ∧
      thetaSecondMode (1/128:ℝ) ≤ (2872419343/500000000000000:ℝ) := by
  have hfirst : (41288994596097/500000000000000:ℝ) ≤ thetaFirstMode (1/128:ℝ) ∧
      thetaFirstMode (1/128:ℝ) ≤ (20644497298049/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/128:ℝ) (203149541717337/200000000000000:ℝ) (507873854293343/500000000000000:ℝ)
      (41288994596097/500000000000000:ℝ) (20644497298049/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (1148967737/200000000000000:ℝ) ≤ thetaSecondMode (1/128:ℝ) ∧
      thetaSecondMode (1/128:ℝ) ≤ (2872419343/500000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/128:ℝ) (203149541717337/200000000000000:ℝ) (507873854293343/500000000000000:ℝ)
      (1148967737/200000000000000:ℝ) (2872419343/500000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0029 :
    (82104498777719/1000000000000000:ℝ) ≤ thetaFirstMode (9/1024:ℝ) ∧
      thetaFirstMode (9/1024:ℝ) ≤ (2052612469443/25000000000000:ℝ) ∧
      (2802994671/500000000000000:ℝ) ≤ thetaSecondMode (9/1024:ℝ) ∧
      thetaSecondMode (9/1024:ℝ) ≤ (5605989343/1000000000000000:ℝ) := by
  have hfirst : (82104498777719/1000000000000000:ℝ) ≤ thetaFirstMode (9/1024:ℝ) ∧
      thetaFirstMode (9/1024:ℝ) ≤ (2052612469443/25000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9/1024:ℝ) (254433382369239/250000000000000:ℝ) (1017733529476957/1000000000000000:ℝ)
      (82104498777719/1000000000000000:ℝ) (2052612469443/25000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (2802994671/500000000000000:ℝ) ≤ thetaSecondMode (9/1024:ℝ) ∧
      thetaSecondMode (9/1024:ℝ) ≤ (5605989343/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9/1024:ℝ) (254433382369239/250000000000000:ℝ) (1017733529476957/1000000000000000:ℝ)
      (2802994671/500000000000000:ℝ) (5605989343/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0030 :
    (82069637254703/1000000000000000:ℝ) ≤ thetaFirstMode (1107/124928:ℝ) ∧
      thetaFirstMode (1107/124928:ℝ) ≤ (16413927450941/200000000000000:ℝ) ∧
      (559586947/100000000000000:ℝ) ≤ thetaSecondMode (1107/124928:ℝ) ∧
      thetaSecondMode (1107/124928:ℝ) ≤ (5595869471/1000000000000000:ℝ) := by
  have hfirst : (82069637254703/1000000000000000:ℝ) ≤ thetaFirstMode (1107/124928:ℝ) ∧
      thetaFirstMode (1107/124928:ℝ) ≤ (16413927450941/200000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1107/124928:ℝ) (1017880178133277/1000000000000000:ℝ) (508940089066639/500000000000000:ℝ)
      (82069637254703/1000000000000000:ℝ) (16413927450941/200000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (559586947/100000000000000:ℝ) ≤ thetaSecondMode (1107/124928:ℝ) ∧
      thetaSecondMode (1107/124928:ℝ) ≤ (5595869471/1000000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1107/124928:ℝ) (1017880178133277/1000000000000000:ℝ) (508940089066639/500000000000000:ℝ)
      (559586947/100000000000000:ℝ) (5595869471/1000000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0031 :
    (16407136148567/200000000000000:ℝ) ≤ thetaFirstMode (19215/2151424:ℝ) ∧
      thetaFirstMode (19215/2151424:ℝ) ≤ (20508920185709/250000000000000:ℝ) ∧
      (5586025843/1000000000000000:ℝ) ≤ thetaSecondMode (19215/2151424:ℝ) ∧
      thetaSecondMode (19215/2151424:ℝ) ≤ (1396506461/250000000000000:ℝ) := by
  have hfirst : (16407136148567/200000000000000:ℝ) ≤ thetaFirstMode (19215/2151424:ℝ) ∧
      thetaFirstMode (19215/2151424:ℝ) ≤ (20508920185709/250000000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (19215/2151424:ℝ) (1018023077942377/1000000000000000:ℝ) (509011538971189/500000000000000:ℝ)
      (16407136148567/200000000000000:ℝ) (20508920185709/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (5586025843/1000000000000000:ℝ) ≤ thetaSecondMode (19215/2151424:ℝ) ∧
      thetaSecondMode (19215/2151424:ℝ) ≤ (1396506461/250000000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (19215/2151424:ℝ) (1018023077942377/1000000000000000:ℝ) (509011538971189/500000000000000:ℝ)
      (5586025843/1000000000000000:ℝ) (1396506461/250000000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

end
end CarrySelfAdjointOperator

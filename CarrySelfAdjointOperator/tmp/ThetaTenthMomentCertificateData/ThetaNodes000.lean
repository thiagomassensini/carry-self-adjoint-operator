import CarrySelfAdjointOperator.CompletedNativeThetaSecondModeQuadrature

namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem thetaTenth_node_0000 :
    (172855673/2000000000:ℝ) ≤ thetaFirstMode (0/1:ℝ) ∧
      thetaFirstMode (0/1:ℝ) ≤ (432139183/5000000000:ℝ) ∧
      (34873/5000000000:ℝ) ≤ thetaSecondMode (0/1:ℝ) ∧
      thetaSecondMode (0/1:ℝ) ≤ (69747/10000000000:ℝ) := by
  have hfirst : (172855673/2000000000:ℝ) ≤ thetaFirstMode (0/1:ℝ) ∧
      thetaFirstMode (0/1:ℝ) ≤ (432139183/5000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (0/1:ℝ) (1/1:ℝ) (1/1:ℝ)
      (172855673/2000000000:ℝ) (432139183/5000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (34873/5000000000:ℝ) ≤ thetaSecondMode (0/1:ℝ) ∧
      thetaSecondMode (0/1:ℝ) ≤ (69747/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (0/1:ℝ) (1/1:ℝ) (1/1:ℝ)
      (34873/5000000000:ℝ) (69747/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0001 :
    (376946299/10000000000:ℝ) ≤ thetaFirstMode (1/8:ℝ) ∧
      thetaFirstMode (1/8:ℝ) ≤ (3769463/100000000:ℝ) ∧
      (523/2500000000:ℝ) ≤ thetaSecondMode (1/8:ℝ) ∧
      thetaSecondMode (1/8:ℝ) ≤ (2093/10000000000:ℝ) := by
  have hfirst : (376946299/10000000000:ℝ) ≤ thetaFirstMode (1/8:ℝ) ∧
      thetaFirstMode (1/8:ℝ) ≤ (3769463/100000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/8:ℝ) (6420127083/5000000000:ℝ) (12840254167/10000000000:ℝ)
      (376946299/10000000000:ℝ) (3769463/100000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (523/2500000000:ℝ) ≤ thetaSecondMode (1/8:ℝ) ∧
      thetaSecondMode (1/8:ℝ) ≤ (2093/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/8:ℝ) (6420127083/5000000000:ℝ) (12840254167/10000000000:ℝ)
      (523/2500000000:ℝ) (2093/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0002 :
    (113647327/5000000000:ℝ) ≤ thetaFirstMode (3/16:ℝ) ∧
      thetaFirstMode (3/16:ℝ) ≤ (45458931/2000000000:ℝ) ∧
      (251/10000000000:ℝ) ≤ thetaSecondMode (3/16:ℝ) ∧
      thetaSecondMode (3/16:ℝ) ≤ (63/2500000000:ℝ) := by
  have hfirst : (113647327/5000000000:ℝ) ≤ thetaFirstMode (3/16:ℝ) ∧
      thetaFirstMode (3/16:ℝ) ≤ (45458931/2000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/16:ℝ) (7274957073/5000000000:ℝ) (14549914147/10000000000:ℝ)
      (113647327/5000000000:ℝ) (45458931/2000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (251/10000000000:ℝ) ≤ thetaSecondMode (3/16:ℝ) ∧
      thetaSecondMode (3/16:ℝ) ≤ (63/2500000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/16:ℝ) (7274957073/5000000000:ℝ) (14549914147/10000000000:ℝ)
      (251/10000000000:ℝ) (63/2500000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0003 :
    (189082303/10000000000:ℝ) ≤ thetaFirstMode (5/24:ℝ) ∧
      thetaFirstMode (5/24:ℝ) ≤ (2954411/156250000:ℝ) ∧
      (29/2500000000:ℝ) ≤ thetaSecondMode (5/24:ℝ) ∧
      thetaSecondMode (5/24:ℝ) ≤ (117/10000000000:ℝ) := by
  have hfirst : (189082303/10000000000:ℝ) ≤ thetaFirstMode (5/24:ℝ) ∧
      thetaFirstMode (5/24:ℝ) ≤ (2954411/156250000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5/24:ℝ) (15168967963/10000000000:ℝ) (3792241991/2500000000:ℝ)
      (189082303/10000000000:ℝ) (2954411/156250000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (29/2500000000:ℝ) ≤ thetaSecondMode (5/24:ℝ) ∧
      thetaSecondMode (5/24:ℝ) ≤ (117/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5/24:ℝ) (15168967963/10000000000:ℝ) (3792241991/2500000000:ℝ)
      (29/2500000000:ℝ) (117/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0004 :
    (6877071/400000000:ℝ) ≤ thetaFirstMode (7/32:ℝ) ∧
      thetaFirstMode (7/32:ℝ) ≤ (21490847/1250000000:ℝ) ∧
      (39/5000000000:ℝ) ≤ thetaSecondMode (7/32:ℝ) ∧
      thetaSecondMode (7/32:ℝ) ≤ (79/10000000000:ℝ) := by
  have hfirst : (6877071/400000000:ℝ) ≤ thetaFirstMode (7/32:ℝ) ∧
      thetaFirstMode (7/32:ℝ) ≤ (21490847/1250000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (7/32:ℝ) (7744151493/5000000000:ℝ) (15488302987/10000000000:ℝ)
      (6877071/400000000:ℝ) (21490847/1250000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (39/5000000000:ℝ) ≤ thetaSecondMode (7/32:ℝ) ∧
      thetaSecondMode (7/32:ℝ) ≤ (79/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (7/32:ℝ) (7744151493/5000000000:ℝ) (15488302987/10000000000:ℝ)
      (39/5000000000:ℝ) (79/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0005 :
    (162225851/10000000000:ℝ) ≤ thetaFirstMode (9/40:ℝ) ∧
      thetaFirstMode (9/40:ℝ) ≤ (40556463/2500000000:ℝ) ∧
      (61/10000000000:ℝ) ≤ thetaSecondMode (9/40:ℝ) ∧
      thetaSecondMode (9/40:ℝ) ≤ (31/5000000000:ℝ) := by
  have hfirst : (162225851/10000000000:ℝ) ≤ thetaFirstMode (9/40:ℝ) ∧
      thetaFirstMode (9/40:ℝ) ≤ (40556463/2500000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9/40:ℝ) (7841560927/5000000000:ℝ) (3136624371/2000000000:ℝ)
      (162225851/10000000000:ℝ) (40556463/2500000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (61/10000000000:ℝ) ≤ thetaSecondMode (9/40:ℝ) ∧
      thetaSecondMode (9/40:ℝ) ≤ (31/5000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9/40:ℝ) (7841560927/5000000000:ℝ) (3136624371/2000000000:ℝ)
      (61/10000000000:ℝ) (31/5000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0006 :
    (155997967/10000000000:ℝ) ≤ thetaFirstMode (11/48:ℝ) ∧
      thetaFirstMode (11/48:ℝ) ≤ (9749873/625000000:ℝ) ∧
      (13/2500000000:ℝ) ≤ thetaSecondMode (11/48:ℝ) ∧
      thetaSecondMode (11/48:ℝ) ≤ (53/10000000000:ℝ) := by
  have hfirst : (155997967/10000000000:ℝ) ≤ thetaFirstMode (11/48:ℝ) ∧
      thetaFirstMode (11/48:ℝ) ≤ (9749873/625000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (11/48:ℝ) (3162872121/2000000000:ℝ) (7907180303/5000000000:ℝ)
      (155997967/10000000000:ℝ) (9749873/625000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (13/2500000000:ℝ) ≤ thetaSecondMode (11/48:ℝ) ∧
      thetaSecondMode (11/48:ℝ) ≤ (53/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (11/48:ℝ) (3162872121/2000000000:ℝ) (7907180303/5000000000:ℝ)
      (13/2500000000:ℝ) (53/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0007 :
    (127597007/10000000000:ℝ) ≤ thetaFirstMode (1/4:ℝ) ∧
      thetaFirstMode (1/4:ℝ) ≤ (7974813/625000000:ℝ) ∧
      (11/5000000000:ℝ) ≤ thetaSecondMode (1/4:ℝ) ∧
      thetaSecondMode (1/4:ℝ) ≤ (23/10000000000:ℝ) := by
  have hfirst : (127597007/10000000000:ℝ) ≤ thetaFirstMode (1/4:ℝ) ∧
      thetaFirstMode (1/4:ℝ) ≤ (7974813/625000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/4:ℝ) (16487212707/10000000000:ℝ) (4121803177/2500000000:ℝ)
      (127597007/10000000000:ℝ) (7974813/625000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (11/5000000000:ℝ) ≤ thetaSecondMode (1/4:ℝ) ∧
      thetaSecondMode (1/4:ℝ) ≤ (23/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/4:ℝ) (16487212707/10000000000:ℝ) (4121803177/2500000000:ℝ)
      (11/5000000000:ℝ) (23/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0008 :
    (15597157/5000000000:ℝ) ≤ thetaFirstMode (3/8:ℝ) ∧
      thetaFirstMode (3/8:ℝ) ≤ (6238863/2000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (3/8:ℝ) ∧
      thetaSecondMode (3/8:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (15597157/5000000000:ℝ) ≤ thetaFirstMode (3/8:ℝ) ∧
      thetaFirstMode (3/8:ℝ) ≤ (6238863/2000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/8:ℝ) (10585000083/5000000000:ℝ) (21170000167/10000000000:ℝ)
      (15597157/5000000000:ℝ) (6238863/2000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (3/8:ℝ) ∧
      thetaSecondMode (3/8:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/8:ℝ) (10585000083/5000000000:ℝ) (21170000167/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0009 :
    (21924883/10000000000:ℝ) ≤ thetaFirstMode (45/112:ℝ) ∧
      thetaFirstMode (45/112:ℝ) ≤ (5481221/2500000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (45/112:ℝ) ∧
      thetaSecondMode (45/112:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (21924883/10000000000:ℝ) ≤ thetaFirstMode (45/112:ℝ) ∧
      thetaFirstMode (45/112:ℝ) ≤ (5481221/2500000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (45/112:ℝ) (22335034993/10000000000:ℝ) (11167517497/5000000000:ℝ)
      (21924883/10000000000:ℝ) (5481221/2500000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (45/112:ℝ) ∧
      thetaSecondMode (45/112:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (45/112:ℝ) (22335034993/10000000000:ℝ) (11167517497/5000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0010 :
    (8129413/5000000000:ℝ) ≤ thetaFirstMode (105/248:ℝ) ∧
      thetaFirstMode (105/248:ℝ) ≤ (16258827/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (105/248:ℝ) ∧
      thetaSecondMode (105/248:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (8129413/5000000000:ℝ) ≤ thetaFirstMode (105/248:ℝ) ∧
      thetaFirstMode (105/248:ℝ) ≤ (16258827/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (105/248:ℝ) (23321117639/10000000000:ℝ) (583027941/250000000:ℝ)
      (8129413/5000000000:ℝ) (16258827/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (105/248:ℝ) ∧
      thetaSecondMode (105/248:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (105/248:ℝ) (23321117639/10000000000:ℝ) (583027941/250000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0011 :
    (12946213/10000000000:ℝ) ≤ thetaFirstMode (1785/4064:ℝ) ∧
      thetaFirstMode (1785/4064:ℝ) ≤ (6473107/5000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (1785/4064:ℝ) ∧
      thetaSecondMode (1785/4064:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (12946213/10000000000:ℝ) ≤ thetaFirstMode (1785/4064:ℝ) ∧
      thetaFirstMode (1785/4064:ℝ) ≤ (6473107/5000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1785/4064:ℝ) (24071533863/10000000000:ℝ) (3008941733/1250000000:ℝ)
      (12946213/10000000000:ℝ) (6473107/5000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (1785/4064:ℝ) ∧
      thetaSecondMode (1785/4064:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1785/4064:ℝ) (24071533863/10000000000:ℝ) (3008941733/1250000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0012 :
    (5483161/5000000000:ℝ) ≤ thetaFirstMode (9207/20440:ℝ) ∧
      thetaFirstMode (9207/20440:ℝ) ≤ (10966323/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (9207/20440:ℝ) ∧
      thetaSecondMode (9207/20440:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (5483161/5000000000:ℝ) ≤ thetaFirstMode (9207/20440:ℝ) ∧
      thetaFirstMode (9207/20440:ℝ) ≤ (10966323/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (9207/20440:ℝ) (24617700561/10000000000:ℝ) (12308850281/5000000000:ℝ)
      (5483161/5000000000:ℝ) (10966323/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (9207/20440:ℝ) ∧
      thetaSecondMode (9207/20440:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (9207/20440:ℝ) (24617700561/10000000000:ℝ) (12308850281/5000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0013 :
    (9718351/10000000000:ℝ) ≤ thetaFirstMode (15015/32752:ℝ) ∧
      thetaFirstMode (15015/32752:ℝ) ≤ (607397/625000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (15015/32752:ℝ) ∧
      thetaSecondMode (15015/32752:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (9718351/10000000000:ℝ) ≤ thetaFirstMode (15015/32752:ℝ) ∧
      thetaFirstMode (15015/32752:ℝ) ≤ (607397/625000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (15015/32752:ℝ) (2501500049/1000000000:ℝ) (25015000491/10000000000:ℝ)
      (9718351/10000000000:ℝ) (607397/625000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (15015/32752:ℝ) ∧
      thetaSecondMode (15015/32752:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (15015/32752:ℝ) (2501500049/1000000000:ℝ) (25015000491/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0014 :
    (5021623/10000000000:ℝ) ≤ thetaFirstMode (1/2:ℝ) ∧
      thetaFirstMode (1/2:ℝ) ≤ (627703/1250000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (1/2:ℝ) ∧
      thetaSecondMode (1/2:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (5021623/10000000000:ℝ) ≤ thetaFirstMode (1/2:ℝ) ∧
      thetaFirstMode (1/2:ℝ) ≤ (627703/1250000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/2:ℝ) (6795704571/2500000000:ℝ) (5436563657/2000000000:ℝ)
      (5021623/10000000000:ℝ) (627703/1250000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (1/2:ℝ) ∧
      thetaSecondMode (1/2:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/2:ℝ) (6795704571/2500000000:ℝ) (5436563657/2000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0015 :
    (472721/10000000000:ℝ) ≤ thetaFirstMode (5/8:ℝ) ∧
      thetaFirstMode (5/8:ℝ) ≤ (236361/5000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (5/8:ℝ) ∧
      thetaSecondMode (5/8:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (472721/10000000000:ℝ) ≤ thetaFirstMode (5/8:ℝ) ∧
      thetaFirstMode (5/8:ℝ) ≤ (236361/5000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5/8:ℝ) (17451714787/5000000000:ℝ) (1396137183/400000000:ℝ)
      (472721/10000000000:ℝ) (236361/5000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (5/8:ℝ) ∧
      thetaSecondMode (5/8:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5/8:ℝ) (17451714787/5000000000:ℝ) (1396137183/400000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0016 :
    (33031/1000000000:ℝ) ≤ thetaFirstMode (195/304:ℝ) ∧
      thetaFirstMode (195/304:ℝ) ≤ (330311/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (195/304:ℝ) ∧
      thetaSecondMode (195/304:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (33031/1000000000:ℝ) ≤ thetaFirstMode (195/304:ℝ) ∧
      thetaFirstMode (195/304:ℝ) ≤ (330311/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (195/304:ℝ) (18035330673/5000000000:ℝ) (36070661347/10000000000:ℝ)
      (33031/1000000000:ℝ) (330311/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (195/304:ℝ) ∧
      thetaSecondMode (195/304:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (195/304:ℝ) (18035330673/5000000000:ℝ) (36070661347/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0017 :
    (234871/10000000000:ℝ) ≤ thetaFirstMode (3325/5064:ℝ) ∧
      thetaFirstMode (3325/5064:ℝ) ≤ (29359/1250000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (3325/5064:ℝ) ∧
      thetaSecondMode (3325/5064:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (234871/10000000000:ℝ) ≤ thetaFirstMode (3325/5064:ℝ) ∧
      thetaFirstMode (3325/5064:ℝ) ≤ (29359/1250000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3325/5064:ℝ) (37180195713/10000000000:ℝ) (18590097857/5000000000:ℝ)
      (234871/10000000000:ℝ) (29359/1250000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (3325/5064:ℝ) ∧
      thetaSecondMode (3325/5064:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3325/5064:ℝ) (37180195713/10000000000:ℝ) (18590097857/5000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0018 :
    (86381/5000000000:ℝ) ≤ thetaFirstMode (44135/65888:ℝ) ∧
      thetaFirstMode (44135/65888:ℝ) ≤ (172763/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (44135/65888:ℝ) ∧
      thetaSecondMode (44135/65888:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (86381/5000000000:ℝ) ≤ thetaFirstMode (44135/65888:ℝ) ∧
      thetaFirstMode (44135/65888:ℝ) ≤ (172763/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (44135/65888:ℝ) (38178890637/10000000000:ℝ) (19089445319/5000000000:ℝ)
      (86381/5000000000:ℝ) (172763/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (44135/65888:ℝ) ∧
      thetaSecondMode (44135/65888:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (44135/65888:ℝ) (38178890637/10000000000:ℝ) (19089445319/5000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0019 :
    (33131/2500000000:ℝ) ≤ thetaFirstMode (104445/153368:ℝ) ∧
      thetaFirstMode (104445/153368:ℝ) ≤ (5301/400000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (104445/153368:ℝ) ∧
      thetaSecondMode (104445/153368:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (33131/2500000000:ℝ) ≤ thetaFirstMode (104445/153368:ℝ) ∧
      thetaFirstMode (104445/153368:ℝ) ≤ (5301/400000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (104445/153368:ℝ) (7808128707/2000000000:ℝ) (2440040221/625000000:ℝ)
      (33131/2500000000:ℝ) (5301/400000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (104445/153368:ℝ) ∧
      thetaSecondMode (104445/153368:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (104445/153368:ℝ) (7808128707/2000000000:ℝ) (2440040221/625000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0020 :
    (106091/10000000000:ℝ) ≤ thetaFirstMode (5800795/8404752:ℝ) ∧
      thetaFirstMode (5800795/8404752:ℝ) ≤ (26523/2500000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (5800795/8404752:ℝ) ∧
      thetaSecondMode (5800795/8404752:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (106091/10000000000:ℝ) ≤ thetaFirstMode (5800795/8404752:ℝ) ∧
      thetaFirstMode (5800795/8404752:ℝ) ≤ (26523/2500000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (5800795/8404752:ℝ) (39763359387/10000000000:ℝ) (9940839847/2500000000:ℝ)
      (106091/10000000000:ℝ) (26523/2500000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (5800795/8404752:ℝ) ∧
      thetaSecondMode (5800795/8404752:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (5800795/8404752:ℝ) (39763359387/10000000000:ℝ) (9940839847/2500000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0021 :
    (2793/1250000000:ℝ) ≤ thetaFirstMode (3/4:ℝ) ∧
      thetaFirstMode (3/4:ℝ) ≤ (4469/2000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (3/4:ℝ) ∧
      thetaSecondMode (3/4:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (2793/1250000000:ℝ) ≤ thetaFirstMode (3/4:ℝ) ∧
      thetaFirstMode (3/4:ℝ) ≤ (4469/2000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (3/4:ℝ) (44816890703/10000000000:ℝ) (2801055669/625000000:ℝ)
      (2793/1250000000:ℝ) (4469/2000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (3/4:ℝ) ∧
      thetaSecondMode (3/4:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (3/4:ℝ) (44816890703/10000000000:ℝ) (2801055669/625000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0022 :
    (109/2500000000:ℝ) ≤ thetaFirstMode (7/8:ℝ) ∧
      thetaFirstMode (7/8:ℝ) ≤ (437/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (7/8:ℝ) ∧
      thetaSecondMode (7/8:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (109/2500000000:ℝ) ≤ thetaFirstMode (7/8:ℝ) ∧
      thetaFirstMode (7/8:ℝ) ≤ (437/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (7/8:ℝ) (1438650669/250000000:ℝ) (57546026761/10000000000:ℝ)
      (109/2500000000:ℝ) (437/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (7/8:ℝ) ∧
      thetaSecondMode (7/8:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (7/8:ℝ) (1438650669/250000000:ℝ) (57546026761/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0023 :
    (71/2500000000:ℝ) ≤ thetaFirstMode (525/592:ℝ) ∧
      thetaFirstMode (525/592:ℝ) ≤ (57/2000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (525/592:ℝ) ∧
      thetaSecondMode (525/592:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (71/2500000000:ℝ) ≤ thetaFirstMode (525/592:ℝ) ∧
      thetaFirstMode (525/592:ℝ) ≤ (57/2000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (525/592:ℝ) (14730782921/2500000000:ℝ) (11784626337/2000000000:ℝ)
      (71/2500000000:ℝ) (57/2000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (525/592:ℝ) ∧
      thetaSecondMode (525/592:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (525/592:ℝ) (14730782921/2500000000:ℝ) (11784626337/2000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0024 :
    (187/10000000000:ℝ) ≤ thetaFirstMode (16835/18744:ℝ) ∧
      thetaFirstMode (16835/18744:ℝ) ≤ (47/2500000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (16835/18744:ℝ) ∧
      thetaSecondMode (16835/18744:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (187/10000000000:ℝ) ≤ thetaFirstMode (16835/18744:ℝ) ∧
      thetaFirstMode (16835/18744:ℝ) ≤ (47/2500000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (16835/18744:ℝ) (3013677131/500000000:ℝ) (60273542621/10000000000:ℝ)
      (187/10000000000:ℝ) (47/2500000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (16835/18744:ℝ) ∧
      thetaSecondMode (16835/18744:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (16835/18744:ℝ) (3013677131/500000000:ℝ) (60273542621/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0025 :
    (1/80000000:ℝ) ≤ thetaFirstMode (412825/454304:ℝ) ∧
      thetaFirstMode (412825/454304:ℝ) ≤ (63/5000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (412825/454304:ℝ) ∧
      thetaSecondMode (412825/454304:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (1/80000000:ℝ) ≤ thetaFirstMode (412825/454304:ℝ) ∧
      thetaFirstMode (412825/454304:ℝ) ≤ (63/5000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (412825/454304:ℝ) (30779020733/5000000000:ℝ) (61558041467/10000000000:ℝ)
      (1/80000000:ℝ) (63/5000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (412825/454304:ℝ) ∧
      thetaSecondMode (412825/454304:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (412825/454304:ℝ) (30779020733/5000000000:ℝ) (61558041467/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0026 :
    (43/5000000000:ℝ) ≤ thetaFirstMode (8905743/9698440:ℝ) ∧
      thetaFirstMode (8905743/9698440:ℝ) ≤ (87/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (8905743/9698440:ℝ) ∧
      thetaSecondMode (8905743/9698440:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (43/5000000000:ℝ) ≤ thetaFirstMode (8905743/9698440:ℝ) ∧
      thetaFirstMode (8905743/9698440:ℝ) ≤ (87/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (8905743/9698440:ℝ) (62747335987/10000000000:ℝ) (15686833997/2500000000:ℝ)
      (43/5000000000:ℝ) (87/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (8905743/9698440:ℝ) ∧
      thetaSecondMode (8905743/9698440:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (8905743/9698440:ℝ) (62747335987/10000000000:ℝ) (15686833997/2500000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0027 :
    (31/5000000000:ℝ) ≤ thetaFirstMode (178703525/192823536:ℝ) ∧
      thetaFirstMode (178703525/192823536:ℝ) ≤ (63/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (178703525/192823536:ℝ) ∧
      thetaSecondMode (178703525/192823536:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (31/5000000000:ℝ) ≤ thetaFirstMode (178703525/192823536:ℝ) ∧
      thetaFirstMode (178703525/192823536:ℝ) ≤ (63/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (178703525/192823536:ℝ) (15956008507/2500000000:ℝ) (63824034029/10000000000:ℝ)
      (31/5000000000:ℝ) (63/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (178703525/192823536:ℝ) ∧
      thetaSecondMode (178703525/192823536:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (178703525/192823536:ℝ) (15956008507/2500000000:ℝ) (63824034029/10000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem thetaTenth_node_0028 :
    (1/5000000000:ℝ) ≤ thetaFirstMode (1/1:ℝ) ∧
      thetaFirstMode (1/1:ℝ) ≤ (3/10000000000:ℝ) ∧
      (0/1:ℝ) ≤ thetaSecondMode (1/1:ℝ) ∧
      thetaSecondMode (1/1:ℝ) ≤ (1/10000000000:ℝ) := by
  have hfirst : (1/5000000000:ℝ) ≤ thetaFirstMode (1/1:ℝ) ∧
      thetaFirstMode (1/1:ℝ) ≤ (3/10000000000:ℝ) := by
    apply thetaFirstMode_node_bounds_d20 (1/1:ℝ) (73890560989/10000000000:ℝ) (7389056099/1000000000:ℝ)
      (1/5000000000:ℝ) (3/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]
  have hsecond : (0/1:ℝ) ≤ thetaSecondMode (1/1:ℝ) ∧
      thetaSecondMode (1/1:ℝ) ≤ (1/10000000000:ℝ) := by
    apply thetaSecondMode_node_bounds_d20 (1/1:ℝ) (73890560989/10000000000:ℝ) (7389056099/1000000000:ℝ)
      (0/1:ℝ) (1/10000000000:ℝ)
    all_goals norm_num [thetaExpLower, thetaExpUpper, thetaExpLower128,
      thetaExpUpper128, Finset.sum_range_succ]
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

end
end CarrySelfAdjointOperator

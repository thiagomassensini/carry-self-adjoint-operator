import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds

namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000

theorem thetaFirstMode_node_000 :
    (21606951647/250000000000:ℝ) ≤ thetaFirstMode (0/1:ℝ) ∧ thetaFirstMode (0/1:ℝ) ≤ (10803486627/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (0/1:ℝ) (1/1:ℝ) (1/1:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_001 :
    (42244559843/500000000000:ℝ) ≤ thetaFirstMode (1/256:ℝ) ∧ thetaFirstMode (1/256:ℝ) ≤ (16897840973/200000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/256:ℝ) (2519607743/2500000000:ℝ) (10078430973/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_002 :
    (41765049867/500000000000:ℝ) ≤ thetaFirstMode (3/512:ℝ) ∧ thetaFirstMode (3/512:ℝ) ≤ (20882546069/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3/512:ℝ) (2023575367/2000000000:ℝ) (2529469209/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_003 :
    (83211955461/1000000000000:ℝ) ≤ thetaFirstMode (5/768:ℝ) ∧ thetaFirstMode (5/768:ℝ) ≤ (83212039791/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (5/768:ℝ) (2026211947/2000000000:ℝ) (1266382467/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_004 :
    (20644490033/250000000000:ℝ) ≤ thetaFirstMode (1/128:ℝ) ∧ thetaFirstMode (1/128:ℝ) ≤ (82578044037/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/128:ℝ) (2031495417/2000000000:ℝ) (5078738543/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_005 :
    (80694313103/1000000000000:ℝ) ≤ thetaFirstMode (3/256:ℝ) ∧ thetaFirstMode (3/256:ℝ) ≤ (80694395737/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3/256:ℝ) (5118571583/5000000000:ℝ) (10237143167/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_006 :
    (8029425187/100000000000:ℝ) ≤ thetaFirstMode (45/3584:ℝ) ∧ thetaFirstMode (45/3584:ℝ) ≤ (10036791779/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (45/3584:ℝ) (5127147797/5000000000:ℝ) (2050859119/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_007 :
    (1999313529/25000000000:ℝ) ≤ thetaFirstMode (105/7936:ℝ) ∧ thetaFirstMode (105/7936:ℝ) ≤ (9996577913/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (105/7936:ℝ) (1283518641/1250000000:ℝ) (10268149129/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_008 :
    (7883815599/100000000000:ℝ) ≤ thetaFirstMode (1/64:ℝ) ∧ thetaFirstMode (1/64:ℝ) ≤ (19709559339/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/64:ℝ) (5158717037/5000000000:ℝ) (412697363/400000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_009 :
    (77009458073/1000000000000:ℝ) ≤ thetaFirstMode (5/256:ℝ) ∧ thetaFirstMode (5/256:ℝ) ≤ (601637017/7812500000:ℝ) := by
  apply thetaFirstMode_node_bounds (5/256:ℝ) (10398354713/10000000000:ℝ) (5199177357/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_010 :
    (19192720553/250000000000:ℝ) ≤ thetaFirstMode (195/9728:ℝ) ∧ thetaFirstMode (195/9728:ℝ) ≤ (76770962149/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (195/9728:ℝ) (10409049307/10000000000:ℝ) (2602262327/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_011 :
    (7655157111/100000000000:ℝ) ≤ thetaFirstMode (3325/162048:ℝ) ∧ thetaFirstMode (3325/162048:ℝ) ≤ (76551650893/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3325/162048:ℝ) (2604727219/2500000000:ℝ) (10418908877/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_012 :
    (601665447/8000000000:ℝ) ≤ thetaFirstMode (3/128:ℝ) ∧ thetaFirstMode (3/128:ℝ) ≤ (37604129859/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3/128:ℝ) (523995501/500000000:ℝ) (10479910021/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_013 :
    (73434278003/1000000000000:ℝ) ≤ thetaFirstMode (7/256:ℝ) ∧ thetaFirstMode (7/256:ℝ) ≤ (73434355589/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (7/256:ℝ) (10562104973/10000000000:ℝ) (5281052487/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_014 :
    (14653578341/200000000000:ℝ) ≤ thetaFirstMode (525/18944:ℝ) ∧ thetaFirstMode (525/18944:ℝ) ≤ (73267969173/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (525/18944:ℝ) (10569913467/10000000000:ℝ) (2642478367/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_015 :
    (2924347763/40000000000:ℝ) ≤ thetaFirstMode (16835/599808:ℝ) ∧ thetaFirstMode (16835/599808:ℝ) ≤ (73108771429/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (16835/599808:ℝ) (5288700387/5000000000:ℝ) (423096031/400000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_016 :
    (8960961907/125000000000:ℝ) ≤ thetaFirstMode (1/32:ℝ) ∧ thetaFirstMode (1/32:ℝ) ≤ (71687771591/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/32:ℝ) (10644944589/10000000000:ℝ) (1064494459/1000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_017 :
    (17492092671/250000000000:ℝ) ≤ thetaFirstMode (9/256:ℝ) ∧ thetaFirstMode (9/256:ℝ) ≤ (17492111443/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (9/256:ℝ) (2682108481/2500000000:ℝ) (429137357/400000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_018 :
    (69842613013/1000000000000:ℝ) ≤ thetaFirstMode (1107/31232:ℝ) ∧ thetaFirstMode (1107/31232:ℝ) ≤ (69842688009/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1107/31232:ℝ) (2146923769/2000000000:ℝ) (5367309423/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_019 :
    (34860114917/500000000000:ℝ) ≤ thetaFirstMode (19215/537856:ℝ) ∧ thetaFirstMode (19215/537856:ℝ) ≤ (69720304741/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (19215/537856:ℝ) (10740648231/10000000000:ℝ) (1342581029/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_020 :
    (533408083/7812500000:ℝ) ≤ thetaFirstMode (5/128:ℝ) ∧ thetaFirstMode (5/128:ℝ) ≤ (6827630847/100000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (5/128:ℝ) (5406289037/5000000000:ℝ) (432503123/400000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_021 :
    (66611209773/1000000000000:ℝ) ≤ thetaFirstMode (11/256:ℝ) ∧ thetaFirstMode (11/256:ℝ) ≤ (4163205149/62500000000:ℝ) := by
  apply thetaFirstMode_node_bounds (11/256:ℝ) (435895287/400000000:ℝ) (340543193/312500000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_022 :
    (1039241303/15625000000:ℝ) ≤ thetaFirstMode (2013/46592:ℝ) ∧ thetaFirstMode (2013/46592:ℝ) ≤ (8313939491/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (2013/46592:ℝ) (34070403/31250000:ℝ) (10902528961/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_023 :
    (13282700699/200000000000:ℝ) ≤ thetaFirstMode (155155/3571968:ℝ) ∧ thetaFirstMode (155155/3571968:ℝ) ≤ (33206787979/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (155155/3571968:ℝ) (681724303/625000000:ℝ) (10907588849/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_024 :
    (32486605629/500000000000:ℝ) ≤ thetaFirstMode (3/64:ℝ) ∧ thetaFirstMode (3/64:ℝ) ≤ (32486641319/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3/64:ℝ) (10982851403/10000000000:ℝ) (2745712851/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_025 :
    (7920268339/125000000000:ℝ) ≤ thetaFirstMode (13/256:ℝ) ∧ thetaFirstMode (13/256:ℝ) ≤ (63362216869/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (13/256:ℝ) (5534495487/5000000000:ℝ) (442759639/400000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_026 :
    (7910051673/125000000000:ℝ) ≤ thetaFirstMode (3315/65024:ℝ) ∧ thetaFirstMode (3315/65024:ℝ) ≤ (31640241739/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3315/65024:ℝ) (11073417821/10000000000:ℝ) (5536708911/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_027 :
    (7899971087/125000000000:ℝ) ≤ thetaFirstMode (354965/6935808:ℝ) ∧ thetaFirstMode (354965/6935808:ℝ) ≤ (63199838729/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (354965/6935808:ℝ) (5538895589/5000000000:ℝ) (11077791179/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_028 :
    (61777916317/1000000000000:ℝ) ≤ thetaFirstMode (7/128:ℝ) ∧ thetaFirstMode (7/128:ℝ) ≤ (7722248157/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (7/128:ℝ) (5577903073/5000000000:ℝ) (11155806147/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_029 :
    (6022041291/100000000000:ℝ) ≤ thetaFirstMode (15/256:ℝ) ∧ thetaFirstMode (15/256:ℝ) ≤ (30110240319/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (15/256:ℝ) (5621651109/5000000000:ℝ) (11243302219/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_030 :
    (30075955267/500000000000:ℝ) ≤ thetaFirstMode (5085/86528:ℝ) ∧ thetaFirstMode (5085/86528:ℝ) ≤ (1879749319/31250000000:ℝ) := by
  apply thetaFirstMode_node_bounds (5085/86528:ℝ) (11247201043/10000000000:ℝ) (2811800261/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_031 :
    (15021025897/250000000000:ℝ) ≤ thetaFirstMode (240825/4086016:ℝ) ∧ thetaFirstMode (240825/4086016:ℝ) ≤ (60084171209/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (240825/4086016:ℝ) (11251064561/10000000000:ℝ) (5625532281/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

end CarrySelfAdjointOperator

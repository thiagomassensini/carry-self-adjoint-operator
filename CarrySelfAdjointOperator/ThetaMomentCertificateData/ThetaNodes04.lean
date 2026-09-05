import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds

namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000

theorem thetaFirstMode_node_128 :
    (12759693487/1000000000000:ℝ) ≤ thetaFirstMode (1/4:ℝ) ∧ thetaFirstMode (1/4:ℝ) ≤ (12759714529/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/4:ℝ) (16487212707/10000000000:ℝ) (4121803177/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_129 :
    (12275681449/1000000000000:ℝ) ≤ thetaFirstMode (65/256:ℝ) ∧ thetaFirstMode (65/256:ℝ) ≤ (3068925463/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (65/256:ℝ) (8308261759/5000000000:ℝ) (16616523519/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_130 :
    (1533849217/125000000000:ℝ) ≤ thetaFirstMode (412035/1622528:ℝ) ∧ thetaFirstMode (412035/1622528:ℝ) ≤ (3067703533/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (412035/1622528:ℝ) (16617854919/10000000000:ℝ) (415446373/250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_131 :
    (6132955013/500000000000:ℝ) ≤ thetaFirstMode (1088630725/4286178048:ℝ) ∧ thetaFirstMode (1088630725/4286178048:ℝ) ≤ (766620651/62500000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1088630725/4286178048:ℝ) (8309592877/5000000000:ℝ) (3323837151/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_132 :
    (5903133537/500000000000:ℝ) ≤ thetaFirstMode (33/128:ℝ) ∧ thetaFirstMode (33/128:ℝ) ≤ (236125737/20000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (33/128:ℝ) (1046678033/625000000:ℝ) (16746848529/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_133 :
    (11351157161/1000000000000:ℝ) ≤ thetaFirstMode (67/256:ℝ) ∧ thetaFirstMode (67/256:ℝ) ≤ (454047053/40000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (67/256:ℝ) (16878195689/10000000000:ℝ) (1687819569/1000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_134 :
    (5673349963/500000000000:ℝ) ≤ thetaFirstMode (451245/1723904:ℝ) ∧ thetaFirstMode (451245/1723904:ℝ) ≤ (2836679771/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (451245/1723904:ℝ) (16879507691/10000000000:ℝ) (4219876923/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_135 :
    (5671123097/500000000000:ℝ) ≤ thetaFirstMode (1266682235/4838423808:ℝ) ∧ thetaFirstMode (1266682235/4838423808:ℝ) ≤ (2268453069/200000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1266682235/4838423808:ℝ) (4220204793/2500000000:ℝ) (16880819173/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_136 :
    (10910059431/1000000000000:ℝ) ≤ thetaFirstMode (17/64:ℝ) ∧ thetaFirstMode (17/64:ℝ) ≤ (5455038997/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (17/64:ℝ) (8505286509/5000000000:ℝ) (17010573019/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_137 :
    (5241341343/500000000000:ℝ) ≤ thetaFirstMode (69/256:ℝ) ∧ thetaFirstMode (69/256:ℝ) ≤ (5241350331/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (69/256:ℝ) (4285997149/2500000000:ℝ) (17143988597/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_138 :
    (2095723941/200000000000:ℝ) ≤ thetaFirstMode (492867/1828352:ℝ) ∧ thetaFirstMode (492867/1828352:ℝ) ≤ (2619659419/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (492867/1828352:ℝ) (3429056527/2000000000:ℝ) (4286320659/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_139 :
    (5237279897/500000000000:ℝ) ≤ thetaFirstMode (489102015/1814131456:ℝ) ∧ thetaFirstMode (489102015/1814131456:ℝ) ≤ (5237288879/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (489102015/1814131456:ℝ) (17146576193/10000000000:ℝ) (8573288097/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_140 :
    (5034368489/500000000000:ℝ) ≤ thetaFirstMode (35/128:ℝ) ∧ thetaFirstMode (35/128:ℝ) ≤ (10068754379/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (35/128:ℝ) (3455690113/2000000000:ℝ) (8639225283/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_141 :
    (1933586749/200000000000:ℝ) ≤ thetaFirstMode (71/256:ℝ) ∧ thetaFirstMode (71/256:ℝ) ≤ (1208493823/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (71/256:ℝ) (4353491783/2500000000:ℝ) (17413967133/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_142 :
    (4832115973/500000000000:ℝ) ≤ thetaFirstMode (536973/1935872:ℝ) ∧ thetaFirstMode (536973/1935872:ℝ) ≤ (483212439/50000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (536973/1935872:ℝ) (1088452783/625000000:ℝ) (17415244529/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_143 :
    (9660532849/1000000000000:ℝ) ≤ thetaFirstMode (1692583555/6101223168:ℝ) ∧ thetaFirstMode (1692583555/6101223168:ℝ) ≤ (4830274839/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1692583555/6101223168:ℝ) (4354130369/2500000000:ℝ) (17416521477/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_144 :
    (1855997193/200000000000:ℝ) ≤ thetaFirstMode (9/32:ℝ) ∧ thetaFirstMode (9/32:ℝ) ≤ (580000141/62500000000:ℝ) := by
  apply thetaFirstMode_node_bounds (9/32:ℝ) (17550546569/10000000000:ℝ) (1755054657/1000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_145 :
    (1780921661/200000000000:ℝ) ≤ thetaFirstMode (73/256:ℝ) ∧ thetaFirstMode (73/256:ℝ) ≤ (8904624059/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (73/256:ℝ) (4422049303/2500000000:ℝ) (17688197213/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_146 :
    (556327341/62500000000:ℝ) ≤ thetaFirstMode (583635/2046464:ℝ) ∧ thetaFirstMode (583635/2046464:ℝ) ≤ (4450626603/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (583635/2046464:ℝ) (8844729589/5000000000:ℝ) (17689459179/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_147 :
    (8897868977/1000000000000:ℝ) ≤ thetaFirstMode (1944720365/6818135808:ℝ) ∧ thetaFirstMode (1944720365/6818135808:ℝ) ≤ (4448942361/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1944720365/6818135808:ℝ) (1769072073/1000000000:ℝ) (17690720731/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_148 :
    (1708303451/200000000000:ℝ) ≤ thetaFirstMode (37/128:ℝ) ∧ thetaFirstMode (37/128:ℝ) ≤ (4270766243/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (37/128:ℝ) (8913463731/5000000000:ℝ) (17826927463/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_149 :
    (8190431269/1000000000000:ℝ) ≤ thetaFirstMode (75/256:ℝ) ∧ thetaFirstMode (75/256:ℝ) ≤ (2047611497/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (75/256:ℝ) (17966745787/10000000000:ℝ) (4491686447/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_150 :
    (2046840919/250000000000:ℝ) ≤ thetaFirstMode (632925/2160128:ℝ) ∧ thetaFirstMode (632925/2160128:ℝ) ≤ (818737839/100000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (632925/2160128:ℝ) (17967993447/10000000000:ℝ) (2245999181/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_151 :
    (818429817/100000000000:ℝ) ≤ thetaFirstMode (742016625/2532150016:ℝ) ∧ thetaFirstMode (742016625/2532150016:ℝ) ≤ (102303911/12500000000:ℝ) := by
  apply thetaFirstMode_node_bounds (742016625/2532150016:ℝ) (17969240721/10000000000:ℝ) (8984620361/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_152 :
    (490691931/62500000000:ℝ) ≤ thetaFirstMode (19/64:ℝ) ∧ thetaFirstMode (19/64:ℝ) ≤ (1962771279/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (19/64:ℝ) (18107660721/10000000000:ℝ) (9053830361/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_153 :
    (3761579459/500000000000:ℝ) ≤ thetaFirstMode (77/256:ℝ) ∧ thetaFirstMode (77/256:ℝ) ≤ (7523172651/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (77/256:ℝ) (570302527/312500000:ℝ) (3649936173/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_154 :
    (1504073839/200000000000:ℝ) ≤ thetaFirstMode (684915/2276864:ℝ) ∧ thetaFirstMode (684915/2276864:ℝ) ≤ (1880095731/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (684915/2276864:ℝ) (18250915257/10000000000:ℝ) (9125457629/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_155 :
    (7517581311/1000000000000:ℝ) ≤ thetaFirstMode (2539036885/8439575808:ℝ) ∧ thetaFirstMode (2539036885/8439575808:ℝ) ≤ (1879398759/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (2539036885/8439575808:ℝ) (1825214929/1000000000:ℝ) (18252149291/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_156 :
    (1441284093/200000000000:ℝ) ≤ thetaFirstMode (39/128:ℝ) ∧ thetaFirstMode (39/128:ℝ) ≤ (3603216861/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (39/128:ℝ) (3678562977/2000000000:ℝ) (9196407443/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_157 :
    (3450291571/500000000000:ℝ) ≤ thetaFirstMode (79/256:ℝ) ∧ thetaFirstMode (79/256:ℝ) ≤ (6900595937/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (79/256:ℝ) (115856697/62500000:ℝ) (18537071521/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_158 :
    (3449023993/500000000000:ℝ) ≤ thetaFirstMode (739677/2396672:ℝ) ∧ thetaFirstMode (739677/2396672:ℝ) ≤ (6898060777/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (739677/2396672:ℝ) (4634573403/2500000000:ℝ) (18538293613/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_159 :
    (1723878613/250000000000:ℝ) ≤ thetaFirstMode (2886281195/9351015168:ℝ) ∧ thetaFirstMode (2886281195/9351015168:ℝ) ≤ (172388181/25000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (2886281195/9351015168:ℝ) (18539515367/10000000000:ℝ) (2317439421/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

end CarrySelfAdjointOperator

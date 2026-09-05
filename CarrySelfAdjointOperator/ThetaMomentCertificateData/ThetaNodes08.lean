import CarrySelfAdjointOperator.CompletedNativeThetaExponentialBounds

namespace CarrySelfAdjointOperator
set_option maxHeartbeats 4000000

theorem thetaFirstMode_node_256 :
    (251080949/500000000000:ℝ) ≤ thetaFirstMode (1/2:ℝ) ∧ thetaFirstMode (1/2:ℝ) ≤ (7846301/15625000000:ℝ) := by
  apply thetaFirstMode_node_bounds (1/2:ℝ) (6795704571/2500000000:ℝ) (5436563657/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_257 :
    (470547883/1000000000000:ℝ) ≤ thetaFirstMode (129/256:ℝ) ∧ thetaFirstMode (129/256:ℝ) ≤ (235274587/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (129/256:ℝ) (2739601577/1000000000:ℝ) (27396015771/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_258 :
    (470389147/1000000000000:ℝ) ≤ thetaFirstMode (3220227/6390272:ℝ) ∧ thetaFirstMode (3220227/6390272:ℝ) ≤ (470390437/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3220227/6390272:ℝ) (6849280469/2500000000:ℝ) (27397121877/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_259 :
    (470230479/1000000000000:ℝ) ≤ thetaFirstMode (11165689815/22156493056:ℝ) ∧ thetaFirstMode (11165689815/22156493056:ℝ) ≤ (58778971/125000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (11165689815/22156493056:ℝ) (6849556971/2500000000:ℝ) (5479645577/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_260 :
    (27543287/62500000000:ℝ) ≤ thetaFirstMode (65/128:ℝ) ∧ thetaFirstMode (65/128:ℝ) ≤ (44069381/100000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (65/128:ℝ) (5522177077/2000000000:ℝ) (13805442693/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_261 :
    (412513101/1000000000000:ℝ) ≤ thetaFirstMode (131/256:ℝ) ∧ thetaFirstMode (131/256:ℝ) ≤ (1650057/4000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (131/256:ℝ) (27827440243/10000000000:ℝ) (6956860061/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_262 :
    (103093461/250000000000:ℝ) ≤ thetaFirstMode (3372333/6589952:ℝ) ∧ thetaFirstMode (3372333/6589952:ℝ) ≤ (412374993/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3372333/6589952:ℝ) (13914273307/5000000000:ℝ) (5565709323/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_263 :
    (412234647/1000000000000:ℝ) ≤ thetaFirstMode (36175296955/70688218368:ℝ) ∧ thetaFirstMode (36175296955/70688218368:ℝ) ≤ (82447159/200000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (36175296955/70688218368:ℝ) (6957413223/2500000000:ℝ) (27829652893/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_264 :
    (385929527/1000000000000:ℝ) ≤ thetaFirstMode (33/64:ℝ) ∧ thetaFirstMode (33/64:ℝ) ≤ (38593061/100000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (33/64:ℝ) (14022846781/5000000000:ℝ) (28045693563/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_265 :
    (180432481/500000000000:ℝ) ≤ thetaFirstMode (133/256:ℝ) ∧ thetaFirstMode (133/256:ℝ) ≤ (360865983/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (133/256:ℝ) (28265658663/10000000000:ℝ) (3533207333/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_266 :
    (90185757/250000000000:ℝ) ≤ thetaFirstMode (3529155/6792704:ℝ) ∧ thetaFirstMode (3529155/6792704:ℝ) ≤ (360744049/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3529155/6792704:ℝ) (14133382779/5000000000:ℝ) (28266765559/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_267 :
    (72124229/200000000000:ℝ) ≤ thetaFirstMode (39022160765/75104663808:ℝ) ∧ thetaFirstMode (39022160765/75104663808:ℝ) ≤ (72124433/200000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (39022160765/75104663808:ℝ) (28267872363/10000000000:ℝ) (7066968091/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_268 :
    (337245407/1000000000000:ℝ) ≤ thetaFirstMode (67/128:ℝ) ∧ thetaFirstMode (67/128:ℝ) ≤ (337246369/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (67/128:ℝ) (28487348971/10000000000:ℝ) (7121837243/2500000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_269 :
    (3149997/10000000000:ℝ) ≤ thetaFirstMode (135/256:ℝ) ∧ thetaFirstMode (135/256:ℝ) ≤ (157500303/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (135/256:ℝ) (14355389009/5000000000:ℝ) (28710778019/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_270 :
    (314893141/1000000000000:ℝ) ≤ thetaFirstMode (3690765/6998528:ℝ) ∧ thetaFirstMode (3690765/6998528:ℝ) ≤ (157447023/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3690765/6998528:ℝ) (3588985711/1250000000:ℝ) (28711885689/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_271 :
    (314786627/1000000000000:ℝ) ≤ thetaFirstMode (14015167425/26574966016:ℝ) ∧ thetaFirstMode (14015167425/26574966016:ℝ) ≤ (78696883/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (14015167425/26574966016:ℝ) (28712993271/10000000000:ℝ) (3589124159/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_272 :
    (58811891/200000000000:ℝ) ≤ thetaFirstMode (17/32:ℝ) ∧ thetaFirstMode (17/32:ℝ) ≤ (294060307/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (17/32:ℝ) (28935959441/10000000000:ℝ) (14467979721/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_273 :
    (137179493/500000000000:ℝ) ≤ thetaFirstMode (137/256:ℝ) ∧ thetaFirstMode (137/256:ℝ) ≤ (274359787/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (137/256:ℝ) (3645363373/1250000000:ℝ) (5832581397/2000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_274 :
    (274266049/1000000000000:ℝ) ≤ thetaFirstMode (3857235/7207424:ℝ) ∧ thetaFirstMode (3857235/7207424:ℝ) ≤ (5485337/20000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (3857235/7207424:ℝ) (3645501959/1250000000:ℝ) (29164015673/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_275 :
    (5483463/20000000000:ℝ) ≤ thetaFirstMode (45253402285/84555095808:ℝ) ∧ thetaFirstMode (45253402285/84555095808:ℝ) ≤ (274173951/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (45253402285/84555095808:ℝ) (29165124277/10000000000:ℝ) (14582562139/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_276 :
    (127917623/500000000000:ℝ) ≤ thetaFirstMode (69/128:ℝ) ∧ thetaFirstMode (69/128:ℝ) ≤ (255835999/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (69/128:ℝ) (14695817249/5000000000:ℝ) (29391634499/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_277 :
    (238427751/1000000000000:ℝ) ≤ thetaFirstMode (139/256:ℝ) ∧ thetaFirstMode (139/256:ℝ) ≤ (238428459/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (139/256:ℝ) (5924431189/2000000000:ℝ) (14811077973/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_278 :
    (238346859/1000000000000:ℝ) ≤ thetaFirstMode (4028637/7419392:ℝ) ∧ thetaFirstMode (4028637/7419392:ℝ) ≤ (119173783/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (4028637/7419392:ℝ) (29623265889/10000000000:ℝ) (2962326589/1000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_279 :
    (119133/500000000:ℝ) ≤ thetaFirstMode (48654184595/89601523968:ℝ) ∧ thetaFirstMode (48654184595/89601523968:ℝ) ≤ (238266707/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (48654184595/89601523968:ℝ) (29624375753/10000000000:ℝ) (14812187877/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_280 :
    (111039259/500000000000:ℝ) ≤ thetaFirstMode (35/64:ℝ) ∧ thetaFirstMode (35/64:ℝ) ≤ (111039591/500000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (35/64:ℝ) (29854485393/10000000000:ℝ) (14927242697/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_281 :
    (206731989/1000000000000:ℝ) ≤ thetaFirstMode (141/256:ℝ) ∧ thetaFirstMode (141/256:ℝ) ≤ (51683153/250000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (141/256:ℝ) (940269907/312500000:ℝ) (1203545481/400000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_282 :
    (103330863/500000000000:ℝ) ≤ thetaFirstMode (4205043/7634432:ℝ) ∧ thetaFirstMode (4205043/7634432:ℝ) ≤ (206662349/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (4205043/7634432:ℝ) (3761218557/1250000000:ℝ) (30089748457/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_283 :
    (51647873/250000000000:ℝ) ≤ thetaFirstMode (17418806535/31623513856:ℝ) ∧ thetaFirstMode (17418806535/31623513856:ℝ) ≤ (41318423/200000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (17418806535/31623513856:ℝ) (3009085981/1000000000:ℝ) (30090859811/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_284 :
    (192334969/1000000000000:ℝ) ≤ thetaFirstMode (71/128:ℝ) ∧ thetaFirstMode (71/128:ℝ) ≤ (192335553/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (71/128:ℝ) (30324625129/10000000000:ℝ) (3032462513/1000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_285 :
    (178836553/1000000000000:ℝ) ≤ thetaFirstMode (143/256:ℝ) ∧ thetaFirstMode (143/256:ℝ) ≤ (178837101/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (143/256:ℝ) (1910154007/625000000:ℝ) (30562464113/10000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_286 :
    (44693913/250000000000:ℝ) ≤ thetaFirstMode (4386525/7852544:ℝ) ∧ thetaFirstMode (4386525/7852544:ℝ) ≤ (178776199/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (4386525/7852544:ℝ) (30563577257/10000000000:ℝ) (15281788629/5000000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

theorem thetaFirstMode_node_287 :
    (22339347/125000000000:ℝ) ≤ thetaFirstMode (56068927915/100368599808:ℝ) ∧ thetaFirstMode (56068927915/100368599808:ℝ) ≤ (178715323/1000000000000:ℝ) := by
  apply thetaFirstMode_node_bounds (56068927915/100368599808:ℝ) (30564690327/10000000000:ℝ) (3820586291/1250000000:ℝ)
  all_goals norm_num [thetaExpLower, thetaExpUpper, Finset.sum_range_succ]

end CarrySelfAdjointOperator

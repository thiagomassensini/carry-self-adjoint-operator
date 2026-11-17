import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block00
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block01
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block02
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block03
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block04
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block05
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block06
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block07
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block08
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block09
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block10
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block11
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block12
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block13
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block14
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block15
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block16
import CarrySelfAdjointOperator.ThetaSixteenthFloorCertificateData.Block17
import Mathlib.Tactic

open scoped BigOperators
open MeasureTheory
namespace CarrySelfAdjointOperator
noncomputable section
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384

def theta16FloorQ : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 0
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 0
  | 42 => 0
  | 43 => 0
  | 44 => 0
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 0
  | 55 => 0
  | 56 => 0
  | 57 => 0
  | 58 => 0
  | 59 => 0
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 0
  | 64 => 0
  | 65 => 0
  | 66 => 0
  | 67 => 0
  | 68 => 0
  | 69 => 0
  | 70 => 1
  | 71 => 1
  | 72 => 1
  | 73 => 2
  | 74 => 2
  | 75 => 3
  | 76 => 3
  | 77 => 4
  | 78 => 5
  | 79 => 6
  | 80 => 7
  | 81 => 9
  | 82 => 11
  | 83 => 13
  | 84 => 16
  | 85 => 19
  | 86 => 22
  | 87 => 26
  | 88 => 31
  | 89 => 37
  | 90 => 43
  | 91 => 51
  | 92 => 60
  | 93 => 70
  | 94 => 81
  | 95 => 95
  | 96 => 110
  | 97 => 128
  | 98 => 148
  | 99 => 171
  | 100 => 197
  | 101 => 227
  | 102 => 261
  | 103 => 300
  | 104 => 344
  | 105 => 394
  | 106 => 450
  | 107 => 514
  | 108 => 586
  | 109 => 666
  | 110 => 757
  | 111 => 859
  | 112 => 974
  | 113 => 1102
  | 114 => 1245
  | 115 => 1405
  | 116 => 1584
  | 117 => 1783
  | 118 => 2005
  | 119 => 2251
  | 120 => 2525
  | 121 => 2829
  | 122 => 3165
  | 123 => 3538
  | 124 => 3950
  | 125 => 4405
  | 126 => 4907
  | 127 => 5461
  | 128 => 6070
  | 129 => 6741
  | 130 => 7478
  | 131 => 8286
  | 132 => 9173
  | 133 => 10145
  | 134 => 11209
  | 135 => 12373
  | 136 => 13644
  | 137 => 15032
  | 138 => 16545
  | 139 => 18194
  | 140 => 19990
  | 141 => 21942
  | 142 => 24065
  | 143 => 26370
  | 144 => 28870
  | 145 => 31581
  | 146 => 34517
  | 147 => 37695
  | 148 => 41132
  | 149 => 44845
  | 150 => 48855
  | 151 => 53181
  | 152 => 57844
  | 153 => 62868
  | 154 => 68276
  | 155 => 74092
  | 156 => 80344
  | 157 => 87059
  | 158 => 94266
  | 159 => 101995
  | 160 => 110279
  | 161 => 119150
  | 162 => 128645
  | 163 => 138800
  | 164 => 149652
  | 165 => 161244
  | 166 => 173615
  | 167 => 186811
  | 168 => 200877
  | 169 => 215860
  | 170 => 231809
  | 171 => 248777
  | 172 => 266817
  | 173 => 285984
  | 174 => 306335
  | 175 => 327932
  | 176 => 350835
  | 177 => 375109
  | 178 => 400821
  | 179 => 428038
  | 180 => 456833
  | 181 => 487277
  | 182 => 519448
  | 183 => 553422
  | 184 => 589280
  | 185 => 627105
  | 186 => 666981
  | 187 => 708995
  | 188 => 753239
  | 189 => 799802
  | 190 => 848780
  | 191 => 900269
  | 192 => 954369
  | 193 => 1011179
  | 194 => 1070804
  | 195 => 1133349
  | 196 => 1198921
  | 197 => 1267630
  | 198 => 1339589
  | 199 => 1414909
  | 200 => 1493708
  | 201 => 1576101
  | 202 => 1662209
  | 203 => 1752152
  | 204 => 1846052
  | 205 => 1944032
  | 206 => 2046218
  | 207 => 2152736
  | 208 => 2263713
  | 209 => 2379276
  | 210 => 2499556
  | 211 => 2624681
  | 212 => 2754781
  | 213 => 2889989
  | 214 => 3030433
  | 215 => 3176244
  | 216 => 3327555
  | 217 => 3484493
  | 218 => 3647190
  | 219 => 3815774
  | 220 => 3990374
  | 221 => 4171116
  | 222 => 4358126
  | 223 => 4551527
  | 224 => 4751443
  | 225 => 4957994
  | 226 => 5171296
  | 227 => 5391467
  | 228 => 5618617
  | 229 => 5852859
  | 230 => 6094296
  | 231 => 6343034
  | 232 => 6599171
  | 233 => 6862802
  | 234 => 7134018
  | 235 => 7412906
  | 236 => 7699547
  | 237 => 7994018
  | 238 => 8296390
  | 239 => 8606730
  | 240 => 8925096
  | 241 => 9251543
  | 242 => 9586118
  | 243 => 9928861
  | 244 => 10279808
  | 245 => 10638984
  | 246 => 11006409
  | 247 => 11382094
  | 248 => 11766044
  | 249 => 12158255
  | 250 => 12558714
  | 251 => 12967401
  | 252 => 13384285
  | 253 => 13809328
  | 254 => 14242482
  | 255 => 14683692
  | 256 => 15132889
  | 257 => 15589998
  | 258 => 16054934
  | 259 => 16527600
  | 260 => 17007891
  | 261 => 17495691
  | 262 => 17990873
  | 263 => 18493302
  | 264 => 19002830
  | 265 => 19519299
  | 266 => 20042543
  | 267 => 20572382
  | 268 => 21108628
  | 269 => 21651080
  | 270 => 22199529
  | 271 => 22753754
  | 272 => 23313524
  | 273 => 23878598
  | 274 => 24448723
  | 275 => 25023639
  | 276 => 25603072
  | 277 => 26186741
  | 278 => 26774355
  | 279 => 27365611
  | 280 => 27960200
  | 281 => 28557801
  | 282 => 29158087
  | 283 => 29760718
  | 284 => 30365350
  | 285 => 30971628
  | 286 => 31579190
  | 287 => 32187667
  | 288 => 32796682
  | 289 => 33405852
  | 290 => 34014786
  | 291 => 34623089
  | 292 => 35230359
  | 293 => 35836188
  | 294 => 36440164
  | 295 => 37041871
  | 296 => 37640889
  | 297 => 38236793
  | 298 => 38829157
  | 299 => 39417551
  | 300 => 40001543
  | 301 => 40580700
  | 302 => 41154587
  | 303 => 41722771
  | 304 => 42284816
  | 305 => 42840287
  | 306 => 43388752
  | 307 => 43929779
  | 308 => 44462939
  | 309 => 44987804
  | 310 => 45503952
  | 311 => 46010962
  | 312 => 46508420
  | 313 => 46995915
  | 314 => 47473043
  | 315 => 47939403
  | 316 => 48394605
  | 317 => 48838263
  | 318 => 49269998
  | 319 => 49689443
  | 320 => 50096235
  | 321 => 50490023
  | 322 => 50870465
  | 323 => 51237230
  | 324 => 51589995
  | 325 => 51928450
  | 326 => 52252297
  | 327 => 52561249
  | 328 => 52855032
  | 329 => 53133382
  | 330 => 53396052
  | 331 => 53642807
  | 332 => 53873425
  | 333 => 54087699
  | 334 => 54285435
  | 335 => 54466456
  | 336 => 54630599
  | 337 => 54777716
  | 338 => 54907674
  | 339 => 55020356
  | 340 => 55115662
  | 341 => 55193506
  | 342 => 55253819
  | 343 => 55296549
  | 344 => 55321659
  | 345 => 55329128
  | 346 => 55318954
  | 347 => 55291147
  | 348 => 55245738
  | 349 => 55182772
  | 350 => 55102308
  | 351 => 55004426
  | 352 => 54889218
  | 353 => 54756794
  | 354 => 54607279
  | 355 => 54440812
  | 356 => 54257551
  | 357 => 54057666
  | 358 => 53841342
  | 359 => 53608780
  | 360 => 53360194
  | 361 => 53095813
  | 362 => 52815879
  | 363 => 52520646
  | 364 => 52210384
  | 365 => 51885372
  | 366 => 51545904
  | 367 => 51192283
  | 368 => 50824824
  | 369 => 50443855
  | 370 => 50049712
  | 371 => 49642740
  | 372 => 49223296
  | 373 => 48791744
  | 374 => 48348456
  | 375 => 47893814
  | 376 => 47428204
  | 377 => 46952022
  | 378 => 46465667
  | 379 => 45969546
  | 380 => 45464071
  | 381 => 44949656
  | 382 => 44426723
  | 383 => 43895695
  | 384 => 43356996
  | 385 => 42811057
  | 386 => 42258307
  | 387 => 41699177
  | 388 => 41134101
  | 389 => 40563509
  | 390 => 39987835
  | 391 => 39407508
  | 392 => 38822959
  | 393 => 38234616
  | 394 => 37642903
  | 395 => 37048243
  | 396 => 36451054
  | 397 => 35851753
  | 398 => 35250749
  | 399 => 34648449
  | 400 => 34045254
  | 401 => 33441558
  | 402 => 32837752
  | 403 => 32234217
  | 404 => 31631331
  | 405 => 31029462
  | 406 => 30428971
  | 407 => 29830214
  | 408 => 29233535
  | 409 => 28639272
  | 410 => 28047754
  | 411 => 27459302
  | 412 => 26874225
  | 413 => 26292827
  | 414 => 25715399
  | 415 => 25142224
  | 416 => 24573575
  | 417 => 24009714
  | 418 => 23450895
  | 419 => 22897359
  | 420 => 22349340
  | 421 => 21807059
  | 422 => 21270728
  | 423 => 20740548
  | 424 => 20216710
  | 425 => 19699395
  | 426 => 19188771
  | 427 => 18684999
  | 428 => 18188228
  | 429 => 17698597
  | 430 => 17216234
  | 431 => 16741258
  | 432 => 16273777
  | 433 => 15813890
  | 434 => 15361686
  | 435 => 14917244
  | 436 => 14480633
  | 437 => 14051914
  | 438 => 13631139
  | 439 => 13218349
  | 440 => 12813578
  | 441 => 12416851
  | 442 => 12028183
  | 443 => 11647584
  | 444 => 11275055
  | 445 => 10910586
  | 446 => 10554165
  | 447 => 10205768
  | 448 => 9865366
  | 449 => 9532925
  | 450 => 9208401
  | 451 => 8891746
  | 452 => 8582906
  | 453 => 8281819
  | 454 => 7988421
  | 455 => 7702641
  | 456 => 7424402
  | 457 => 7153624
  | 458 => 6890222
  | 459 => 6634107
  | 460 => 6385184
  | 461 => 6143359
  | 462 => 5908529
  | 463 => 5680592
  | 464 => 5459442
  | 465 => 5244968
  | 466 => 5037060
  | 467 => 4835603
  | 468 => 4640482
  | 469 => 4451580
  | 470 => 4268776
  | 471 => 4091950
  | 472 => 3920981
  | 473 => 3755746
  | 474 => 3596121
  | 475 => 3441982
  | 476 => 3293206
  | 477 => 3149667
  | 478 => 3011240
  | 479 => 2877802
  | 480 => 2749228
  | 481 => 2625393
  | 482 => 2506176
  | 483 => 2391452
  | 484 => 2281101
  | 485 => 2175002
  | 486 => 2073035
  | 487 => 1975081
  | 488 => 1881023
  | 489 => 1790746
  | 490 => 1704134
  | 491 => 1621076
  | 492 => 1541460
  | 493 => 1465176
  | 494 => 1392117
  | 495 => 1322178
  | 496 => 1255253
  | 497 => 1191241
  | 498 => 1130042
  | 499 => 1071558
  | 500 => 1015693
  | 501 => 962353
  | 502 => 911446
  | 503 => 862883
  | 504 => 816576
  | 505 => 772439
  | 506 => 730391
  | 507 => 690349
  | 508 => 652234
  | 509 => 615970
  | 510 => 581483
  | 511 => 548700
  | 512 => 517550
  | 513 => 487966
  | 514 => 459881
  | 515 => 433231
  | 516 => 407955
  | 517 => 383992
  | 518 => 361284
  | 519 => 339775
  | 520 => 319411
  | 521 => 300140
  | 522 => 281912
  | 523 => 264677
  | 524 => 248389
  | 525 => 233004
  | 526 => 218477
  | 527 => 204767
  | 528 => 191835
  | 529 => 179641
  | 530 => 168149
  | 531 => 157323
  | 532 => 147129
  | 533 => 137535
  | 534 => 128511
  | 535 => 120025
  | 536 => 112050
  | 537 => 104558
  | 538 => 97523
  | 539 => 90921
  | 540 => 84728
  | 541 => 78921
  | 542 => 73479
  | 543 => 68381
  | 544 => 63608
  | 545 => 59141
  | 546 => 54963
  | 547 => 51056
  | 548 => 47406
  | 549 => 43996
  | 550 => 40812
  | 551 => 37841
  | 552 => 35070
  | 553 => 32487
  | 554 => 30080
  | 555 => 27838
  | 556 => 25751
  | 557 => 23809
  | 558 => 22004
  | 559 => 20325
  | 560 => 18766
  | 561 => 17318
  | 562 => 15974
  | 563 => 14727
  | 564 => 13571
  | 565 => 12500
  | 566 => 11507
  | 567 => 10588
  | 568 => 9738
  | 569 => 8952
  | 570 => 8225
  | 571 => 7553
  | 572 => 6933
  | 573 => 6361
  | 574 => 5833
  | 575 => 5346
  | _ => 0

def theta16FloorTerm (j : ℕ) : ℝ :=
  ((j : ℝ)/512)^2 *
    (∫ x in ((j : ℝ)/512)..(((j+1 : ℕ):ℝ)/512), x^14*thetaFirstMode x)

theorem theta16_floor_cell_bound (j : ℕ) (hj : j < 576) :
    ((theta16FloorQ j : ℝ) / 1000000000000000000) ≤ theta16FloorTerm j := by
  interval_cases j <;>
  simp [theta16FloorQ, theta16FloorTerm,
    theta16_floor_cell_000,
    theta16_floor_cell_001,
    theta16_floor_cell_002,
    theta16_floor_cell_003,
    theta16_floor_cell_004,
    theta16_floor_cell_005,
    theta16_floor_cell_006,
    theta16_floor_cell_007,
    theta16_floor_cell_008,
    theta16_floor_cell_009,
    theta16_floor_cell_010,
    theta16_floor_cell_011,
    theta16_floor_cell_012,
    theta16_floor_cell_013,
    theta16_floor_cell_014,
    theta16_floor_cell_015,
    theta16_floor_cell_016,
    theta16_floor_cell_017,
    theta16_floor_cell_018,
    theta16_floor_cell_019,
    theta16_floor_cell_020,
    theta16_floor_cell_021,
    theta16_floor_cell_022,
    theta16_floor_cell_023,
    theta16_floor_cell_024,
    theta16_floor_cell_025,
    theta16_floor_cell_026,
    theta16_floor_cell_027,
    theta16_floor_cell_028,
    theta16_floor_cell_029,
    theta16_floor_cell_030,
    theta16_floor_cell_031,
    theta16_floor_cell_032,
    theta16_floor_cell_033,
    theta16_floor_cell_034,
    theta16_floor_cell_035,
    theta16_floor_cell_036,
    theta16_floor_cell_037,
    theta16_floor_cell_038,
    theta16_floor_cell_039,
    theta16_floor_cell_040,
    theta16_floor_cell_041,
    theta16_floor_cell_042,
    theta16_floor_cell_043,
    theta16_floor_cell_044,
    theta16_floor_cell_045,
    theta16_floor_cell_046,
    theta16_floor_cell_047,
    theta16_floor_cell_048,
    theta16_floor_cell_049,
    theta16_floor_cell_050,
    theta16_floor_cell_051,
    theta16_floor_cell_052,
    theta16_floor_cell_053,
    theta16_floor_cell_054,
    theta16_floor_cell_055,
    theta16_floor_cell_056,
    theta16_floor_cell_057,
    theta16_floor_cell_058,
    theta16_floor_cell_059,
    theta16_floor_cell_060,
    theta16_floor_cell_061,
    theta16_floor_cell_062,
    theta16_floor_cell_063,
    theta16_floor_cell_064,
    theta16_floor_cell_065,
    theta16_floor_cell_066,
    theta16_floor_cell_067,
    theta16_floor_cell_068,
    theta16_floor_cell_069,
    theta16_floor_cell_070,
    theta16_floor_cell_071,
    theta16_floor_cell_072,
    theta16_floor_cell_073,
    theta16_floor_cell_074,
    theta16_floor_cell_075,
    theta16_floor_cell_076,
    theta16_floor_cell_077,
    theta16_floor_cell_078,
    theta16_floor_cell_079,
    theta16_floor_cell_080,
    theta16_floor_cell_081,
    theta16_floor_cell_082,
    theta16_floor_cell_083,
    theta16_floor_cell_084,
    theta16_floor_cell_085,
    theta16_floor_cell_086,
    theta16_floor_cell_087,
    theta16_floor_cell_088,
    theta16_floor_cell_089,
    theta16_floor_cell_090,
    theta16_floor_cell_091,
    theta16_floor_cell_092,
    theta16_floor_cell_093,
    theta16_floor_cell_094,
    theta16_floor_cell_095,
    theta16_floor_cell_096,
    theta16_floor_cell_097,
    theta16_floor_cell_098,
    theta16_floor_cell_099,
    theta16_floor_cell_100,
    theta16_floor_cell_101,
    theta16_floor_cell_102,
    theta16_floor_cell_103,
    theta16_floor_cell_104,
    theta16_floor_cell_105,
    theta16_floor_cell_106,
    theta16_floor_cell_107,
    theta16_floor_cell_108,
    theta16_floor_cell_109,
    theta16_floor_cell_110,
    theta16_floor_cell_111,
    theta16_floor_cell_112,
    theta16_floor_cell_113,
    theta16_floor_cell_114,
    theta16_floor_cell_115,
    theta16_floor_cell_116,
    theta16_floor_cell_117,
    theta16_floor_cell_118,
    theta16_floor_cell_119,
    theta16_floor_cell_120,
    theta16_floor_cell_121,
    theta16_floor_cell_122,
    theta16_floor_cell_123,
    theta16_floor_cell_124,
    theta16_floor_cell_125,
    theta16_floor_cell_126,
    theta16_floor_cell_127,
    theta16_floor_cell_128,
    theta16_floor_cell_129,
    theta16_floor_cell_130,
    theta16_floor_cell_131,
    theta16_floor_cell_132,
    theta16_floor_cell_133,
    theta16_floor_cell_134,
    theta16_floor_cell_135,
    theta16_floor_cell_136,
    theta16_floor_cell_137,
    theta16_floor_cell_138,
    theta16_floor_cell_139,
    theta16_floor_cell_140,
    theta16_floor_cell_141,
    theta16_floor_cell_142,
    theta16_floor_cell_143,
    theta16_floor_cell_144,
    theta16_floor_cell_145,
    theta16_floor_cell_146,
    theta16_floor_cell_147,
    theta16_floor_cell_148,
    theta16_floor_cell_149,
    theta16_floor_cell_150,
    theta16_floor_cell_151,
    theta16_floor_cell_152,
    theta16_floor_cell_153,
    theta16_floor_cell_154,
    theta16_floor_cell_155,
    theta16_floor_cell_156,
    theta16_floor_cell_157,
    theta16_floor_cell_158,
    theta16_floor_cell_159,
    theta16_floor_cell_160,
    theta16_floor_cell_161,
    theta16_floor_cell_162,
    theta16_floor_cell_163,
    theta16_floor_cell_164,
    theta16_floor_cell_165,
    theta16_floor_cell_166,
    theta16_floor_cell_167,
    theta16_floor_cell_168,
    theta16_floor_cell_169,
    theta16_floor_cell_170,
    theta16_floor_cell_171,
    theta16_floor_cell_172,
    theta16_floor_cell_173,
    theta16_floor_cell_174,
    theta16_floor_cell_175,
    theta16_floor_cell_176,
    theta16_floor_cell_177,
    theta16_floor_cell_178,
    theta16_floor_cell_179,
    theta16_floor_cell_180,
    theta16_floor_cell_181,
    theta16_floor_cell_182,
    theta16_floor_cell_183,
    theta16_floor_cell_184,
    theta16_floor_cell_185,
    theta16_floor_cell_186,
    theta16_floor_cell_187,
    theta16_floor_cell_188,
    theta16_floor_cell_189,
    theta16_floor_cell_190,
    theta16_floor_cell_191,
    theta16_floor_cell_192,
    theta16_floor_cell_193,
    theta16_floor_cell_194,
    theta16_floor_cell_195,
    theta16_floor_cell_196,
    theta16_floor_cell_197,
    theta16_floor_cell_198,
    theta16_floor_cell_199,
    theta16_floor_cell_200,
    theta16_floor_cell_201,
    theta16_floor_cell_202,
    theta16_floor_cell_203,
    theta16_floor_cell_204,
    theta16_floor_cell_205,
    theta16_floor_cell_206,
    theta16_floor_cell_207,
    theta16_floor_cell_208,
    theta16_floor_cell_209,
    theta16_floor_cell_210,
    theta16_floor_cell_211,
    theta16_floor_cell_212,
    theta16_floor_cell_213,
    theta16_floor_cell_214,
    theta16_floor_cell_215,
    theta16_floor_cell_216,
    theta16_floor_cell_217,
    theta16_floor_cell_218,
    theta16_floor_cell_219,
    theta16_floor_cell_220,
    theta16_floor_cell_221,
    theta16_floor_cell_222,
    theta16_floor_cell_223,
    theta16_floor_cell_224,
    theta16_floor_cell_225,
    theta16_floor_cell_226,
    theta16_floor_cell_227,
    theta16_floor_cell_228,
    theta16_floor_cell_229,
    theta16_floor_cell_230,
    theta16_floor_cell_231,
    theta16_floor_cell_232,
    theta16_floor_cell_233,
    theta16_floor_cell_234,
    theta16_floor_cell_235,
    theta16_floor_cell_236,
    theta16_floor_cell_237,
    theta16_floor_cell_238,
    theta16_floor_cell_239,
    theta16_floor_cell_240,
    theta16_floor_cell_241,
    theta16_floor_cell_242,
    theta16_floor_cell_243,
    theta16_floor_cell_244,
    theta16_floor_cell_245,
    theta16_floor_cell_246,
    theta16_floor_cell_247,
    theta16_floor_cell_248,
    theta16_floor_cell_249,
    theta16_floor_cell_250,
    theta16_floor_cell_251,
    theta16_floor_cell_252,
    theta16_floor_cell_253,
    theta16_floor_cell_254,
    theta16_floor_cell_255,
    theta16_floor_cell_256,
    theta16_floor_cell_257,
    theta16_floor_cell_258,
    theta16_floor_cell_259,
    theta16_floor_cell_260,
    theta16_floor_cell_261,
    theta16_floor_cell_262,
    theta16_floor_cell_263,
    theta16_floor_cell_264,
    theta16_floor_cell_265,
    theta16_floor_cell_266,
    theta16_floor_cell_267,
    theta16_floor_cell_268,
    theta16_floor_cell_269,
    theta16_floor_cell_270,
    theta16_floor_cell_271,
    theta16_floor_cell_272,
    theta16_floor_cell_273,
    theta16_floor_cell_274,
    theta16_floor_cell_275,
    theta16_floor_cell_276,
    theta16_floor_cell_277,
    theta16_floor_cell_278,
    theta16_floor_cell_279,
    theta16_floor_cell_280,
    theta16_floor_cell_281,
    theta16_floor_cell_282,
    theta16_floor_cell_283,
    theta16_floor_cell_284,
    theta16_floor_cell_285,
    theta16_floor_cell_286,
    theta16_floor_cell_287,
    theta16_floor_cell_288,
    theta16_floor_cell_289,
    theta16_floor_cell_290,
    theta16_floor_cell_291,
    theta16_floor_cell_292,
    theta16_floor_cell_293,
    theta16_floor_cell_294,
    theta16_floor_cell_295,
    theta16_floor_cell_296,
    theta16_floor_cell_297,
    theta16_floor_cell_298,
    theta16_floor_cell_299,
    theta16_floor_cell_300,
    theta16_floor_cell_301,
    theta16_floor_cell_302,
    theta16_floor_cell_303,
    theta16_floor_cell_304,
    theta16_floor_cell_305,
    theta16_floor_cell_306,
    theta16_floor_cell_307,
    theta16_floor_cell_308,
    theta16_floor_cell_309,
    theta16_floor_cell_310,
    theta16_floor_cell_311,
    theta16_floor_cell_312,
    theta16_floor_cell_313,
    theta16_floor_cell_314,
    theta16_floor_cell_315,
    theta16_floor_cell_316,
    theta16_floor_cell_317,
    theta16_floor_cell_318,
    theta16_floor_cell_319,
    theta16_floor_cell_320,
    theta16_floor_cell_321,
    theta16_floor_cell_322,
    theta16_floor_cell_323,
    theta16_floor_cell_324,
    theta16_floor_cell_325,
    theta16_floor_cell_326,
    theta16_floor_cell_327,
    theta16_floor_cell_328,
    theta16_floor_cell_329,
    theta16_floor_cell_330,
    theta16_floor_cell_331,
    theta16_floor_cell_332,
    theta16_floor_cell_333,
    theta16_floor_cell_334,
    theta16_floor_cell_335,
    theta16_floor_cell_336,
    theta16_floor_cell_337,
    theta16_floor_cell_338,
    theta16_floor_cell_339,
    theta16_floor_cell_340,
    theta16_floor_cell_341,
    theta16_floor_cell_342,
    theta16_floor_cell_343,
    theta16_floor_cell_344,
    theta16_floor_cell_345,
    theta16_floor_cell_346,
    theta16_floor_cell_347,
    theta16_floor_cell_348,
    theta16_floor_cell_349,
    theta16_floor_cell_350,
    theta16_floor_cell_351,
    theta16_floor_cell_352,
    theta16_floor_cell_353,
    theta16_floor_cell_354,
    theta16_floor_cell_355,
    theta16_floor_cell_356,
    theta16_floor_cell_357,
    theta16_floor_cell_358,
    theta16_floor_cell_359,
    theta16_floor_cell_360,
    theta16_floor_cell_361,
    theta16_floor_cell_362,
    theta16_floor_cell_363,
    theta16_floor_cell_364,
    theta16_floor_cell_365,
    theta16_floor_cell_366,
    theta16_floor_cell_367,
    theta16_floor_cell_368,
    theta16_floor_cell_369,
    theta16_floor_cell_370,
    theta16_floor_cell_371,
    theta16_floor_cell_372,
    theta16_floor_cell_373,
    theta16_floor_cell_374,
    theta16_floor_cell_375,
    theta16_floor_cell_376,
    theta16_floor_cell_377,
    theta16_floor_cell_378,
    theta16_floor_cell_379,
    theta16_floor_cell_380,
    theta16_floor_cell_381,
    theta16_floor_cell_382,
    theta16_floor_cell_383,
    theta16_floor_cell_384,
    theta16_floor_cell_385,
    theta16_floor_cell_386,
    theta16_floor_cell_387,
    theta16_floor_cell_388,
    theta16_floor_cell_389,
    theta16_floor_cell_390,
    theta16_floor_cell_391,
    theta16_floor_cell_392,
    theta16_floor_cell_393,
    theta16_floor_cell_394,
    theta16_floor_cell_395,
    theta16_floor_cell_396,
    theta16_floor_cell_397,
    theta16_floor_cell_398,
    theta16_floor_cell_399,
    theta16_floor_cell_400,
    theta16_floor_cell_401,
    theta16_floor_cell_402,
    theta16_floor_cell_403,
    theta16_floor_cell_404,
    theta16_floor_cell_405,
    theta16_floor_cell_406,
    theta16_floor_cell_407,
    theta16_floor_cell_408,
    theta16_floor_cell_409,
    theta16_floor_cell_410,
    theta16_floor_cell_411,
    theta16_floor_cell_412,
    theta16_floor_cell_413,
    theta16_floor_cell_414,
    theta16_floor_cell_415,
    theta16_floor_cell_416,
    theta16_floor_cell_417,
    theta16_floor_cell_418,
    theta16_floor_cell_419,
    theta16_floor_cell_420,
    theta16_floor_cell_421,
    theta16_floor_cell_422,
    theta16_floor_cell_423,
    theta16_floor_cell_424,
    theta16_floor_cell_425,
    theta16_floor_cell_426,
    theta16_floor_cell_427,
    theta16_floor_cell_428,
    theta16_floor_cell_429,
    theta16_floor_cell_430,
    theta16_floor_cell_431,
    theta16_floor_cell_432,
    theta16_floor_cell_433,
    theta16_floor_cell_434,
    theta16_floor_cell_435,
    theta16_floor_cell_436,
    theta16_floor_cell_437,
    theta16_floor_cell_438,
    theta16_floor_cell_439,
    theta16_floor_cell_440,
    theta16_floor_cell_441,
    theta16_floor_cell_442,
    theta16_floor_cell_443,
    theta16_floor_cell_444,
    theta16_floor_cell_445,
    theta16_floor_cell_446,
    theta16_floor_cell_447,
    theta16_floor_cell_448,
    theta16_floor_cell_449,
    theta16_floor_cell_450,
    theta16_floor_cell_451,
    theta16_floor_cell_452,
    theta16_floor_cell_453,
    theta16_floor_cell_454,
    theta16_floor_cell_455,
    theta16_floor_cell_456,
    theta16_floor_cell_457,
    theta16_floor_cell_458,
    theta16_floor_cell_459,
    theta16_floor_cell_460,
    theta16_floor_cell_461,
    theta16_floor_cell_462,
    theta16_floor_cell_463,
    theta16_floor_cell_464,
    theta16_floor_cell_465,
    theta16_floor_cell_466,
    theta16_floor_cell_467,
    theta16_floor_cell_468,
    theta16_floor_cell_469,
    theta16_floor_cell_470,
    theta16_floor_cell_471,
    theta16_floor_cell_472,
    theta16_floor_cell_473,
    theta16_floor_cell_474,
    theta16_floor_cell_475,
    theta16_floor_cell_476,
    theta16_floor_cell_477,
    theta16_floor_cell_478,
    theta16_floor_cell_479,
    theta16_floor_cell_480,
    theta16_floor_cell_481,
    theta16_floor_cell_482,
    theta16_floor_cell_483,
    theta16_floor_cell_484,
    theta16_floor_cell_485,
    theta16_floor_cell_486,
    theta16_floor_cell_487,
    theta16_floor_cell_488,
    theta16_floor_cell_489,
    theta16_floor_cell_490,
    theta16_floor_cell_491,
    theta16_floor_cell_492,
    theta16_floor_cell_493,
    theta16_floor_cell_494,
    theta16_floor_cell_495,
    theta16_floor_cell_496,
    theta16_floor_cell_497,
    theta16_floor_cell_498,
    theta16_floor_cell_499,
    theta16_floor_cell_500,
    theta16_floor_cell_501,
    theta16_floor_cell_502,
    theta16_floor_cell_503,
    theta16_floor_cell_504,
    theta16_floor_cell_505,
    theta16_floor_cell_506,
    theta16_floor_cell_507,
    theta16_floor_cell_508,
    theta16_floor_cell_509,
    theta16_floor_cell_510,
    theta16_floor_cell_511,
    theta16_floor_cell_512,
    theta16_floor_cell_513,
    theta16_floor_cell_514,
    theta16_floor_cell_515,
    theta16_floor_cell_516,
    theta16_floor_cell_517,
    theta16_floor_cell_518,
    theta16_floor_cell_519,
    theta16_floor_cell_520,
    theta16_floor_cell_521,
    theta16_floor_cell_522,
    theta16_floor_cell_523,
    theta16_floor_cell_524,
    theta16_floor_cell_525,
    theta16_floor_cell_526,
    theta16_floor_cell_527,
    theta16_floor_cell_528,
    theta16_floor_cell_529,
    theta16_floor_cell_530,
    theta16_floor_cell_531,
    theta16_floor_cell_532,
    theta16_floor_cell_533,
    theta16_floor_cell_534,
    theta16_floor_cell_535,
    theta16_floor_cell_536,
    theta16_floor_cell_537,
    theta16_floor_cell_538,
    theta16_floor_cell_539,
    theta16_floor_cell_540,
    theta16_floor_cell_541,
    theta16_floor_cell_542,
    theta16_floor_cell_543,
    theta16_floor_cell_544,
    theta16_floor_cell_545,
    theta16_floor_cell_546,
    theta16_floor_cell_547,
    theta16_floor_cell_548,
    theta16_floor_cell_549,
    theta16_floor_cell_550,
    theta16_floor_cell_551,
    theta16_floor_cell_552,
    theta16_floor_cell_553,
    theta16_floor_cell_554,
    theta16_floor_cell_555,
    theta16_floor_cell_556,
    theta16_floor_cell_557,
    theta16_floor_cell_558,
    theta16_floor_cell_559,
    theta16_floor_cell_560,
    theta16_floor_cell_561,
    theta16_floor_cell_562,
    theta16_floor_cell_563,
    theta16_floor_cell_564,
    theta16_floor_cell_565,
    theta16_floor_cell_566,
    theta16_floor_cell_567,
    theta16_floor_cell_568,
    theta16_floor_cell_569,
    theta16_floor_cell_570,
    theta16_floor_cell_571,
    theta16_floor_cell_572,
    theta16_floor_cell_573,
    theta16_floor_cell_574,
    theta16_floor_cell_575
  ]

theorem theta16_floor_sum_lower_exact :
    (7675744886 : ℝ) / 1000000000000000000 ≤
      Finset.sum (Finset.range 576) theta16FloorTerm := by
  have hsum :
      Finset.sum (Finset.range 576) (fun j => ((theta16FloorQ j : ℝ) / 1000000000000000000)) ≤
      Finset.sum (Finset.range 576) theta16FloorTerm := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact theta16_floor_cell_bound j (Finset.mem_range.mp hj)
  have hnum :
      (7675744886 : ℝ) / 1000000000000000000 ≤
      Finset.sum (Finset.range 576) (fun j => ((theta16FloorQ j : ℝ) / 1000000000000000000)) := by
    norm_num [theta16FloorQ]
  exact hnum.trans hsum

theorem theta16_floor_sum_lower_target :
    (7675700000 : ℝ) / 1000000000000000000 ≤
      Finset.sum (Finset.range 576) theta16FloorTerm := by
  exact (by
    norm_num :
      (7675700000 : ℝ) / 1000000000000000000 ≤
        (7675744886 : ℝ) / 1000000000000000000).trans
    theta16_floor_sum_lower_exact

end
end CarrySelfAdjointOperator

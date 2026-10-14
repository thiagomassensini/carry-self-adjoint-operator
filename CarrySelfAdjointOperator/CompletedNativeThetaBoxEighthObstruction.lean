import CarrySelfAdjointOperator.CompletedNativeThetaFourteenthSourceCertificate
import CarrySelfAdjointOperator.LogarithmicMomentHankel
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact obstruction to closing the eighth-source sign from the old theta box

The actual theta moments satisfy the old rational box. A DIFFERENT rational
point in that same box passes the division-free response recurrence through
order seven but has a negative odd quadratic direction. This refutes only
sufficiency of those rectangular bounds for this finite algebraic test.
It is not a negative direction of the native source or a theta-kernel model.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-- The unchanged eight interval constraints used for the seventh-source
certificate. The ninth coordinate is deliberately unrestricted by this box. -/
def nativeThetaFourteenthBox (a : ℕ → ℝ) : Prop :=
  ((143957803576790947/12500000000000000000:ℝ) ≤ a 0 ∧ a 0 ≤ (1151705926264716973/100000000000000000000:ℝ)) ∧
  ((12366004462665709/50000000000000000000:ℝ) ≤ a 1 ∧ a 1 ≤ (24732174504327621/100000000000000000000:ℝ)) ∧
  ((250006235248489/12500000000000000000:ℝ) ≤ a 2 ∧ a 2 ≤ (100002690918557/5000000000000000000:ℝ)) ∧
  ((35962943842419/12500000000000000000:ℝ) ≤ a 3 ∧ a 3 ≤ (143851913648521/50000000000000000000:ℝ)) ∧
  ((58974919255771/100000000000000000000:ℝ) ≤ a 4 ∧ a 4 ≤ (58974975697643/100000000000000000000:ℝ)) ∧
  ((7760401629807/50000000000000000000:ℝ) ≤ a 5 ∧ a 5 ≤ (7760416175641/50000000000000000000:ℝ)) ∧
  ((4940838545437/100000000000000000000:ℝ) ≤ a 6 ∧ a 6 ≤ (617607723967/12500000000000000000:ℝ)) ∧
  ((183134056399/10000000000000000000:ℝ) ≤ a 7 ∧ a 7 ≤ (73254480547/4000000000000000000:ℝ))

/-- These are actual source bounds, not assumptions about fitted moments. -/
theorem nativeThetaFourteenthBox_actual :
    nativeThetaFourteenthBox (fun n => completedNativeThetaTailMoment (2*n)) := by
  exact ⟨nativeSourceThetaIntegral_fourteenth_box_0,
    nativeSourceThetaIntegral_fourteenth_box_2,
    nativeSourceThetaIntegral_fourteenth_box_4,
    nativeSourceThetaIntegral_fourteenth_box_6,
    nativeSourceThetaIntegral_fourteenth_box_8,
    nativeSourceThetaIntegral_fourteenth_box_10,
    nativeSourceThetaIntegral_fourteenth_box_12,
    nativeSourceThetaIntegral_fourteenth_box_14⟩

/-- A rational countermodel for the bounding argument only; not the native source. -/
def thetaBoxEighthCandidate : ℕ → ℚ
  | 0 => (1151705926264716973/100000000000000000000:ℚ)
  | 1 => (12366004462665709/50000000000000000000:ℚ)
  | 2 => (100002690918557/5000000000000000000:ℚ)
  | 3 => (35962943842419/12500000000000000000:ℚ)
  | 4 => (58974919255771/100000000000000000000:ℚ)
  | 5 => (7760416175641/50000000000000000000:ℚ)
  | 6 => (4940838545437/100000000000000000000:ℚ)
  | 7 => (73254480547/4000000000000000000:ℚ)
  | 8 => (38493197358544125403/5000000000000000000000000000:ℚ)
  | _ => 0

/-- The theta-to-even-characteristic coefficient formula used in the source
calculation, interpreted here for a rational test array. -/
def thetaBoxEvenCoefficient (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1/2-a 0/4 else
    (-1:ℚ)^n * (a (n-1)/((2*n-2).factorial:ℚ) - a n/(4*((2*n).factorial:ℚ)))

/-- Exact evaluated coefficients; the next theorem checks their entire prefix. -/
def thetaBoxEighthCharacteristic : ℕ → ℚ
  | 0 => (198848294073735283027/400000000000000000000:ℚ)
  | 1 => (-4594457700596202183/400000000000000000000:ℚ)
  | 2 => (296284093649384231/2400000000000000000000:ℚ)
  | 3 => (-3329427147969409/4000000000000000000000:ℚ)
  | 4 => (64386620446359077/16128000000000000000000000:ℚ)
  | 5 => (-10607725049863139/725760000000000000000000000:ℚ)
  | 6 => (1170008377561637/27371520000000000000000000000:ℚ)
  | 7 => (-3595099099064461/34871316480000000000000000000000:ℚ)
  | 8 => (87866883459041455874597/418455797760000000000000000000000000000000:ℚ)
  | _ => 0

/-- Uniquely determined rational response prefix, checked division-free below. -/
def thetaBoxEighthLogMoment : ℕ → ℚ
  | 0 => (4594457700596202183/198848294073735283027:ℚ)
  | 1 => (4411538104340344277225892151986149230/118621932168104119441467311517215382848187:ℚ)
  | 2 => (5681607291574342786779123784227015740273822133636822249/39312948085596411844887934568310059808015831633678716364703415:ℚ)
  | 3 => (233772831330921945956374827974738430935181986663140106705477078020980921213/350215607249991339207436631148760592259046430673184846427268164962753984035641986784:ℚ)
  | 4 => (183732166369682351007085698977783861884464127690393937999239746323779597332529895492805040627267/56408218608323025552152145313005898735310426725475979821683907664066644456728449696337166918201895147286080:ℚ)
  | 5 => (80081710407380492421714606751292544212052227249044349023082160201857036942552882561521138879593262140298462620410683/4935338338481480070282877327178492557992101239342269063484049597865879761381170904482947296660816546436576487206592262284440230400:ℚ)
  | 6 => (831603792342431761051220827525472775232969301567323533468598826183022316675765589798971078792465726332056626093060918374322328149840613/10206389536550952490643935567929265259326469380304269483191654608860948135248598613694893984277678876771066479041281265978919279453278897894814529976320:ℚ)
  | 7 => (10085229525713478319397603064804140191908799194696003912146125943175242075840078298374585479253858849054833108634445391091995238716968187146517018449565147291803293/24588453523787740343088958408319451940114615415836197770056409352868789804323794973661429604122058293099603787977425656911731406949946379391439350725685423695773777095961600000000000:ℚ)
  | _ => 0

/-- The rational characteristic is computed from the candidate, not fitted. -/
theorem thetaBoxEighthCharacteristic_from_theta :
    ∀ n : ℕ, n ≤ 8 → thetaBoxEighthCharacteristic n =
      thetaBoxEvenCoefficient thetaBoxEighthCandidate n := by
  intro n hn
  interval_cases n <;> norm_num [thetaBoxEighthCharacteristic,
    thetaBoxEvenCoefficient, thetaBoxEighthCandidate, Nat.factorial]

/-- The same source recurrence is checked in every order needed by the test. -/
theorem thetaBoxEighthLogMoment_recurrence :
    ∀ n : ℕ, n < 8 →
      thetaBoxEighthCharacteristic 0 * thetaBoxEighthLogMoment n +
        ∑ k ∈ Finset.range n, thetaBoxEighthLogMoment k *
          thetaBoxEighthCharacteristic (n-k) =
        -((n+1:ℕ):ℚ) * thetaBoxEighthCharacteristic (n+1) := by
  intro n hn
  interval_cases n <;> norm_num [thetaBoxEighthCharacteristic,
    thetaBoxEighthLogMoment, Finset.sum_range_succ]

/-- The countermodel lies within every currently certified interval. -/
theorem thetaBoxEighthCandidate_inside :
    nativeThetaFourteenthBox (fun n => (thetaBoxEighthCandidate n:ℝ)) := by
  norm_num [nativeThetaFourteenthBox, thetaBoxEighthCandidate]

/-- No negative raw theta moment is used to manufacture the obstruction. -/
theorem thetaBoxEighthCandidate_nonneg (n : ℕ) : 0 ≤ thetaBoxEighthCandidate n := by
  unfold thetaBoxEighthCandidate
  split <;> norm_num

/-- The source center divisor also has the correct positive sign. -/
theorem thetaBoxEighthCharacteristic_zero_pos : 0 < thetaBoxEighthCharacteristic 0 := by
  norm_num [thetaBoxEighthCharacteristic]

/-- All nine corresponding raw cosine moments have the positive sign. -/
theorem thetaBoxEighth_raw_cosine_prefix_pos :
    ∀ n : ℕ, n ≤ 8 → 0 < (-1:ℚ)^n * ((2*n).factorial:ℚ) *
      thetaBoxEighthCharacteristic n := by
  intro n hn
  interval_cases n <;> norm_num [thetaBoxEighthCharacteristic, Nat.factorial]

/-- A fixed rational test vector in the odd four-coordinate response block. -/
def thetaBoxEighthOddWitness : Fin 4 → ℚ :=
  ![(-15674039/5000000000000000:ℚ), (29723112307/2500000000000000:ℚ), (-582326565457/80000000000000:ℚ), (1/1:ℚ)]

/-- Exact negative quadratic value, verified by rational arithmetic in Lean.
This is a countermodel of interval sufficiency, NOT of native positivity. -/
theorem thetaBoxEighthOddWitness_negative :
    (∑ i : Fin 4, ∑ j : Fin 4,
      thetaBoxEighthLogMoment (i.val+j.val+1) *
        thetaBoxEighthOddWitness i * thetaBoxEighthOddWitness j) < 0 := by
  norm_num [Fin.sum_univ_succ, thetaBoxEighthOddWitness, thetaBoxEighthLogMoment]

private def thetaBoxRawTheta0Upper : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1/1:ℝ), (24732008925331418/1151705926264716973:ℝ), (2000053818371140/1151705926264716973:ℝ), (287703550739352/1151705926264716973:ℝ), (58974919255771/1151705926264716973:ℝ);
    (0/1:ℝ), (1/1:ℝ), (17617783469175948474638984184061/105737598123984054782438677091781:ℝ), (60806277223119438359157577340047/1691801569983744876519018833468496:ℝ), (1368072197510682731338146633009/140983464165312073043251569455708:ℝ);
    (0/1:ℝ), (0/1:ℝ), (1/1:ℝ), (658145343303693296065608497124878406931295003/1556586868643810442753179954779262896541454119:ℝ), (260472417240702267650353246603253664069482361/1556586868643810442753179954779262896541454119:ℝ);
    (0/1:ℝ), (0/1:ℝ), (0/1:ℝ), (1/1:ℝ), (6543908986412675338264707857058621477071633546057246793908/8458778937575381939142108051025664161056219624604313020665:ℝ);
    (0/1:ℝ), (0/1:ℝ), (0/1:ℝ), (0/1:ℝ), (1/1:ℝ)]

private def thetaBoxRawTheta0Diagonal : Fin 5 → ℝ :=
  ![(1151705926264716973/100000000000000000000:ℝ), (105737598123984054782438677091781/7198162039154481081250000000000000000:ℝ), (1556586868643810442753179954779262896541454119/10573759812398405478243867709178100000000000000000000:ℝ), (1691755787515076387828421610205132832211243924920862604133/498107797966019341681017585529364126893265318080000000000000000000:ℝ), (1103064397127872809551551790374318510350889819944839970144743015819738090599/8458778937575381939142108051025664161056219624604313020665000000000000000000000000000:ℝ)]

/-- Exact positive raw-theta Hankel certificate for the countermodel.
This does not assert positivity of its logarithmic response form. -/
theorem thetaBoxRawTheta0_posDef :
    Matrix.PosDef (fun i j : Fin 5 => (thetaBoxEighthCandidate (i.val+j.val+0):ℝ)) := by
  classical
  have hf : (fun i j : Fin 5 => (thetaBoxEighthCandidate (i.val+j.val+0):ℝ)) =
      (thetaBoxRawTheta0Upper).conjTranspose * Matrix.diagonal thetaBoxRawTheta0Diagonal * thetaBoxRawTheta0Upper := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaBoxRawTheta0Upper, thetaBoxRawTheta0Diagonal, thetaBoxEighthCandidate,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
        Fin.sum_univ_succ]
  have hd : (Matrix.diagonal thetaBoxRawTheta0Diagonal).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [thetaBoxRawTheta0Diagonal]
  have hu : IsUnit thetaBoxRawTheta0Upper := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    have ht : (thetaBoxRawTheta0Upper).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [thetaBoxRawTheta0Upper]
    have hdU : (thetaBoxRawTheta0Upper).det = 1 := by
      rw [Matrix.det_of_upperTriangular ht]
      apply Finset.prod_eq_one
      intro i _
      fin_cases i <;> norm_num [thetaBoxRawTheta0Upper]
    rw [hdU]
    exact isUnit_one
  rw [hf]
  exact hd.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hu)

private def thetaBoxRawTheta1Upper : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1/1:ℝ), (1000026909185570/12366004462665709:ℝ), (143851775369676/12366004462665709:ℝ), (58974919255771/24732008925331418:ℝ);
    (0/1:ℝ), (1/1:ℝ), (441572822094626046639372505999/1557635754177108537966374830768:ℝ), (33238543974355572973972791117/389408938544277134491593707692:ℝ);
    (0/1:ℝ), (0/1:ℝ), (1/1:ℝ), (1879808405565469298413679312207762924668276/3194741206022279769874275082718463204326683:ℝ);
    (0/1:ℝ), (0/1:ℝ), (0/1:ℝ), (1/1:ℝ)]

private def thetaBoxRawTheta1Diagonal : Fin 4 → ℝ :=
  ![(12366004462665709/50000000000000000000:ℝ), (97352234636069283622898426923/77287527891660681250000000000000000:ℝ), (3194741206022279769874275082718463204326683/155763575417710853796637483076800000000000000000000:ℝ), (401938051170133635864362297034916015049030214617675987/638948241204455953974855016543692640865336600000000000000000000:ℝ)]

/-- Exact positive raw-theta shifted Hankel certificate for the countermodel.
This does not assert positivity of its logarithmic response form. -/
theorem thetaBoxRawTheta1_posDef :
    Matrix.PosDef (fun i j : Fin 4 => (thetaBoxEighthCandidate (i.val+j.val+1):ℝ)) := by
  classical
  have hf : (fun i j : Fin 4 => (thetaBoxEighthCandidate (i.val+j.val+1):ℝ)) =
      (thetaBoxRawTheta1Upper).conjTranspose * Matrix.diagonal thetaBoxRawTheta1Diagonal * thetaBoxRawTheta1Upper := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaBoxRawTheta1Upper, thetaBoxRawTheta1Diagonal, thetaBoxEighthCandidate,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
        Fin.sum_univ_succ]
  have hd : (Matrix.diagonal thetaBoxRawTheta1Diagonal).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num [thetaBoxRawTheta1Diagonal]
  have hu : IsUnit thetaBoxRawTheta1Upper := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    have ht : (thetaBoxRawTheta1Upper).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [thetaBoxRawTheta1Upper]
    have hdU : (thetaBoxRawTheta1Upper).det = 1 := by
      rw [Matrix.det_of_upperTriangular ht]
      apply Finset.prod_eq_one
      intro i _
      fin_cases i <;> norm_num [thetaBoxRawTheta1Upper]
    rw [hdU]
    exact isUnit_one
  rw [hf]
  exact hd.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hu)


/-- The old box, nonnegative theta values, positive raw cosine prefix, and
positive raw moment Grams STILL do not imply the required logarithmic sign.
Only this finite algebraic implication is refuted, not the actual source. -/
theorem thetaFourteenthBox_and_raw_positivity_insufficient :
    ¬ (∀ a phi h : ℕ → ℚ,
      nativeThetaFourteenthBox (fun n => (a n : ℝ)) →
      (∀ n, 0 ≤ a n) →
      (∀ n, n ≤ 8 → phi n = thetaBoxEvenCoefficient a n) →
      0 < phi 0 →
      (∀ n, n ≤ 8 → 0 < (-1:ℚ)^n * ((2*n).factorial:ℚ) * phi n) →
      (∀ n, n < 8 → phi 0 * h n +
        ∑ k ∈ Finset.range n, h k * phi (n-k) = -((n+1:ℕ):ℚ)*phi (n+1)) →
      Matrix.PosDef (fun i j : Fin 5 => (a (i.val+j.val):ℝ)) →
      Matrix.PosDef (fun i j : Fin 4 => (a (i.val+j.val+1):ℝ)) →
      ∀ x : Fin 4 → ℚ, 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4,
        h (i.val+j.val+1)*x i*x j) := by
  intro hall
  have h := hall thetaBoxEighthCandidate thetaBoxEighthCharacteristic thetaBoxEighthLogMoment
    thetaBoxEighthCandidate_inside thetaBoxEighthCandidate_nonneg
    thetaBoxEighthCharacteristic_from_theta thetaBoxEighthCharacteristic_zero_pos
    thetaBoxEighth_raw_cosine_prefix_pos thetaBoxEighthLogMoment_recurrence
    (by simpa only [Nat.add_zero] using thetaBoxRawTheta0_posDef)
    thetaBoxRawTheta1_posDef thetaBoxEighthOddWitness
  exact (not_le_of_gt thetaBoxEighthOddWitness_negative) h

end
end CarrySelfAdjointOperator

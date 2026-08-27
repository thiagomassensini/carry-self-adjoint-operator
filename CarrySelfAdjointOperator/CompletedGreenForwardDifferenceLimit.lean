import CarrySelfAdjointOperator.CompletedGreenRealKernelClosure
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import CarrySelfAdjointOperator.GreenKernelCoefficientClosure
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Tactic

/-!
# Scalar forward-difference limit for the completed Green kernel

The normalized completed Green Gram is already identified with the total
divided difference `dslope response`.  This file extracts the resulting
two-variable Taylor coefficients without differentiating the Hilbert-valued
state.  Every sampled kernel entry lies on a one-variable analytic ray; the
finite forward-difference sums can therefore be handled entirely on the
scalar side.
-/

namespace CarrySelfAdjointOperator

open Filter

noncomputable section

/-- The coefficient of a scalar power-series germ is its factorial-normalized
iterated derivative. -/
theorem hasFPowerSeriesAt_coeff_eq_iteratedDeriv_div_factorial
    {f : ℂ → ℂ} {series : FormalMultilinearSeries ℂ ℂ ℂ} {x : ℂ}
    (hseries : HasFPowerSeriesAt f series x) (n : ℕ) :
    series.coeff n = iteratedDeriv n f x / (n.factorial : ℂ) := by
  rcases hseries with ⟨radius, hball⟩
  have hderiv := hball.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hderiv
  simp only [Finset.prod_const_one, one_smul, nsmul_eq_mul] at hderiv
  change (n.factorial : ℂ) * series.coeff n = iteratedDeriv n f x at hderiv
  rw [← hderiv]
  field_simp [show (n.factorial : ℂ) ≠ 0 by
    exact_mod_cast n.factorial_ne_zero]

/-- Passing to the canonical divided difference shifts scalar Taylor
coefficients by one. -/
theorem iteratedDeriv_dslope_div_factorial_eq_succ
    {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (n : ℕ) :
    iteratedDeriv n (dslope f x) x / (n.factorial : ℂ) =
      iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℂ) := by
  rcases hf with ⟨series, hseries⟩
  calc
    iteratedDeriv n (dslope f x) x / (n.factorial : ℂ) =
        series.fslope.coeff n :=
      (hasFPowerSeriesAt_coeff_eq_iteratedDeriv_div_factorial
        hseries.has_fpower_series_dslope_fslope n).symm
    _ = series.coeff (n + 1) := FormalMultilinearSeries.coeff_fslope
    _ = iteratedDeriv (n + 1) f x / ((n + 1).factorial : ℂ) :=
      hasFPowerSeriesAt_coeff_eq_iteratedDeriv_div_factorial hseries (n + 1)

/-- Iterated scalar differentiation commutes with dilation.  This statement
is unconditional because Mathlib's scalar derivative and its zero fallback
both obey the dilation rule. -/
theorem iteratedDeriv_comp_mul_zero
    (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => f (c * z)) 0 =
      c ^ n * iteratedDeriv n f 0 := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ']
      have hderiv : deriv (fun z => f (c * z)) =
          fun z => c * deriv f (c * z) := by
        funext z
        simpa only [smul_eq_mul] using deriv_comp_mul_left c f z
      rw [hderiv, iteratedDeriv_const_mul_field,
        ih (deriv f), ← iteratedDeriv_succ']
      simp [pow_succ, Nat.succ_eq_add_one, mul_assoc, mul_comm]

/-- Homogeneous coefficient of the divided difference of the monomial
`z^(n+1)` at the coordinate pair `(i,j)`. -/
def completedGreenHomogeneousDividedPower (i j n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (n + 1),
    (i : ℂ) ^ r * (j : ℂ) ^ (n - r)

/-- On the coordinate diagonal the homogeneous divided power is the
derivative coefficient `(n+1) i^n`. -/
theorem completedGreenHomogeneousDividedPower_self
    (i n : ℕ) :
    completedGreenHomogeneousDividedPower i i n =
      ((n + 1 : ℕ) : ℂ) * (i : ℂ) ^ n := by
  simpa [completedGreenHomogeneousDividedPower] using
    (geom_sum₂_self (i : ℂ) (n + 1))

/-- Off the coordinate diagonal, multiplying the homogeneous divided power
by the coordinate difference recovers the difference of powers. -/
theorem sub_mul_completedGreenHomogeneousDividedPower
    (i j n : ℕ) :
    ((j : ℂ) - (i : ℂ)) * completedGreenHomogeneousDividedPower i j n =
      (j : ℂ) ^ (n + 1) - (i : ℂ) ^ (n + 1) := by
  simpa [completedGreenHomogeneousDividedPower] using
    (Commute.mul_neg_geom_sum₂ (Commute.all (i : ℂ) (j : ℂ)) (n + 1))

/-- Restriction of a total divided-difference kernel to the ray through the
pair of natural coordinates `(i,j)`. -/
def completedGreenDslopeRay
    (response : ℂ → ℂ) (i j : ℕ) (h : ℂ) : ℂ :=
  dslope response ((i : ℂ) * h) ((j : ℂ) * h)

/-- Off the coordinate diagonal, a moving two-point divided difference is a
fixed-center divided difference of the difference of the two dilated
responses.  The formula also holds at `h = 0`, where both sides use the
canonical derivative value. -/
theorem completedGreenDslopeRay_eq_fixedCenter_of_ne
    {response : ℂ → ℂ}
    (hresponse : DifferentiableAt ℂ response 0)
    {i j : ℕ} (hij : i ≠ j) :
    completedGreenDslopeRay response i j =
      fun h => (((j : ℂ) - (i : ℂ))⁻¹) *
        dslope (fun u => response ((j : ℂ) * u) -
          response ((i : ℂ) * u)) 0 h := by
  funext h
  by_cases hh : h = 0
  · subst h
    simp only [completedGreenDslopeRay, mul_zero, dslope_same]
    have hjdiff : DifferentiableAt ℂ
        (fun u : ℂ => response ((j : ℂ) * u)) 0 := by
      have hinner : HasDerivAt (fun u : ℂ => (j : ℂ) * u) (j : ℂ) 0 :=
        hasDerivAt_const_mul (j : ℂ)
      have houter : HasDerivAt response (deriv response 0)
          ((j : ℂ) * (0 : ℂ)) := by
        simpa using hresponse.hasDerivAt
      simpa [Function.comp_def] using
        (houter.comp 0 hinner).differentiableAt
    have hidiff : DifferentiableAt ℂ
        (fun u : ℂ => response ((i : ℂ) * u)) 0 := by
      have hinner : HasDerivAt (fun u : ℂ => (i : ℂ) * u) (i : ℂ) 0 :=
        hasDerivAt_const_mul (i : ℂ)
      have houter : HasDerivAt response (deriv response 0)
          ((i : ℂ) * (0 : ℂ)) := by
        simpa using hresponse.hasDerivAt
      simpa [Function.comp_def] using
        (houter.comp 0 hinner).differentiableAt
    have hderiv :
        deriv (fun u : ℂ => response ((j : ℂ) * u) -
            response ((i : ℂ) * u)) 0 =
          (j : ℂ) * deriv response 0 -
            (i : ℂ) * deriv response 0 := by
      rw [show (fun u : ℂ => response ((j : ℂ) * u) -
          response ((i : ℂ) * u)) =
          (fun u : ℂ => response ((j : ℂ) * u)) -
            (fun u : ℂ => response ((i : ℂ) * u)) by rfl,
        deriv_sub hjdiff hidiff,
        deriv_comp_mul_left, deriv_comp_mul_left]
      simp only [smul_eq_mul, mul_zero]
    rw [hderiv]
    have hcast : (j : ℂ) - (i : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hij.symm)
    field_simp [hcast]
  · have hpoints : (j : ℂ) * h ≠ (i : ℂ) * h := by
      intro heq
      have : (j : ℂ) = (i : ℂ) := by
        exact mul_right_cancel₀ hh heq
      exact hij (Nat.cast_injective this.symm)
    rw [completedGreenDslopeRay, dslope_of_ne _ hpoints,
      dslope_of_ne _ hh]
    rw [slope_def_module, slope_def_module]
    simp only [smul_eq_mul, sub_zero, mul_zero, sub_self]
    have hcast : (j : ℂ) - (i : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hij.symm)
    change (((j : ℂ) * h - (i : ℂ) * h)⁻¹) *
        (response ((j : ℂ) * h) - response ((i : ℂ) * h)) =
      ((j : ℂ) - (i : ℂ))⁻¹ *
        (h⁻¹ * (response ((j : ℂ) * h) - response ((i : ℂ) * h)))
    rw [show (j : ℂ) * h - (i : ℂ) * h =
        ((j : ℂ) - (i : ℂ)) * h by ring]
    field_simp [hcast, hh]

/-- Every natural-coordinate ray of an analytic total divided difference is
analytic at the centered origin, including the collision rays `i = j`. -/
theorem completedGreenDslopeRay_analyticAt
    {response : ℂ → ℂ}
    (hresponse : AnalyticAt ℂ response 0)
    (i j : ℕ) :
    AnalyticAt ℂ (completedGreenDslopeRay response i j) 0 := by
  by_cases hij : i = j
  · subst j
    have heq : completedGreenDslopeRay response i i =
        fun h => deriv response ((i : ℂ) * h) := by
      funext h
      simp [completedGreenDslopeRay, dslope_same]
    rw [heq]
    have hinner : AnalyticAt ℂ (fun h : ℂ => (i : ℂ) * h) 0 :=
      analyticAt_const.mul analyticAt_id
    have houter : AnalyticAt ℂ (deriv response) ((i : ℂ) * (0 : ℂ)) := by
      simpa using hresponse.deriv
    simpa [Function.comp_def] using houter.comp hinner
  · rw [completedGreenDslopeRay_eq_fixedCenter_of_ne
      hresponse.differentiableAt hij]
    have hjinner : AnalyticAt ℂ (fun u : ℂ => (j : ℂ) * u) 0 :=
      analyticAt_const.mul analyticAt_id
    have hiinner : AnalyticAt ℂ (fun u : ℂ => (i : ℂ) * u) 0 :=
      analyticAt_const.mul analyticAt_id
    have hjouter : AnalyticAt ℂ response ((j : ℂ) * (0 : ℂ)) := by
      simpa using hresponse
    have hiouter : AnalyticAt ℂ response ((i : ℂ) * (0 : ℂ)) := by
      simpa using hresponse
    have hj : AnalyticAt ℂ (fun u => response ((j : ℂ) * u)) 0 := by
      simpa [Function.comp_def] using hjouter.comp hjinner
    have hi : AnalyticAt ℂ (fun u => response ((i : ℂ) * u)) 0 := by
      simpa [Function.comp_def] using hiouter.comp hiinner
    rcases (hj.sub hi) with ⟨series, hseries⟩
    exact (hseries.has_fpower_series_dslope_fslope.const_smul
      (c := ((j : ℂ) - (i : ℂ))⁻¹)).analyticAt

/-- The order-`n` Taylor coefficient of every sampled divided-difference ray
is the order-`n+1` response coefficient times the homogeneous divided power.
This is one formula for both collision and noncollision rays. -/
theorem completedGreenDslopeRay_taylorCoefficient
    {response : ℂ → ℂ}
    (hresponse : AnalyticAt ℂ response 0)
    (i j n : ℕ) :
    iteratedDeriv n (completedGreenDslopeRay response i j) 0 /
        (n.factorial : ℂ) =
      (iteratedDeriv (n + 1) response 0 / ((n + 1).factorial : ℂ)) *
        completedGreenHomogeneousDividedPower i j n := by
  by_cases hij : i = j
  · subst j
    have heq : completedGreenDslopeRay response i i =
        fun h => deriv response ((i : ℂ) * h) := by
      funext h
      simp [completedGreenDslopeRay, dslope_same]
    rw [heq, iteratedDeriv_comp_mul_zero,
      ← iteratedDeriv_succ',
      completedGreenHomogeneousDividedPower_self]
    have hnfac : ((n + 1).factorial : ℂ) =
        ((n + 1 : ℕ) : ℂ) * (n.factorial : ℂ) := by
      norm_cast
    rw [hnfac]
    field_simp [show (n.factorial : ℂ) ≠ 0 by
      exact_mod_cast n.factorial_ne_zero,
      show (((n + 1 : ℕ) : ℂ)) ≠ 0 by exact_mod_cast Nat.succ_ne_zero n]
  · rw [completedGreenDslopeRay_eq_fixedCenter_of_ne
      hresponse.differentiableAt hij,
      iteratedDeriv_const_mul_field]
    let g : ℂ → ℂ := fun u =>
      response ((j : ℂ) * u) - response ((i : ℂ) * u)
    have hjinner : AnalyticAt ℂ (fun u : ℂ => (j : ℂ) * u) 0 :=
      analyticAt_const.mul analyticAt_id
    have hiinner : AnalyticAt ℂ (fun u : ℂ => (i : ℂ) * u) 0 :=
      analyticAt_const.mul analyticAt_id
    have hjouter : AnalyticAt ℂ response ((j : ℂ) * (0 : ℂ)) := by
      simpa using hresponse
    have hiouter : AnalyticAt ℂ response ((i : ℂ) * (0 : ℂ)) := by
      simpa using hresponse
    have hj : AnalyticAt ℂ (fun u => response ((j : ℂ) * u)) 0 := by
      simpa [Function.comp_def] using hjouter.comp hjinner
    have hi : AnalyticAt ℂ (fun u => response ((i : ℂ) * u)) 0 := by
      simpa [Function.comp_def] using hiouter.comp hiinner
    have hg : AnalyticAt ℂ g 0 := hj.sub hi
    have hshift := iteratedDeriv_dslope_div_factorial_eq_succ hg n
    have hgsucc : iteratedDeriv (n + 1) g 0 =
        ((j : ℂ) ^ (n + 1) - (i : ℂ) ^ (n + 1)) *
          iteratedDeriv (n + 1) response 0 := by
      change iteratedDeriv (n + 1)
          ((fun u : ℂ => response ((j : ℂ) * u)) -
            (fun u : ℂ => response ((i : ℂ) * u))) 0 = _
      rw [iteratedDeriv_sub hj.contDiffAt hi.contDiffAt,
        iteratedDeriv_comp_mul_zero,
        iteratedDeriv_comp_mul_zero]
      ring
    have hcast : (j : ℂ) - (i : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hij)
    calc
      ((j : ℂ) - (i : ℂ))⁻¹ *
            iteratedDeriv n (dslope g 0) 0 /
          (n.factorial : ℂ) =
        ((j : ℂ) - (i : ℂ))⁻¹ *
          (iteratedDeriv (n + 1) g 0 / ((n + 1).factorial : ℂ)) := by
            rw [mul_div_assoc, hshift]
      _ = (iteratedDeriv (n + 1) response 0 /
              ((n + 1).factorial : ℂ)) *
            completedGreenHomogeneousDividedPower i j n := by
        rw [hgsucc, ← sub_mul_completedGreenHomogeneousDividedPower]
        field_simp [hcast]

/-! ## Finite-difference cancellation on the analytic rays -/

/-- Complex form of the signed binomial weight in an iterated forward
difference. -/
def completedGreenForwardWeight (order index : ℕ) : ℂ :=
  (((-1 : ℤ) ^ (order - index) * order.choose index : ℤ) : ℂ)

/-- Moment of the signed binomial weights. -/
def completedGreenForwardWeightPower (order degree : ℕ) : ℂ :=
  ∑ index ∈ Finset.range (order + 1),
    completedGreenForwardWeight order index * (index : ℂ) ^ degree

/-- An order-`order` forward difference kills every lower monomial. -/
theorem completedGreenForwardWeightPower_eq_zero_of_lt
    {degree order : ℕ} (hdegree : degree < order) :
    completedGreenForwardWeightPower order degree = 0 := by
  have hpoly := congrFun
    (fwdDiff_iter_pow_eq_zero_of_lt (R := ℂ) hdegree) 0
  rw [fwdDiff_iter_eq_sum_shift] at hpoly
  simpa [completedGreenForwardWeightPower, completedGreenForwardWeight,
    smul_eq_mul] using hpoly

/-- At the matching degree, the signed binomial moment is the factorial. -/
theorem completedGreenForwardWeightPower_self (order : ℕ) :
    completedGreenForwardWeightPower order order = (order.factorial : ℂ) := by
  have hpoly := congrFun
    (fwdDiff_iter_eq_factorial (R := ℂ) (n := order)) 0
  rw [fwdDiff_iter_eq_sum_shift] at hpoly
  simpa [completedGreenForwardWeightPower, completedGreenForwardWeight,
    smul_eq_mul] using hpoly

/-- Explicit double ray sum underlying the mixed forward difference of a
total divided-difference kernel. -/
def completedGreenDslopeMixedRaySum
    (response : ℂ → ℂ) (p q : ℕ) (h : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (q + 1),
      completedGreenForwardWeight p i *
        completedGreenForwardWeight q j *
          completedGreenDslopeRay response i j h

/-- The finite mixed ray sum remains analytic at the center. -/
theorem completedGreenDslopeMixedRaySum_analyticAt
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    AnalyticAt ℂ (completedGreenDslopeMixedRaySum response p q) 0 := by
  unfold completedGreenDslopeMixedRaySum
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact (analyticAt_const.mul analyticAt_const).mul
    (completedGreenDslopeRay_analyticAt hresponse i j)

/-- Signed binomial contraction of one homogeneous divided-power
coefficient. -/
def completedGreenMixedHomogeneousWeight (p q degree : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1),
    ∑ j ∈ Finset.range (q + 1),
      completedGreenForwardWeight p i *
        completedGreenForwardWeight q j *
          completedGreenHomogeneousDividedPower i j degree

/-- Expanding the homogeneous divided power factors the two camera
coordinates into independent signed-binomial moments. -/
theorem completedGreenMixedHomogeneousWeight_eq_sum_product
    (p q degree : ℕ) :
    completedGreenMixedHomogeneousWeight p q degree =
      ∑ r ∈ Finset.range (degree + 1),
        completedGreenForwardWeightPower p r *
          completedGreenForwardWeightPower q (degree - r) := by
  classical
  unfold completedGreenMixedHomogeneousWeight
    completedGreenHomogeneousDividedPower
    completedGreenForwardWeightPower
  symm
  calc
    (∑ r ∈ Finset.range (degree + 1),
        (∑ i ∈ Finset.range (p + 1),
            completedGreenForwardWeight p i * (i : ℂ) ^ r) *
          ∑ j ∈ Finset.range (q + 1),
            completedGreenForwardWeight q j * (j : ℂ) ^ (degree - r)) =
      ∑ r ∈ Finset.range (degree + 1),
        ∑ i ∈ Finset.range (p + 1),
          ∑ j ∈ Finset.range (q + 1),
            (completedGreenForwardWeight p i * (i : ℂ) ^ r) *
              (completedGreenForwardWeight q j *
                (j : ℂ) ^ (degree - r)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_mul_sum _ _ _ _
    _ = ∑ i ∈ Finset.range (p + 1),
        ∑ r ∈ Finset.range (degree + 1),
          ∑ j ∈ Finset.range (q + 1),
            (completedGreenForwardWeight p i * (i : ℂ) ^ r) *
              (completedGreenForwardWeight q j *
                (j : ℂ) ^ (degree - r)) := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (q + 1),
          ∑ r ∈ Finset.range (degree + 1),
            (completedGreenForwardWeight p i * (i : ℂ) ^ r) *
              (completedGreenForwardWeight q j *
                (j : ℂ) ^ (degree - r)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (q + 1),
          completedGreenForwardWeight p i *
            completedGreenForwardWeight q j *
              ∑ r ∈ Finset.range (degree + 1),
                (i : ℂ) ^ r * (j : ℂ) ^ (degree - r) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- The mixed order `(p,q)` contraction kills every homogeneous degree below
`p+q`. -/
theorem completedGreenMixedHomogeneousWeight_eq_zero_of_lt
    {p q degree : ℕ} (hdegree : degree < p + q) :
    completedGreenMixedHomogeneousWeight p q degree = 0 := by
  rw [completedGreenMixedHomogeneousWeight_eq_sum_product]
  apply Finset.sum_eq_zero
  intro r hr
  have hrle : r ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  by_cases hrp : r < p
  · rw [completedGreenForwardWeightPower_eq_zero_of_lt hrp, zero_mul]
  · have hq : degree - r < q := by omega
    rw [completedGreenForwardWeightPower_eq_zero_of_lt hq, mul_zero]

/-- At degree `p+q`, exactly one homogeneous monomial survives and contributes
`p! q!`. -/
theorem completedGreenMixedHomogeneousWeight_add
    (p q : ℕ) :
    completedGreenMixedHomogeneousWeight p q (p + q) =
      (p.factorial : ℂ) * (q.factorial : ℂ) := by
  rw [completedGreenMixedHomogeneousWeight_eq_sum_product]
  calc
    (∑ r ∈ Finset.range (p + q + 1),
        completedGreenForwardWeightPower p r *
          completedGreenForwardWeightPower q (p + q - r)) =
      completedGreenForwardWeightPower p p *
        completedGreenForwardWeightPower q (p + q - p) := by
      apply Finset.sum_eq_single p
      · intro r hr hrne
        have hrle : r ≤ p + q := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
        by_cases hrp : r < p
        · rw [completedGreenForwardWeightPower_eq_zero_of_lt hrp, zero_mul]
        · have hpr : p < r :=
            lt_of_le_of_ne (Nat.le_of_not_gt hrp) (Ne.symm hrne)
          have hq : p + q - r < q := by omega
          rw [completedGreenForwardWeightPower_eq_zero_of_lt hq, mul_zero]
      · intro hp
        exact (hp (Finset.mem_range.mpr (by omega))).elim
    _ = (p.factorial : ℂ) * (q.factorial : ℂ) := by
      rw [completedGreenForwardWeightPower_self]
      have hpq : p + q - p = q := by omega
      rw [hpq, completedGreenForwardWeightPower_self]

/-- Iterated differentiation of the finite ray sum is termwise. -/
theorem iteratedDeriv_completedGreenDslopeMixedRaySum
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q n : ℕ) :
    iteratedDeriv n (completedGreenDslopeMixedRaySum response p q) 0 =
      ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (q + 1),
          completedGreenForwardWeight p i *
            completedGreenForwardWeight q j *
              iteratedDeriv n (completedGreenDslopeRay response i j) 0 := by
  unfold completedGreenDslopeMixedRaySum
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_fun_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDeriv_const_mul_field]
    · intro j hj
      exact ((analyticAt_const.mul analyticAt_const).mul
        (completedGreenDslopeRay_analyticAt hresponse i j)).contDiffAt
  · intro i hi
    apply (Finset.analyticAt_fun_sum _ fun j hj => ?_).contDiffAt
    exact (analyticAt_const.mul analyticAt_const).mul
      (completedGreenDslopeRay_analyticAt hresponse i j)

/-- The Taylor coefficient of the finite mixed ray sum factors into the
response coefficient and the signed homogeneous contraction. -/
theorem completedGreenDslopeMixedRaySum_taylorCoefficient
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q degree : ℕ) :
    iteratedDeriv degree
          (completedGreenDslopeMixedRaySum response p q) 0 /
        (degree.factorial : ℂ) =
      (iteratedDeriv (degree + 1) response 0 /
          ((degree + 1).factorial : ℂ)) *
        completedGreenMixedHomogeneousWeight p q degree := by
  rw [iteratedDeriv_completedGreenDslopeMixedRaySum hresponse]
  unfold completedGreenMixedHomogeneousWeight
  calc
    (∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (q + 1),
          completedGreenForwardWeight p i *
            completedGreenForwardWeight q j *
              iteratedDeriv degree
                (completedGreenDslopeRay response i j) 0) /
          (degree.factorial : ℂ) =
      ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (q + 1),
          completedGreenForwardWeight p i *
            completedGreenForwardWeight q j *
              (iteratedDeriv degree
                (completedGreenDslopeRay response i j) 0 /
                  (degree.factorial : ℂ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (iteratedDeriv (degree + 1) response 0 /
            ((degree + 1).factorial : ℂ)) *
          ∑ i ∈ Finset.range (p + 1),
            ∑ j ∈ Finset.range (q + 1),
              completedGreenForwardWeight p i *
                completedGreenForwardWeight q j *
                  completedGreenHomogeneousDividedPower i j degree := by
      simp_rw [completedGreenDslopeRay_taylorCoefficient hresponse]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- All derivatives of the mixed ray sum below its total forward-difference
order vanish. -/
theorem iteratedDeriv_completedGreenDslopeMixedRaySum_eq_zero_of_lt
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    {p q degree : ℕ} (hdegree : degree < p + q) :
    iteratedDeriv degree
      (completedGreenDslopeMixedRaySum response p q) 0 = 0 := by
  have hcoeff := completedGreenDslopeMixedRaySum_taylorCoefficient
    hresponse p q degree
  rw [completedGreenMixedHomogeneousWeight_eq_zero_of_lt hdegree,
    mul_zero] at hcoeff
  exact (div_eq_zero_iff.mp hcoeff).resolve_right
    (by exact_mod_cast degree.factorial_ne_zero)

/-- The first surviving coefficient of the mixed ray sum. -/
theorem completedGreenDslopeMixedRaySum_taylorCoefficient_add
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    iteratedDeriv (p + q)
          (completedGreenDslopeMixedRaySum response p q) 0 /
        ((p + q).factorial : ℂ) =
      (iteratedDeriv (p + q + 1) response 0 /
          ((p + q + 1).factorial : ℂ)) *
        (p.factorial : ℂ) * (q.factorial : ℂ) := by
  rw [completedGreenDslopeMixedRaySum_taylorCoefficient hresponse,
    completedGreenMixedHomogeneousWeight_add]
  ring

/-- Coefficient extraction along the canonical nonzero steps.  No
Hilbert-valued differentiability is involved. -/
theorem tendsto_div_pow_canonicalGreenJetStep_of_analyticAt
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (order : ℕ)
    (hzero : ∀ degree < order, iteratedDeriv degree f 0 = 0) :
    Tendsto
      (fun k => f (canonicalGreenJetStep k) /
        canonicalGreenJetStep k ^ order)
      atTop
      (nhds (iteratedDeriv order f 0 / (order.factorial : ℂ))) := by
  rcases hf with ⟨series, hseries⟩
  let quotient : ℂ → ℂ := (Function.swap dslope 0)^[order] f
  have hquotientSeries : HasFPowerSeriesAt quotient
      ((FormalMultilinearSeries.fslope^[order]) series) 0 :=
    hseries.has_fpower_series_iterate_dslope_fslope order
  have hzeroQuotient : ∀ degree < order,
      (Function.swap dslope 0)^[degree] f 0 = 0 := by
    intro degree hdegree
    have hdegreeSeries :=
      hseries.has_fpower_series_iterate_dslope_fslope degree
    have hvalue := hdegreeSeries.coeff_zero (1 : Fin 0 → ℂ)
    change ((FormalMultilinearSeries.fslope^[degree]) series).coeff 0 =
      (Function.swap dslope 0)^[degree] f 0 at hvalue
    rw [← hvalue,
      FormalMultilinearSeries.coeff_iterate_fslope]
    simp only [zero_add]
    rw [hasFPowerSeriesAt_coeff_eq_iteratedDeriv_div_factorial
      hseries degree, hzero degree hdegree, zero_div]
  have hfactorization : ∀ z : ℂ,
      f z = z ^ order * quotient z := by
    intro z
    simpa [quotient] using
      (pow_sub_smul_iterate_dslope_of_zero order hzeroQuotient z).symm
  have hlimit : Tendsto (fun k => quotient (canonicalGreenJetStep k))
      atTop (nhds (quotient 0)) :=
    hquotientSeries.continuousAt.tendsto.comp
      canonicalGreenJetStep_tendsto_zero
  have hquotientZero : quotient 0 =
      iteratedDeriv order f 0 / (order.factorial : ℂ) := by
    have hvalue := hquotientSeries.coeff_zero (1 : Fin 0 → ℂ)
    change ((FormalMultilinearSeries.fslope^[order]) series).coeff 0 =
      quotient 0 at hvalue
    rw [← hvalue,
      FormalMultilinearSeries.coeff_iterate_fslope]
    simp only [zero_add]
    exact hasFPowerSeriesAt_coeff_eq_iteratedDeriv_div_factorial
      hseries order
  rw [hquotientZero] at hlimit
  apply hlimit.congr'
  filter_upwards with k
  have hstep : canonicalGreenJetStep k ≠ 0 := by
    unfold canonicalGreenJetStep
    exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero k)
  rw [hfactorization]
  field_simp [hstep]

/-- The iterated mixed forward difference of the total `dslope` kernel is
exactly the explicit double ray sum. -/
theorem completedGreenDslope_mixedForwardDifference_eq_raySum
    (response : ℂ → ℂ) (h : ℂ) (p q : ℕ) :
    (completedGreenForwardDifference h)^[p]
        (fun w => (completedGreenForwardDifference h)^[q]
          (fun z => dslope response w z) 0) 0 =
      completedGreenDslopeMixedRaySum response p q h := by
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  unfold completedGreenDslopeMixedRaySum
  apply Finset.sum_congr rfl
  intro i hi
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [completedGreenForwardWeight, completedGreenDslopeRay,
    nsmul_eq_mul]
  ring

/-- Scalar normalized mixed forward differences of the analytic completed
Green kernel converge to the corresponding response Taylor coefficient. -/
theorem completedGreenKernelForwardDifference_dslope_tendsto
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    Tendsto
      (fun k => completedGreenKernelForwardDifference
        (fun w z => dslope response w z)
        (canonicalGreenJetStep k) p q)
      atTop
      (nhds (iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ))) := by
  have hraw := tendsto_div_pow_canonicalGreenJetStep_of_analyticAt
    (completedGreenDslopeMixedRaySum_analyticAt hresponse p q) (p + q)
    (fun degree hdegree =>
      iteratedDeriv_completedGreenDslopeMixedRaySum_eq_zero_of_lt
        hresponse hdegree)
  rw [completedGreenDslopeMixedRaySum_taylorCoefficient_add
    hresponse] at hraw
  let scale : ℂ :=
    ((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹
  have hscaled := hraw.const_mul scale
  have hp : (p.factorial : ℂ) ≠ 0 := by
    exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast q.factorial_ne_zero
  have htarget : scale *
        ((iteratedDeriv (p + q + 1) response 0 /
            ((p + q + 1).factorial : ℂ)) *
          (p.factorial : ℂ) * (q.factorial : ℂ)) =
      iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ) := by
    dsimp [scale]
    field_simp [hp, hq]
  rw [htarget] at hscaled
  apply hscaled.congr'
  filter_upwards with k
  have hstep : canonicalGreenJetStep k ≠ 0 := by
    unfold canonicalGreenJetStep
    exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero k)
  have hstepStar : (starRingEnd ℂ) (canonicalGreenJetStep k) =
      canonicalGreenJetStep k := by
    simp [canonicalGreenJetStep]
  rw [completedGreenKernelForwardDifference,
    completedGreenDslope_mixedForwardDifference_eq_raySum]
  simp only [map_inv₀, map_mul, map_pow, map_natCast, hstepStar]
  dsimp [scale]
  have hpow : canonicalGreenJetStep k ^ (p + q) =
      canonicalGreenJetStep k ^ p * canonicalGreenJetStep k ^ q := by
    rw [pow_add]
  rw [hpow]
  field_simp [hp, hq, hstep]

/-! ## Specialization to the canonical completed response -/

/-- Every even Taylor coefficient of the completed normalized response is
zero.  This is derived from the existing division-free response recurrence
and the vanishing of the odd characteristic coefficients. -/
theorem completedNativeGreenResponseTaylorCoefficient_even_eq_zero
    (n : ℕ) :
    completedNativeGreenResponseTaylorCoefficient (2 * n) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      let term : ℕ → ℂ := fun i =>
        completedNativeGreenResponseTaylorCoefficient i *
          completedNativeFullCharacteristicTaylorCoefficient (2 * n - i)
      have hsum :
          ∑ i ∈ Finset.range (2 * n + 1), term i =
            completedNativeGreenResponseTaylorCoefficient (2 * n) *
              completedNativeFullCharacteristicTaylorCoefficient 0 := by
        calc
          (∑ i ∈ Finset.range (2 * n + 1), term i) = term (2 * n) := by
            apply Finset.sum_eq_single (2 * n)
            · intro i hi hne
              have hiLtSucc : i < 2 * n + 1 := Finset.mem_range.mp hi
              have hiLt : i < 2 * n := by omega
              by_cases heven : Even i
              · rcases heven with ⟨k, hk⟩
                have hkLt : k < n := by omega
                unfold term
                rw [hk, show k + k = 2 * k by omega,
                  ih k hkLt, zero_mul]
              · have hodd : Odd i := Nat.not_even_iff_odd.mp heven
                rcases hodd with ⟨k, hk⟩
                have hkLt : k < n := by omega
                unfold term
                rw [show 2 * n - i = 2 * (n - k - 1) + 1 by omega,
                  completedNativeFullCharacteristicTaylorCoefficient_odd,
                  mul_zero]
            · intro hmem
              exact (hmem (Finset.mem_range.mpr (by omega))).elim
          _ = completedNativeGreenResponseTaylorCoefficient (2 * n) *
                completedNativeFullCharacteristicTaylorCoefficient 0 := by
            simp [term]
      have hrec := completedNativeGreenResponse_coefficientRecurrence (2 * n)
      change (∑ i ∈ Finset.range (2 * n + 1), term i) = _ at hrec
      rw [hsum,
        completedNativeFullCharacteristicTaylorCoefficient_odd] at hrec
      simp only [mul_zero] at hrec
      have hF0 : completedNativeFullCharacteristicTaylorCoefficient 0 ≠ 0 := by
        rw [show 0 = 2 * 0 by omega,
          completedNativeFullCharacteristicTaylorCoefficient_even]
        exact completedNativeEvenCharacteristicCoefficient_zero_ne_zero
      exact (mul_eq_zero.mp hrec).resolve_right hF0

/-- The response coefficient selected by a mixed order `(p,q)` is exactly
the canonical polarized Green coefficient. -/
theorem completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized
    (p q : ℕ) :
    completedNativeGreenResponseTaylorCoefficient (p + q + 1) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
  by_cases heven : Even (p + q)
  · rcases heven with ⟨n, hn⟩
    have hdegree : p + q = 2 * n := by omega
    rw [hdegree,
      show 2 * n + 1 = 2 * n + 1 by rfl,
      completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
    unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
    rw [if_pos]
    · congr 2
      omega
    · exact ⟨n, by omega⟩
  · have hodd : Odd (p + q) := Nat.not_even_iff_odd.mp heven
    rcases hodd with ⟨n, hn⟩
    have hdegree : p + q = 2 * n + 1 := by omega
    rw [hdegree,
      show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
      completedNativeGreenResponseTaylorCoefficient_even_eq_zero]
    unfold polarizedGreenMomentCoefficient evenMomentDiagonalCoefficient
    rw [if_neg]
    intro hcontra
    exact heven hcontra

/-- The scalar completed Green kernel has the canonical polarized moment as
the all-order mixed forward-difference limit. -/
theorem completedNativeGreenKernelForwardDifference_dslope_tendsto
    (p q : ℕ) :
    Tendsto
      (fun k => completedGreenKernelForwardDifference
        (fun w z => dslope
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) w z)
        (canonicalGreenJetStep k) p q)
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hlimit := completedGreenKernelForwardDifference_dslope_tendsto
    completedNativeGreenNormalizedResponse_analyticAt p q
  have hcoefficient :
      iteratedDeriv (p + q + 1)
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) 0 /
        ((p + q + 1).factorial : ℂ) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q := by
    exact completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized p q
  rw [hcoefficient] at hlimit
  exact hlimit

/-- Derivative order represented by one parity-tagged Green jet. -/
def completedGreenParityOrder : ℕ ⊕ ℕ → ℕ
  | Sum.inl n => 2 * n
  | Sum.inr n => 2 * n + 1

/-- The real parts of the scalar completed-kernel limits are exactly the
four parity blocks of the canonical Green--Wronskian moment kernel. -/
theorem completedNativeGreenKernelForwardDifference_dslope_re_tendsto
    (i j : ℕ ⊕ ℕ) :
    Tendsto
      (fun k => (completedGreenKernelForwardDifference
        (fun w z => dslope
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) w z)
        (canonicalGreenJetStep k)
        (completedGreenParityOrder i)
        (completedGreenParityOrder j)).re)
      atTop
      (nhds (greenWronskianMomentKernel
        canonicalCompletedNativeLogDerivativeMoment i j)) := by
  have hcomplex :=
    (completedNativeGreenKernelForwardDifference_dslope_tendsto
      (completedGreenParityOrder i) (completedGreenParityOrder j))
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal
      | inr j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal
  | inr i =>
      cases j with
      | inl j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal
      | inr j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal

end

end CarrySelfAdjointOperator

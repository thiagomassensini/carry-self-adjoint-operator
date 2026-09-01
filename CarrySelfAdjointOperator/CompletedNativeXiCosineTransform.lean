import CarrySelfAdjointOperator.CompletedNativeXiThetaCosineRepresentation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The positive cosine transform of the completed native characteristic

This module differentiates the theta tail from
`CompletedNativeXiThetaCosineRepresentation` twice, justifies the two
half-line integrations by parts, and identifies the result with the explicit
positive kernel from `CompletedNativeXiCosineKernel`.
-/

open Real Set Filter MeasureTheory

namespace CarrySelfAdjointOperator

namespace XiThetaCosine

noncomputable section

/-- A positive-index theta mode after the logarithmic change of variables. -/
def thetaTailMode (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))

/-- First derivative of a logarithmic theta mode. -/
def thetaTailModeFirst (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 2 - 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) *
    thetaTailMode n u

/-- Second derivative of a logarithmic theta mode. -/
def thetaTailModeSecond (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 4 - 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u) +
      4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (4 * u)) *
    thetaTailMode n u

theorem hasDerivAt_thetaTailMode (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaTailMode n) (thetaTailModeFirst n u) u := by
  have hhalf : HasDerivAt (fun x : ℝ ↦ x / 2) (1 / 2) u :=
    (hasDerivAt_id u).div_const 2
  have hleft : HasDerivAt (fun x : ℝ ↦ Real.exp (x / 2))
      ((1 / 2) * Real.exp (u / 2)) u := by
    refine (((Real.hasDerivAt_exp (u / 2)).comp u hhalf).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  have htwo : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 u :=
    by
      refine (((hasDerivAt_id u).const_mul 2).congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
      · ring
  have hexp2 : HasDerivAt (fun x : ℝ ↦ Real.exp (2 * x))
      (2 * Real.exp (2 * u)) u := by
    refine (((Real.hasDerivAt_exp (2 * u)).comp u htwo).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  have hinner : HasDerivAt
      (fun x : ℝ ↦ -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))
      (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) u := by
    refine ((hexp2.const_mul
      (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  have hright : HasDerivAt
      (fun x : ℝ ↦ Real.exp
        (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)))
      ((-2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) u := by
    refine (((Real.hasDerivAt_exp
      (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))).comp u hinner).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  refine ((hleft.mul hright).congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · simp only [thetaTailMode, thetaTailModeFirst]
    ring

theorem hasDerivAt_thetaTailModeFirst (n : ℕ) (u : ℝ) :
    HasDerivAt (thetaTailModeFirst n) (thetaTailModeSecond n u) u := by
  have htwo : HasDerivAt (fun x : ℝ ↦ 2 * x) 2 u :=
    by
      refine (((hasDerivAt_id u).const_mul 2).congr_of_eventuallyEq ?_).congr_deriv ?_
      · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
      · ring
  have hexp2 : HasDerivAt (fun x : ℝ ↦ Real.exp (2 * x))
      (2 * Real.exp (2 * u)) u := by
    refine (((Real.hasDerivAt_exp (2 * u)).comp u htwo).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  have hfactor : HasDerivAt
      (fun x : ℝ ↦ 1 / 2 -
        2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))
      (-4 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) u := by
    refine (((hasDerivAt_const u (1 / 2 : ℝ)).sub
      (hexp2.const_mul
        (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2))).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  have hexp4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [show 4 * u = 2 * u + 2 * u by ring, Real.exp_add, pow_two]
  refine ((hfactor.mul (hasDerivAt_thetaTailMode n u)).congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · simp only [thetaTailModeFirst, thetaTailModeSecond]
    rw [hexp4]
    ring

private theorem summable_thetaGaussian (k : ℕ) (u : ℝ) :
    Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ k) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by
  have h := HurwitzKernelBounds.summable_f_nat k 1 (Real.exp_pos (2 * u))
  rw [show (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ k) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) =
      HurwitzKernelBounds.f_nat k 1 (Real.exp (2 * u)) by
    funext n
    simp only [HurwitzKernelBounds.f_nat, Nat.cast_add, Nat.cast_one]]
  exact h

theorem summable_thetaTailMode (u : ℝ) :
    Summable (fun n : ℕ ↦ thetaTailMode n u) := by
  have h := (summable_thetaGaussian 0 u).mul_left (Real.exp (u / 2))
  simpa [thetaTailMode] using h

theorem summable_thetaTailModeFirst (u : ℝ) :
    Summable (fun n : ℕ ↦ thetaTailModeFirst n u) := by
  have h0 := (summable_thetaGaussian 0 u).mul_left
    ((1 / 2 : ℝ) * Real.exp (u / 2))
  have h2 := (summable_thetaGaussian 2 u).mul_left
    (2 * Real.pi * Real.exp (u / 2) * Real.exp (2 * u))
  rw [show (fun n : ℕ ↦ thetaTailModeFirst n u) =
      fun n : ℕ ↦
        ((1 / 2 : ℝ) * Real.exp (u / 2)) *
            (1 * Real.exp
              (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) -
          (2 * Real.pi * Real.exp (u / 2) * Real.exp (2 * u)) *
            (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp
              (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) by
    funext n
    simp only [thetaTailModeFirst, thetaTailMode]
    ring]
  exact h0.sub h2

theorem summable_thetaTailModeSecond (u : ℝ) :
    Summable (fun n : ℕ ↦ thetaTailModeSecond n u) := by
  have h0 := (summable_thetaGaussian 0 u).mul_left
    ((1 / 4 : ℝ) * Real.exp (u / 2))
  have h2 := (summable_thetaGaussian 2 u).mul_left
    (6 * Real.pi * Real.exp (u / 2) * Real.exp (2 * u))
  have h4 := (summable_thetaGaussian 4 u).mul_left
    (4 * Real.pi ^ 2 * Real.exp (u / 2) * Real.exp (4 * u))
  rw [show (fun n : ℕ ↦ thetaTailModeSecond n u) =
      fun n : ℕ ↦
        ((1 / 4 : ℝ) * Real.exp (u / 2)) *
            (1 * Real.exp
              (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) -
          (6 * Real.pi * Real.exp (u / 2) * Real.exp (2 * u)) *
            (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp
              (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) +
          (4 * Real.pi ^ 2 * Real.exp (u / 2) * Real.exp (4 * u)) *
            (((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp
              (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) by
    funext n
    simp only [thetaTailModeSecond, thetaTailMode]
    ring]
  exact (h0.sub h2).add h4

/-- The actual first derivative of `thetaTail`, written as a mode sum. -/
def thetaTailFirst (u : ℝ) : ℝ :=
  2 * ∑' n : ℕ, thetaTailModeFirst n u

/-- The actual second derivative of `thetaTail`, written as a mode sum. -/
def thetaTailSecond (u : ℝ) : ℝ :=
  2 * ∑' n : ℕ, thetaTailModeSecond n u

theorem thetaTail_eq_two_mul_tsum (u : ℝ) :
    thetaTail u = 2 * ∑' n : ℕ, thetaTailMode n u := by
  have h := (HurwitzZeta.hasSum_nat_cosKernel₀ 0
    (Real.exp_pos (2 * u))).mul_left (Real.exp (u / 2))
  have hsum : HasSum (fun n : ℕ ↦ 2 * thetaTailMode n u) (thetaTail u) := by
    simpa [thetaTailMode, thetaTail,
      HurwitzZeta.evenKernel_eq_cosKernel_of_zero, mul_assoc, mul_left_comm,
      mul_comm] using h
  rw [← hsum.tsum_eq]
  exact tsum_mul_left

private theorem thetaTailModeFirst_expanded (n : ℕ) (u : ℝ) :
    thetaTailModeFirst n u =
      (1 / 2 : ℝ) * Real.exp (u / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) -
        2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) := by
  have h5 : Real.exp (5 * u / 2) = Real.exp (u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h5]
  simp only [thetaTailModeFirst, thetaTailMode]
  ring

private theorem thetaTailModeSecond_expanded (n : ℕ) (u : ℝ) :
    thetaTailModeSecond n u =
      (1 / 4 : ℝ) * Real.exp (u / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) -
        6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) +
        4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) := by
  have h5 : Real.exp (5 * u / 2) = Real.exp (u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h9 : Real.exp (9 * u / 2) = Real.exp (u / 2) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h5, h9]
  simp only [thetaTailModeSecond, thetaTailMode]
  ring

private def thetaLocalGaussian (x : ℝ) (k : ℕ) (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ k) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (2 * (x - 1)))

private def thetaFirstMajorant (x : ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp ((x + 1) / 2) * thetaLocalGaussian x 0 n +
    2 * Real.pi * Real.exp (5 * (x + 1) / 2) * thetaLocalGaussian x 2 n

private def thetaSecondMajorant (x : ℝ) (n : ℕ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp ((x + 1) / 2) * thetaLocalGaussian x 0 n +
    6 * Real.pi * Real.exp (5 * (x + 1) / 2) * thetaLocalGaussian x 2 n +
    4 * Real.pi ^ 2 * Real.exp (9 * (x + 1) / 2) * thetaLocalGaussian x 4 n

private theorem summable_thetaLocalGaussian (x : ℝ) (k : ℕ) :
    Summable (thetaLocalGaussian x k) := by
  change Summable (fun n : ℕ ↦
    (((n + 1 : ℕ) : ℝ) ^ k) *
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (2 * (x - 1))))
  exact summable_thetaGaussian k (x - 1)

private theorem summable_thetaFirstMajorant (x : ℝ) :
    Summable (thetaFirstMajorant x) := by
  unfold thetaFirstMajorant
  exact ((summable_thetaLocalGaussian x 0).mul_left
    ((1 / 2 : ℝ) * Real.exp ((x + 1) / 2))).add
      ((summable_thetaLocalGaussian x 2).mul_left
        (2 * Real.pi * Real.exp (5 * (x + 1) / 2)))

private theorem summable_thetaSecondMajorant (x : ℝ) :
    Summable (thetaSecondMajorant x) := by
  unfold thetaSecondMajorant
  exact (((summable_thetaLocalGaussian x 0).mul_left
    ((1 / 4 : ℝ) * Real.exp ((x + 1) / 2))).add
      ((summable_thetaLocalGaussian x 2).mul_left
        (6 * Real.pi * Real.exp (5 * (x + 1) / 2)))).add
      ((summable_thetaLocalGaussian x 4).mul_left
        (4 * Real.pi ^ 2 * Real.exp (9 * (x + 1) / 2)))

private theorem theta_gaussian_le_local {x y : ℝ}
    (hy : y ∈ Ioo (x - 1) (x + 1)) (n : ℕ) :
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y)) ≤
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (2 * (x - 1))) := by
  apply Real.exp_le_exp.mpr
  have he : Real.exp (2 * (x - 1)) ≤ Real.exp (2 * y) := by
    apply Real.exp_le_exp.mpr
    linarith [hy.1]
  have hc : 0 ≤ Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

private theorem norm_thetaTailModeFirst_le {x y : ℝ}
    (hy : y ∈ Ioo (x - 1) (x + 1)) (n : ℕ) :
    ‖thetaTailModeFirst n y‖ ≤ thetaFirstMajorant x n := by
  have h1 : Real.exp (y / 2) ≤ Real.exp ((x + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hy.2]
  have h5 : Real.exp (5 * y / 2) ≤ Real.exp (5 * (x + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hy.2]
  have hg := theta_gaussian_le_local hy n
  rw [thetaTailModeFirst_expanded, Real.norm_eq_abs]
  calc
    |_ - _| ≤
        |(1 / 2 : ℝ) * Real.exp (y / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y))| +
        |2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * y / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y))| :=
      abs_sub _ _
    _ =
        (1 / 2 : ℝ) * Real.exp (y / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y)) +
        2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * y / 2) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y)) := by
      congr 1 <;> rw [abs_of_nonneg] <;> positivity
    _ ≤ thetaFirstMajorant x n := by
      have hterm0 :
          (1 / 2 : ℝ) * Real.exp (y / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y)) ≤
            (1 / 2 : ℝ) * Real.exp ((x + 1) / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                Real.exp (2 * (x - 1))) := by
        gcongr
      have hterm2 :
          2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * y / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y)) ≤
            2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
              Real.exp (5 * (x + 1) / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                Real.exp (2 * (x - 1))) := by
        gcongr
      calc
        _ ≤
            (1 / 2 : ℝ) * Real.exp ((x + 1) / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                  Real.exp (2 * (x - 1))) +
              2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                Real.exp (5 * (x + 1) / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                  Real.exp (2 * (x - 1))) := add_le_add hterm0 hterm2
        _ = thetaFirstMajorant x n := by
          unfold thetaFirstMajorant thetaLocalGaussian
          simp only [pow_zero, one_mul]
          ring

private theorem norm_thetaTailModeSecond_le {x y : ℝ}
    (hy : y ∈ Ioo (x - 1) (x + 1)) (n : ℕ) :
    ‖thetaTailModeSecond n y‖ ≤ thetaSecondMajorant x n := by
  have h1 : Real.exp (y / 2) ≤ Real.exp ((x + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hy.2]
  have h5 : Real.exp (5 * y / 2) ≤ Real.exp (5 * (x + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hy.2]
  have h9 : Real.exp (9 * y / 2) ≤ Real.exp (9 * (x + 1) / 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hy.2]
  have hg := theta_gaussian_le_local hy n
  let a : ℝ := (1 / 4 : ℝ) * Real.exp (y / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y))
  let b : ℝ := 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * y / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y))
  let c : ℝ := 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * y / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * y))
  have ha : 0 ≤ a := by unfold a; positivity
  have hb : 0 ≤ b := by unfold b; positivity
  have hc : 0 ≤ c := by unfold c; positivity
  rw [thetaTailModeSecond_expanded, Real.norm_eq_abs]
  change |a - b + c| ≤ _
  calc
    |a - b + c| ≤ |a - b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := add_le_add (abs_sub _ _) le_rfl
    _ = a + b + c := by rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc]
    _ ≤ thetaSecondMajorant x n := by
      have hterm0 : a ≤
          (1 / 4 : ℝ) * Real.exp ((x + 1) / 2) *
            Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
              Real.exp (2 * (x - 1))) := by
        unfold a
        gcongr
      have hterm2 : b ≤
          6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
            Real.exp (5 * (x + 1) / 2) *
            Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
              Real.exp (2 * (x - 1))) := by
        unfold b
        gcongr
      have hterm4 : c ≤
          4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 *
            Real.exp (9 * (x + 1) / 2) *
            Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
              Real.exp (2 * (x - 1))) := by
        unfold c
        gcongr
      calc
        a + b + c ≤
            (1 / 4 : ℝ) * Real.exp ((x + 1) / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                  Real.exp (2 * (x - 1))) +
              6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                Real.exp (5 * (x + 1) / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                  Real.exp (2 * (x - 1))) +
              4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 *
                Real.exp (9 * (x + 1) / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 *
                  Real.exp (2 * (x - 1))) := add_le_add (add_le_add hterm0 hterm2) hterm4
        _ = thetaSecondMajorant x n := by
          unfold thetaSecondMajorant thetaLocalGaussian
          simp only [pow_zero, one_mul]
          ring

theorem hasDerivAt_thetaTail (x : ℝ) :
    HasDerivAt thetaTail (thetaTailFirst x) x := by
  have hxmem : x ∈ Ioo (x - 1) (x + 1) := by constructor <;> linarith
  have hsum : HasDerivAt
      (fun y : ℝ ↦ ∑' n : ℕ, thetaTailMode n y)
      (∑' n : ℕ, thetaTailModeFirst n x) x :=
    hasDerivAt_tsum_of_isPreconnected
      (g := thetaTailMode) (g' := thetaTailModeFirst)
      (u := thetaFirstMajorant x) (t := Ioo (x - 1) (x + 1))
      (y₀ := x) (y := x)
      (summable_thetaFirstMajorant x) isOpen_Ioo isPreconnected_Ioo
      (fun n y _hy ↦ hasDerivAt_thetaTailMode n y)
      (fun n y hy ↦ norm_thetaTailModeFirst_le hy n)
      hxmem (summable_thetaTailMode x) hxmem
  refine ((hsum.const_mul 2).congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun y ↦ thetaTail_eq_two_mul_tsum y)
  · rfl

theorem hasDerivAt_thetaTailFirst (x : ℝ) :
    HasDerivAt thetaTailFirst (thetaTailSecond x) x := by
  have hxmem : x ∈ Ioo (x - 1) (x + 1) := by constructor <;> linarith
  have hsum : HasDerivAt
      (fun y : ℝ ↦ ∑' n : ℕ, thetaTailModeFirst n y)
      (∑' n : ℕ, thetaTailModeSecond n x) x :=
    hasDerivAt_tsum_of_isPreconnected
      (g := thetaTailModeFirst) (g' := thetaTailModeSecond)
      (u := thetaSecondMajorant x) (t := Ioo (x - 1) (x + 1))
      (y₀ := x) (y := x)
      (summable_thetaSecondMajorant x) isOpen_Ioo isPreconnected_Ioo
      (fun n y _hy ↦ hasDerivAt_thetaTailModeFirst n y)
      (fun n y hy ↦ norm_thetaTailModeSecond_le hy n)
      hxmem (summable_thetaTailModeFirst x) hxmem
  exact hsum.const_mul 2

theorem thetaTailModeSecond_sub_quarter (n : ℕ) (u : ℝ) :
    thetaTailModeSecond n u - (1 / 4 : ℝ) * thetaTailMode n u =
      completedNativeXiCosineKernelTerm (n + 1 : ℤ) u := by
  have hcast : (((n : ℤ) + 1 : ℤ) : ℝ) = (((n + 1 : ℕ) : ℝ)) := by
    norm_cast
  have h5 : Real.exp (5 * u / 2) = Real.exp (u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [show 4 * u = 2 * u + 2 * u by ring, Real.exp_add, pow_two]
  have h9 : Real.exp (9 * u / 2) = Real.exp (u / 2) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [completedNativeXiCosineKernelTerm_eq, h5, h9]
  simp only [thetaTailModeSecond, thetaTailMode,
    Nat.cast_add, Nat.cast_one]
  rw [hcast, h4]
  simp only [Nat.cast_add, Nat.cast_one]
  ring_nf

theorem thetaTailSecond_sub_quarter (u : ℝ) :
    thetaTailSecond u - (1 / 4 : ℝ) * thetaTail u =
      completedNativeXiCosineKernel u := by
  have hscaled : Summable (fun n : ℕ ↦
      (1 / 4 : ℝ) * thetaTailMode n u) :=
    (summable_thetaTailMode u).mul_left (1 / 4 : ℝ)
  calc
    thetaTailSecond u - (1 / 4 : ℝ) * thetaTail u =
        2 * ((∑' n : ℕ, thetaTailModeSecond n u) -
          (1 / 4 : ℝ) * ∑' n : ℕ, thetaTailMode n u) := by
      rw [thetaTail_eq_two_mul_tsum]
      simp only [thetaTailSecond]
      ring
    _ = 2 * ∑' n : ℕ,
          (thetaTailModeSecond n u - (1 / 4 : ℝ) * thetaTailMode n u) := by
      rw [← tsum_mul_left]
      rw [← (summable_thetaTailModeSecond u).tsum_sub hscaled]
    _ = 2 * ∑' n : ℕ,
          completedNativeXiCosineKernelTerm (n + 1 : ℤ) u := by
      congr 1
      apply tsum_congr
      exact fun n ↦ thetaTailModeSecond_sub_quarter n u
    _ = completedNativeXiCosineKernel u :=
      (completedNativeXiCosineKernel_eq_two_mul_tsum u).symm

private theorem evenKernel_exp_neg_two (u : ℝ) :
    HurwitzZeta.evenKernel 0 (Real.exp (-2 * u)) =
      Real.exp u * HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) := by
  have hroot : Real.exp (2 * u) ^ (1 / 2 : ℝ) = Real.exp u := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hinv : 1 / Real.exp (2 * u) = Real.exp (-2 * u) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  have hfe := HurwitzZeta.evenKernel_functional_equation
    (0 : AddCircle (1 : ℝ)) (Real.exp (2 * u))
  rw [hroot, hinv, ← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at hfe
  calc
    HurwitzZeta.evenKernel 0 (Real.exp (-2 * u)) =
        Real.exp u *
          (1 / Real.exp u * HurwitzZeta.evenKernel 0 (Real.exp (-2 * u))) := by
      field_simp
    _ = Real.exp u * HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) := by
      rw [← hfe]

theorem thetaTail_neg (u : ℝ) :
    thetaTail (-u) = thetaTail u + Real.exp (u / 2) - Real.exp (-u / 2) := by
  have htheta := evenKernel_exp_neg_two u
  unfold thetaTail
  rw [show 2 * -u = -2 * u by ring, htheta]
  rw [show -u / 2 = -(u / 2) by ring]
  rw [mul_sub, ← mul_assoc]
  rw [show Real.exp (-(u / 2)) * Real.exp u = Real.exp (u / 2) by
    rw [← Real.exp_add]
    congr 1
    ring]
  ring

theorem thetaTailFirst_zero : thetaTailFirst 0 = -(1 / 2 : ℝ) := by
  have hneg : HasDerivAt (fun u : ℝ ↦ -u) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).neg
  have hleft : HasDerivAt (fun u : ℝ ↦ thetaTail (-u))
      (thetaTailFirst 0 * (-1)) 0 := by
    refine (((hasDerivAt_thetaTail (-0)).comp 0 hneg).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · simp only [neg_zero]
  have hhalf : HasDerivAt (fun u : ℝ ↦ u / 2) (1 / 2) 0 :=
    (hasDerivAt_id (0 : ℝ)).div_const 2
  have hposExp : HasDerivAt (fun u : ℝ ↦ Real.exp (u / 2)) (1 / 2) 0 := by
    refine (hhalf.exp.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · norm_num
  have hnegHalf : HasDerivAt (fun u : ℝ ↦ -u / 2) (-1 / 2) 0 :=
    ((hasDerivAt_id (0 : ℝ)).neg).div_const 2
  have hnegExp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u / 2)) (-1 / 2) 0 := by
    refine (hnegHalf.exp.congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · norm_num
  have hright : HasDerivAt
      (fun u : ℝ ↦ thetaTail u + Real.exp (u / 2) - Real.exp (-u / 2))
      ((thetaTailFirst 0 + 1 / 2) - (-1 / 2)) 0 :=
    ((hasDerivAt_thetaTail 0).add hposExp).sub hnegExp
  have hright' : HasDerivAt (fun u : ℝ ↦ thetaTail (-u))
      ((thetaTailFirst 0 + 1 / 2) - (-1 / 2)) 0 :=
    hright.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u ↦ thetaTail_neg u))
  have hderiv := hleft.unique hright'
  linarith

private def thetaFirstDecayCoefficient (n : ℕ) : ℝ :=
  ((1 / 2 : ℝ) + 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)

private def thetaSecondDecayCoefficient (n : ℕ) : ℝ :=
  ((1 / 4 : ℝ) + 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 +
      4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)

private theorem summable_thetaFirstDecayCoefficient :
    Summable thetaFirstDecayCoefficient := by
  have h0 := (summable_thetaGaussian 0 0).mul_left (1 / 2 : ℝ)
  have h2 := (summable_thetaGaussian 2 0).mul_left (2 * Real.pi)
  rw [show thetaFirstDecayCoefficient = fun n : ℕ ↦
      (1 / 2 : ℝ) *
          (1 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * 0))) +
        2 * Real.pi *
          (((n + 1 : ℕ) : ℝ) ^ 2 *
            Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * 0))) by
    funext n
    simp only [thetaFirstDecayCoefficient, mul_zero, Real.exp_zero, mul_one]
    ring]
  exact h0.add h2

private theorem summable_thetaSecondDecayCoefficient :
    Summable thetaSecondDecayCoefficient := by
  have h0 := (summable_thetaGaussian 0 0).mul_left (1 / 4 : ℝ)
  have h2 := (summable_thetaGaussian 2 0).mul_left (6 * Real.pi)
  have h4 := (summable_thetaGaussian 4 0).mul_left (4 * Real.pi ^ 2)
  rw [show thetaSecondDecayCoefficient = fun n : ℕ ↦
      (1 / 4 : ℝ) *
          (1 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * 0))) +
        6 * Real.pi *
          (((n + 1 : ℕ) : ℝ) ^ 2 *
            Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * 0))) +
        4 * Real.pi ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ 4 *
            Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * 0))) by
    funext n
    simp only [thetaSecondDecayCoefficient, mul_zero, Real.exp_zero, mul_one]
    ring]
  exact (h0.add h2).add h4

private theorem theta_gaussian_le_global_decay {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-6 * u) := by
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  let c : ℝ := Real.pi * m ^ 2
  have hm : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hm2 : 1 ≤ m ^ 2 := by
    nlinarith [mul_nonneg (zero_le_one.trans hm) (sub_nonneg.mpr hm)]
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc3 : 3 ≤ c := by
    calc
      3 ≤ Real.pi := Real.pi_gt_three.le
      _ ≤ Real.pi * m ^ 2 := by
        simpa using mul_le_mul_of_nonneg_left hm2 Real.pi_pos.le
  have he : 1 + 2 * u ≤ Real.exp (2 * u) := by
    linarith [Real.add_one_le_exp (2 * u)]
  have hmul : c * (1 + 2 * u) ≤ c * Real.exp (2 * u) :=
    mul_le_mul_of_nonneg_left he hc0
  have h6 : 6 * u ≤ 2 * c * u := by
    have := mul_le_mul_of_nonneg_right hc3 (by linarith : 0 ≤ 2 * u)
    nlinarith
  have hexponent : -c * Real.exp (2 * u) ≤ -c - 6 * u := by
    have hmain : c + 6 * u ≤ c * Real.exp (2 * u) := by
      calc
        c + 6 * u ≤ c + 2 * c * u := by
          simpa [add_comm] using add_le_add_left h6 c
        _ = c * (1 + 2 * u) := by ring
        _ ≤ c * Real.exp (2 * u) := hmul
    linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [c, m, add_comm, add_left_comm] using hexponent

private theorem theta_nine_half_envelope {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Real.exp (9 * u / 2) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
  calc
    Real.exp (9 * u / 2) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
      Real.exp (9 * u / 2) *
        (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-6 * u)) :=
      mul_le_mul_of_nonneg_left (theta_gaussian_le_global_decay hu n)
        (Real.exp_pos _).le
    _ = Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
      rw [show Real.exp (9 * u / 2) *
          (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) * Real.exp (-6 * u)) =
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.exp (9 * u / 2) * Real.exp (-6 * u)) by ring]
      rw [← Real.exp_add]
      congr 2
      ring

private theorem theta_one_half_envelope {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Real.exp (u / 2) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
  calc
    _ ≤ Real.exp (9 * u / 2) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) := by
      gcongr
      linarith
    _ ≤ _ := theta_nine_half_envelope hu n

private theorem theta_five_half_envelope {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    Real.exp (5 * u / 2) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) ≤
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
  calc
    _ ≤ Real.exp (9 * u / 2) *
        Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) := by
      gcongr
      norm_num
    _ ≤ _ := theta_nine_half_envelope hu n

private theorem norm_thetaTailModeFirst_decay {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ‖thetaTailModeFirst n u‖ ≤
      thetaFirstDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
  let a : ℝ := (1 / 2 : ℝ) * Real.exp (u / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))
  let b : ℝ := 2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))
  have ha : 0 ≤ a := by unfold a; positivity
  have hb : 0 ≤ b := by unfold b; positivity
  rw [thetaTailModeFirst_expanded, Real.norm_eq_abs]
  change |a - b| ≤ _
  calc
    |a - b| ≤ |a| + |b| := abs_sub _ _
    _ = a + b := by rw [abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤
        (1 / 2 : ℝ) *
            (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.exp (-(3 / 2 : ℝ) * u)) +
          (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.exp (-(3 / 2 : ℝ) * u)) := by
      apply add_le_add
      · unfold a
        calc
          (1 / 2 : ℝ) * Real.exp (u / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
              (1 / 2 : ℝ) *
                (Real.exp (u / 2) *
                  Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by ring
          _ ≤ (1 / 2 : ℝ) *
                (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                  Real.exp (-(3 / 2 : ℝ) * u)) :=
            mul_le_mul_of_nonneg_left (theta_one_half_envelope hu n) (by norm_num)
      · unfold b
        calc
          2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
              (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                (Real.exp (5 * u / 2) *
                  Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by ring
          _ ≤ (2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                  Real.exp (-(3 / 2 : ℝ) * u)) :=
            mul_le_mul_of_nonneg_left (theta_five_half_envelope hu n) (by positivity)
    _ = thetaFirstDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
      unfold thetaFirstDecayCoefficient
      ring

private theorem norm_thetaTailModeSecond_decay {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    ‖thetaTailModeSecond n u‖ ≤
      thetaSecondDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
  let a : ℝ := (1 / 4 : ℝ) * Real.exp (u / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))
  let b : ℝ := 6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))
  let c : ℝ := 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u / 2) *
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))
  have ha : 0 ≤ a := by unfold a; positivity
  have hb : 0 ≤ b := by unfold b; positivity
  have hc : 0 ≤ c := by unfold c; positivity
  rw [thetaTailModeSecond_expanded, Real.norm_eq_abs]
  change |a - b + c| ≤ _
  calc
    |a - b + c| ≤ |a - b| + |c| := abs_add_le _ _
    _ ≤ (|a| + |b|) + |c| := add_le_add (abs_sub _ _) le_rfl
    _ = a + b + c := by rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg hc]
    _ ≤
        (1 / 4 : ℝ) *
            (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.exp (-(3 / 2 : ℝ) * u)) +
          (6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.exp (-(3 / 2 : ℝ) * u)) +
          (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4) *
            (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
              Real.exp (-(3 / 2 : ℝ) * u)) := by
      apply add_le_add
      · apply add_le_add
        · unfold a
          calc
            (1 / 4 : ℝ) * Real.exp (u / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
                (1 / 4 : ℝ) *
                  (Real.exp (u / 2) *
                    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by ring
            _ ≤ (1 / 4 : ℝ) *
                  (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                    Real.exp (-(3 / 2 : ℝ) * u)) :=
              mul_le_mul_of_nonneg_left (theta_one_half_envelope hu n) (by norm_num)
        · unfold b
          calc
            6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (5 * u / 2) *
                Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
                (6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                  (Real.exp (5 * u / 2) *
                    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by ring
            _ ≤ (6 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                  (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                    Real.exp (-(3 / 2 : ℝ) * u)) :=
              mul_le_mul_of_nonneg_left (theta_five_half_envelope hu n) (by positivity)
      · unfold c
        calc
          4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (9 * u / 2) *
              Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u)) =
              (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4) *
                (Real.exp (9 * u / 2) *
                  Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (2 * u))) := by ring
          _ ≤ (4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 4) *
                (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) *
                  Real.exp (-(3 / 2 : ℝ) * u)) :=
            mul_le_mul_of_nonneg_left (theta_nine_half_envelope hu n) (by positivity)
    _ = thetaSecondDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
      unfold thetaSecondDecayCoefficient
      ring

private theorem thetaFirstDecayCoefficient_nonneg (n : ℕ) :
    0 ≤ thetaFirstDecayCoefficient n := by
  unfold thetaFirstDecayCoefficient
  positivity

private theorem thetaSecondDecayCoefficient_nonneg (n : ℕ) :
    0 ≤ thetaSecondDecayCoefficient n := by
  unfold thetaSecondDecayCoefficient
  positivity

theorem norm_thetaTailFirst_le_decay {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaTailFirst u‖ ≤
      (2 * ∑' n : ℕ, thetaFirstDecayCoefficient n) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖thetaTailModeFirst n u‖) :=
    (summable_thetaTailModeFirst u).norm
  have hbound : Summable (fun n : ℕ ↦
      thetaFirstDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u)) :=
    summable_thetaFirstDecayCoefficient.mul_right _
  calc
    ‖thetaTailFirst u‖ = 2 * ‖∑' n : ℕ, thetaTailModeFirst n u‖ := by
      simp only [thetaTailFirst, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * ∑' n : ℕ, ‖thetaTailModeFirst n u‖ := by
      gcongr
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ 2 * ∑' n : ℕ,
        thetaFirstDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
      exact mul_le_mul_of_nonneg_left
        (hnorm.tsum_le_tsum (fun n ↦ norm_thetaTailModeFirst_decay hu n) hbound)
        (by norm_num)
    _ = (2 * ∑' n : ℕ, thetaFirstDecayCoefficient n) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
      rw [tsum_mul_right]
      ring

theorem norm_thetaTailSecond_le_decay {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaTailSecond u‖ ≤
      (2 * ∑' n : ℕ, thetaSecondDecayCoefficient n) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖thetaTailModeSecond n u‖) :=
    (summable_thetaTailModeSecond u).norm
  have hbound : Summable (fun n : ℕ ↦
      thetaSecondDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u)) :=
    summable_thetaSecondDecayCoefficient.mul_right _
  calc
    ‖thetaTailSecond u‖ = 2 * ‖∑' n : ℕ, thetaTailModeSecond n u‖ := by
      simp only [thetaTailSecond, norm_mul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * ∑' n : ℕ, ‖thetaTailModeSecond n u‖ := by
      gcongr
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ 2 * ∑' n : ℕ,
        thetaSecondDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
      exact mul_le_mul_of_nonneg_left
        (hnorm.tsum_le_tsum (fun n ↦ norm_thetaTailModeSecond_decay hu n) hbound)
        (by norm_num)
    _ = (2 * ∑' n : ℕ, thetaSecondDecayCoefficient n) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
      rw [tsum_mul_right]
      ring

theorem integrableOn_thetaTail : IntegrableOn thetaTail (Ioi (0 : ℝ)) := by
  have hc : IntegrableOn (fun u : ℝ ↦ (thetaTail u : ℂ)) (Ioi (0 : ℝ)) := by
    apply integrable_profile.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact profile_of_pos hu
  have hre := hc.re
  change Integrable thetaTail (volume.restrict (Ioi (0 : ℝ)))
  simpa using hre

theorem continuous_thetaTailFirst : Continuous thetaTailFirst := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (hasDerivAt_thetaTailFirst x).continuousAt

private theorem aestronglyMeasurable_thetaTailSecond
    (meas : Measure ℝ := volume) : AEStronglyMeasurable thetaTailSecond meas := by
  have hsum : AEMeasurable
      (fun u : ℝ ↦ ∑' n : ℕ, thetaTailModeSecond n u) meas :=
    AEMeasurable.tsum (fun n ↦
      (by
        unfold thetaTailModeSecond thetaTailMode
        fun_prop : Continuous (thetaTailModeSecond n)).aemeasurable)
  have hmul : AEMeasurable thetaTailSecond meas := by
    unfold thetaTailSecond
    exact aemeasurable_const.mul hsum
  exact hmul.aestronglyMeasurable

theorem integrableOn_thetaTailFirst :
    IntegrableOn thetaTailFirst (Ioi (0 : ℝ)) := by
  let C : ℝ := 2 * ∑' n : ℕ, thetaFirstDecayCoefficient n
  have hdecay : IntegrableOn
      (fun u : ℝ ↦ C * Real.exp (-(3 / 2 : ℝ) * u)) (Ioi (0 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (a := -(3 / 2 : ℝ)) (by norm_num) 0).const_mul C
  apply hdecay.mono'
  · exact continuous_thetaTailFirst.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_thetaTailFirst_le_decay hu.le

theorem integrableOn_thetaTailSecond :
    IntegrableOn thetaTailSecond (Ioi (0 : ℝ)) := by
  let C : ℝ := 2 * ∑' n : ℕ, thetaSecondDecayCoefficient n
  have hdecay : IntegrableOn
      (fun u : ℝ ↦ C * Real.exp (-(3 / 2 : ℝ) * u)) (Ioi (0 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (a := -(3 / 2 : ℝ)) (by norm_num) 0).const_mul C
  apply hdecay.mono'
  · exact aestronglyMeasurable_thetaTailSecond.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_thetaTailSecond_le_decay hu.le

private def thetaZeroDecayCoefficient (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)

private theorem summable_thetaZeroDecayCoefficient :
    Summable thetaZeroDecayCoefficient := by
  have h := summable_thetaGaussian 0 0
  change Summable (fun n : ℕ ↦
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2))
  simpa using h

private theorem thetaZeroDecayCoefficient_nonneg (n : ℕ) :
    0 ≤ thetaZeroDecayCoefficient n := by
  unfold thetaZeroDecayCoefficient
  positivity

theorem norm_thetaTail_le_decay {u : ℝ} (hu : 0 ≤ u) :
    ‖thetaTail u‖ ≤
      (2 * ∑' n : ℕ, thetaZeroDecayCoefficient n) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖thetaTailMode n u‖) :=
    (summable_thetaTailMode u).norm
  have hbound : Summable (fun n : ℕ ↦
      thetaZeroDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u)) :=
    summable_thetaZeroDecayCoefficient.mul_right _
  calc
    ‖thetaTail u‖ = 2 * ‖∑' n : ℕ, thetaTailMode n u‖ := by
      rw [thetaTail_eq_two_mul_tsum, norm_mul]
      norm_num
    _ ≤ 2 * ∑' n : ℕ, ‖thetaTailMode n u‖ := by
      exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (by norm_num)
    _ ≤ 2 * ∑' n : ℕ,
        thetaZeroDecayCoefficient n * Real.exp (-(3 / 2 : ℝ) * u) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply hnorm.tsum_le_tsum _ hbound
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold thetaTailMode; positivity)]
      unfold thetaTailMode thetaZeroDecayCoefficient
      exact theta_one_half_envelope hu n
    _ = (2 * ∑' n : ℕ, thetaZeroDecayCoefficient n) *
        Real.exp (-(3 / 2 : ℝ) * u) := by
      rw [tsum_mul_right]
      ring

/-- The theta tail itself has a fixed exponential envelope on the positive
half-line.  This public existential form hides the auxiliary mode sum, which
is useful when polynomially weighted theta moments are developed downstream. -/
theorem exists_thetaTail_exp_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖thetaTail u‖ ≤ C * Real.exp (-(3 / 2 : ℝ) * u) := by
  let C : ℝ := 2 * ∑' n : ℕ, thetaZeroDecayCoefficient n
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (tsum_nonneg thetaZeroDecayCoefficient_nonneg)
  exact ⟨C, hC, fun hu ↦ norm_thetaTail_le_decay hu⟩

/-- The first theta-tail derivative also has a fixed exponential envelope on
the positive half-line. -/
theorem exists_thetaTailFirst_exp_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖thetaTailFirst u‖ ≤ C * Real.exp (-(3 / 2 : ℝ) * u) := by
  let C : ℝ := 2 * ∑' n : ℕ, thetaFirstDecayCoefficient n
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by norm_num) (tsum_nonneg thetaFirstDecayCoefficient_nonneg)
  exact ⟨C, hC, fun hu ↦ norm_thetaTailFirst_le_decay hu⟩

private theorem tendsto_zero_of_norm_le_exp_decay
    (f : ℝ → ℝ) (C : ℝ)
    (hbound : ∀ {u : ℝ}, 0 ≤ u → ‖f u‖ ≤ C * Real.exp (-(3 / 2 : ℝ) * u)) :
    Tendsto f atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun u ↦ norm_nonneg (f u))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact hbound hu
  · have hexp : Tendsto (fun u : ℝ ↦ Real.exp (-(3 / 2 : ℝ) * u))
        atTop (nhds 0) := by
      exact Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(3 / 2 : ℝ) < 0))
    simpa using hexp.const_mul C

theorem thetaTail_tendsto_zero : Tendsto thetaTail atTop (nhds 0) :=
  tendsto_zero_of_norm_le_exp_decay thetaTail
    (2 * ∑' n : ℕ, thetaZeroDecayCoefficient n)
    (fun hu ↦ norm_thetaTail_le_decay hu)

theorem thetaTailFirst_tendsto_zero : Tendsto thetaTailFirst atTop (nhds 0) :=
  tendsto_zero_of_norm_le_exp_decay thetaTailFirst
    (2 * ∑' n : ℕ, thetaFirstDecayCoefficient n)
    (fun hu ↦ norm_thetaTailFirst_le_decay hu)

theorem thetaTailSecond_tendsto_zero : Tendsto thetaTailSecond atTop (nhds 0) :=
  tendsto_zero_of_norm_le_exp_decay thetaTailSecond
    (2 * ∑' n : ℕ, thetaSecondDecayCoefficient n)
    (fun hu ↦ norm_thetaTailSecond_le_decay hu)

private theorem hasDerivAt_sin_mul (t u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.sin (t * x)) (t * Real.cos (t * u)) u := by
  have hlinear : HasDerivAt (fun x : ℝ ↦ t * x) t u := by
    refine (((hasDerivAt_id u).const_mul t).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  refine (((Real.hasDerivAt_sin (t * u)).comp u hlinear).congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · ring

private theorem hasDerivAt_cos_mul (t u : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Real.cos (t * x)) (-t * Real.sin (t * u)) u := by
  have hlinear : HasDerivAt (fun x : ℝ ↦ t * x) t u := by
    refine (((hasDerivAt_id u).const_mul t).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    · ring
  refine (((Real.hasDerivAt_cos (t * u)).comp u hlinear).congr_of_eventuallyEq ?_).congr_deriv ?_
  · exact Filter.Eventually.of_forall (fun _ ↦ rfl)
  · ring

private theorem integrableOn_mul_sin {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (t : ℝ) :
    IntegrableOn (fun u : ℝ ↦ f u * Real.sin (t * u)) (Ioi (0 : ℝ)) := by
  apply hf.mul_bdd
  · exact (by fun_prop : Continuous (fun u : ℝ ↦ Real.sin (t * u))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t * u))

private theorem integrableOn_mul_cos {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (t : ℝ) :
    IntegrableOn (fun u : ℝ ↦ f u * Real.cos (t * u)) (Ioi (0 : ℝ)) := by
  apply hf.mul_bdd
  · exact (by fun_prop : Continuous (fun u : ℝ ↦ Real.cos (t * u))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun u ↦ by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * u))

private theorem thetaTail_mul_sin_tendsto_zero (t : ℝ) :
    Tendsto (fun u : ℝ ↦ thetaTail u * Real.sin (t * u)) atTop (nhds 0) := by
  apply tendsto_zero_of_norm_le_exp_decay _
    (2 * ∑' n : ℕ, thetaZeroDecayCoefficient n)
  intro u hu
  rw [norm_mul]
  calc
    ‖thetaTail u‖ * ‖Real.sin (t * u)‖ ≤ ‖thetaTail u‖ * 1 := by
      gcongr
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (t * u)
    _ = ‖thetaTail u‖ := by ring
    _ ≤ _ := norm_thetaTail_le_decay hu

private theorem thetaTailFirst_mul_cos_tendsto_zero (t : ℝ) :
    Tendsto (fun u : ℝ ↦ thetaTailFirst u * Real.cos (t * u)) atTop (nhds 0) := by
  apply tendsto_zero_of_norm_le_exp_decay _
    (2 * ∑' n : ℕ, thetaFirstDecayCoefficient n)
  intro u hu
  rw [norm_mul]
  calc
    ‖thetaTailFirst u‖ * ‖Real.cos (t * u)‖ ≤ ‖thetaTailFirst u‖ * 1 := by
      gcongr
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * u)
    _ = ‖thetaTailFirst u‖ := by ring
    _ ≤ _ := norm_thetaTailFirst_le_decay hu

private theorem thetaTail_mul_sin_tendsto_zero_right (t : ℝ) :
    Tendsto (fun u : ℝ ↦ thetaTail u * Real.sin (t * u))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcont : ContinuousAt
      (fun u : ℝ ↦ thetaTail u * Real.sin (t * u)) 0 :=
    (hasDerivAt_thetaTail 0).continuousAt.mul (by fun_prop)
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

private theorem thetaTailFirst_mul_cos_tendsto_right (t : ℝ) :
    Tendsto (fun u : ℝ ↦ thetaTailFirst u * Real.cos (t * u))
      (nhdsWithin 0 (Ioi 0)) (nhds (-(1 / 2 : ℝ))) := by
  have hcont : ContinuousAt
      (fun u : ℝ ↦ thetaTailFirst u * Real.cos (t * u)) 0 :=
    (hasDerivAt_thetaTailFirst 0).continuousAt.mul (by fun_prop)
  simpa [thetaTailFirst_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem integral_thetaTailFirst_mul_sin (t : ℝ) :
    (∫ u : ℝ in Ioi 0, thetaTailFirst u * Real.sin (t * u)) =
      -t * ∫ u : ℝ in Ioi 0, thetaTail u * Real.cos (t * u) := by
  have hAcosScaled : IntegrableOn
      (fun u : ℝ ↦ thetaTail u * (t * Real.cos (t * u))) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_mul_cos integrableOn_thetaTail t).mul_const t
    apply h.congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have hAfirstSin : IntegrableOn
      (fun u : ℝ ↦ thetaTailFirst u * Real.sin (t * u)) (Ioi (0 : ℝ)) :=
    integrableOn_mul_sin integrableOn_thetaTailFirst t
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTail) (u' := thetaTailFirst)
    (v := fun u : ℝ ↦ Real.sin (t * u))
    (v' := fun u : ℝ ↦ t * Real.cos (t * u))
    (fun u _hu ↦ hasDerivAt_thetaTail u)
    (fun u _hu ↦ hasDerivAt_sin_mul t u)
    hAcosScaled hAfirstSin
    (thetaTail_mul_sin_tendsto_zero_right t)
    (thetaTail_mul_sin_tendsto_zero t)
  have hleft :
      (∫ u : ℝ in Ioi 0, thetaTail u * (t * Real.cos (t * u))) =
        t * ∫ u : ℝ in Ioi 0, thetaTail u * Real.cos (t * u) := by
    rw [show (fun u : ℝ ↦ thetaTail u * (t * Real.cos (t * u))) =
        fun u : ℝ ↦ t * (thetaTail u * Real.cos (t * u)) by
      funext u
      ring]
    exact integral_const_mul t _
  rw [hleft] at hibp
  linarith

theorem integral_thetaTailSecond_mul_cos (t : ℝ) :
    (∫ u : ℝ in Ioi 0, thetaTailSecond u * Real.cos (t * u)) =
      1 / 2 - t ^ 2 *
        ∫ u : ℝ in Ioi 0, thetaTail u * Real.cos (t * u) := by
  have hAfirstSinScaled : IntegrableOn
      (fun u : ℝ ↦ thetaTailFirst u * (-t * Real.sin (t * u))) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_mul_sin integrableOn_thetaTailFirst t).mul_const (-t)
    apply h.congr
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  have hAsecondCos : IntegrableOn
      (fun u : ℝ ↦ thetaTailSecond u * Real.cos (t * u)) (Ioi (0 : ℝ)) :=
    integrableOn_mul_cos integrableOn_thetaTailSecond t
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := -(1 / 2 : ℝ)) (b' := (0 : ℝ))
    (u := thetaTailFirst) (u' := thetaTailSecond)
    (v := fun u : ℝ ↦ Real.cos (t * u))
    (v' := fun u : ℝ ↦ -t * Real.sin (t * u))
    (fun u _hu ↦ hasDerivAt_thetaTailFirst u)
    (fun u _hu ↦ hasDerivAt_cos_mul t u)
    hAfirstSinScaled hAsecondCos
    (thetaTailFirst_mul_cos_tendsto_right t)
    (thetaTailFirst_mul_cos_tendsto_zero t)
  have hleft :
      (∫ u : ℝ in Ioi 0, thetaTailFirst u * (-t * Real.sin (t * u))) =
        -t * ∫ u : ℝ in Ioi 0, thetaTailFirst u * Real.sin (t * u) := by
    rw [show (fun u : ℝ ↦ thetaTailFirst u * (-t * Real.sin (t * u))) =
        fun u : ℝ ↦ -t * (thetaTailFirst u * Real.sin (t * u)) by
      funext u
      ring]
    exact integral_const_mul (-t) _
  rw [hleft, integral_thetaTailFirst_mul_sin] at hibp
  nlinarith

theorem integrableOn_completedNativeXiCosineKernel :
    IntegrableOn completedNativeXiCosineKernel (Ioi (0 : ℝ)) := by
  have hdiff : IntegrableOn
      (fun u : ℝ ↦ thetaTailSecond u - (1 / 4 : ℝ) * thetaTail u)
      (Ioi (0 : ℝ)) :=
    integrableOn_thetaTailSecond.sub (integrableOn_thetaTail.const_mul (1 / 4 : ℝ))
  apply hdiff.congr
  exact Filter.Eventually.of_forall (fun u ↦ thetaTailSecond_sub_quarter u)

/-- The concrete Xi kernel has a uniform exponential envelope on the positive
half-line.  The existential form deliberately hides the auxiliary theta-mode
constants; downstream moment arguments only need one fixed nonnegative
constant and the decay rate `3 / 2`. -/
theorem exists_completedNativeXiCosineKernel_exp_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : ℝ}, 0 ≤ u →
      ‖completedNativeXiCosineKernel u‖ ≤
        C * Real.exp (-(3 / 2 : ℝ) * u) := by
  let C : ℝ :=
    2 * ∑' n : ℕ, thetaSecondDecayCoefficient n +
      (1 / 4 : ℝ) * (2 * ∑' n : ℕ, thetaZeroDecayCoefficient n)
  have hsecondNonneg :
      0 ≤ ∑' n : ℕ, thetaSecondDecayCoefficient n :=
    tsum_nonneg thetaSecondDecayCoefficient_nonneg
  have hzeroNonneg :
      0 ≤ ∑' n : ℕ, thetaZeroDecayCoefficient n :=
    tsum_nonneg thetaZeroDecayCoefficient_nonneg
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u hu
  have hsecond := norm_thetaTailSecond_le_decay hu
  have hzero := norm_thetaTail_le_decay hu
  rw [← thetaTailSecond_sub_quarter u]
  calc
    ‖thetaTailSecond u - (1 / 4 : ℝ) * thetaTail u‖ ≤
        ‖thetaTailSecond u‖ + ‖(1 / 4 : ℝ) * thetaTail u‖ :=
      norm_sub_le _ _
    _ = ‖thetaTailSecond u‖ +
        (1 / 4 : ℝ) * ‖thetaTail u‖ := by
      rw [norm_mul]
      norm_num
    _ ≤
        (2 * ∑' n : ℕ, thetaSecondDecayCoefficient n) *
            Real.exp (-(3 / 2 : ℝ) * u) +
          (1 / 4 : ℝ) *
            ((2 * ∑' n : ℕ, thetaZeroDecayCoefficient n) *
              Real.exp (-(3 / 2 : ℝ) * u)) := by
      exact add_le_add hsecond (mul_le_mul_of_nonneg_left hzero (by norm_num))
    _ = C * Real.exp (-(3 / 2 : ℝ) * u) := by
      dsimp [C]
      ring

theorem integral_completedNativeXiCosineKernel_mul_cos (t : ℝ) :
    (∫ u : ℝ in Ioi 0,
        completedNativeXiCosineKernel u * Real.cos (t * u)) =
      1 / 2 - (t ^ 2 + 1 / 4) *
        ∫ u : ℝ in Ioi 0, thetaTail u * Real.cos (t * u) := by
  have hAsecondCos : IntegrableOn
      (fun u : ℝ ↦ thetaTailSecond u * Real.cos (t * u)) (Ioi (0 : ℝ)) :=
    integrableOn_mul_cos integrableOn_thetaTailSecond t
  have hAcos : IntegrableOn
      (fun u : ℝ ↦ thetaTail u * Real.cos (t * u)) (Ioi (0 : ℝ)) :=
    integrableOn_mul_cos integrableOn_thetaTail t
  have hquarterAcos : IntegrableOn
      (fun u : ℝ ↦ (1 / 4 : ℝ) *
        (thetaTail u * Real.cos (t * u))) (Ioi (0 : ℝ)) :=
    hAcos.const_mul (1 / 4 : ℝ)
  calc
    (∫ u : ℝ in Ioi 0,
        completedNativeXiCosineKernel u * Real.cos (t * u)) =
      ∫ u : ℝ in Ioi 0,
        thetaTailSecond u * Real.cos (t * u) -
          (1 / 4 : ℝ) * (thetaTail u * Real.cos (t * u)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [← thetaTailSecond_sub_quarter u]
      ring
    _ = (∫ u : ℝ in Ioi 0, thetaTailSecond u * Real.cos (t * u)) -
        ∫ u : ℝ in Ioi 0,
          (1 / 4 : ℝ) * (thetaTail u * Real.cos (t * u)) := by
      exact integral_sub hAsecondCos hquarterAcos
    _ = 1 / 2 - (t ^ 2 + 1 / 4) *
        ∫ u : ℝ in Ioi 0, thetaTail u * Real.cos (t * u) := by
      rw [integral_thetaTailSecond_mul_cos, integral_const_mul]
      ring

/-- The completed native characteristic is the half-line cosine transform
of the explicit strictly positive Jacobi--theta kernel. -/
theorem completedNative_eq_xiCosineKernel (t : ℝ) :
    completedNativeOperatorCharacteristic (t : ℂ) =
      ((∫ u : ℝ in Ioi 0,
        completedNativeXiCosineKernel u * Real.cos (t * u) : ℝ) : ℂ) := by
  rw [completedNative_eq_thetaTail_cosine,
    integral_completedNativeXiCosineKernel_mul_cos]
  have hcomm :
      (∫ u : ℝ in Ioi 0, Real.cos (t * u) * thetaTail u) =
        ∫ u : ℝ in Ioi 0, thetaTail u * Real.cos (t * u) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u ↦ by ring)
  rw [hcomm]

end

end XiThetaCosine

end CarrySelfAdjointOperator

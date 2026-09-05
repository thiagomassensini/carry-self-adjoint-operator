import CarrySelfAdjointOperator.ObservableJetQuotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# C3 trace observability under the material logarithmic generator

The three nodal entries are the variations at material indices 2, 3, 4.
The variation at index 1 is zero. This is a finite causal calculation, not
a variation of the completed canonical analytic family with its tail fixed.
-/

namespace CarrySelfAdjointOperator.C3TraceDynamics

set_option autoImplicit false

section Algebra
variable {K : Type*} [CommRing K]

def gradient (x : Fin 3 → K) : Fin 3 → K :=
  ![x 0, x 1 - x 0, x 2 - x 1]

def recover (g : Fin 3 → K) : Fin 3 → K :=
  ![g 0, g 0 + g 1, g 0 + g 1 + g 2]

theorem recover_gradient (x : Fin 3 → K) : recover (gradient x) = x := by
  funext i
  fin_cases i <;> simp [recover, gradient] <;> ring

theorem gradient_recover (g : Fin 3 → K) : gradient (recover g) = g := by
  funext i
  fin_cases i <;> simp [recover, gradient] <;> ring

def trace (g : Fin 3 → K) : K := g 2 - g 1

def nodalTrace (x : Fin 3 → K) : K := x 0 - 2 * x 1 + x 2

theorem trace_gradient (x : Fin 3 → K) : trace (gradient x) = nodalTrace x := by
  simp [trace, gradient, nodalTrace]
  ring

def nodalClock (a b c : K) (x : Fin 3 → K) : Fin 3 → K :=
  ![a * x 0, b * x 1, c * x 2]

/-- The transported clock is triangular in gradient coordinates. -/
def gradientClock (a b c : K) (g : Fin 3 → K) : Fin 3 → K :=
  ![a * g 0, (b - a) * g 0 + b * g 1,
    (c - b) * (g 0 + g 1) + c * g 2]

theorem clock_intertwines (a b c : K) (g : Fin 3 → K) :
    gradient (nodalClock a b c (recover g)) = gradientClock a b c g := by
  funext i
  fin_cases i <;> simp [gradient, nodalClock, recover, gradientClock] <;> ring

/-- The pulse hidden from the value has its log channel forced by the clock. -/
theorem initialPulse_trace (u : K) : trace ![u, 0, 0] = 0 := by
  simp [trace]

theorem initialPulse_logTrace (a b c u : K) :
    trace (gradientClock a b c ![u, 0, 0]) = (a - 2 * b + c) * u := by
  simp [trace, gradientClock]
  ring

def observation0 (x : Fin 3 → K) : K := nodalTrace x
def observation1 (a b c : K) (x : Fin 3 → K) : K :=
  a * x 0 - 2 * b * x 1 + c * x 2
def observation2 (a b c : K) (x : Fin 3 → K) : K :=
  a ^ 2 * x 0 - 2 * b ^ 2 * x 1 + c ^ 2 * x 2

theorem observation1_eq_clock (a b c : K) (x : Fin 3 → K) :
    observation1 a b c x = nodalTrace (nodalClock a b c x) := by
  simp [observation1, nodalTrace, nodalClock]
  ring

theorem observation2_eq_clock (a b c : K) (x : Fin 3 → K) :
    observation2 a b c x = nodalTrace (nodalClock a b c (nodalClock a b c x)) := by
  simp [observation2, nodalTrace, nodalClock]
  ring

/-- Exact inverse identities: no determinant tolerance or fitted parameters. -/
theorem recover_first_from_observations (a b c : K) (x : Fin 3 → K) :
    observation2 a b c x - (b + c) * observation1 a b c x +
      b * c * observation0 x = (a - b) * (a - c) * x 0 := by
  unfold observation2 observation1 observation0 nodalTrace
  ring

theorem recover_middle_from_observations (a b c : K) (x : Fin 3 → K) :
    observation2 a b c x - (a + c) * observation1 a b c x +
      a * c * observation0 x = -2 * (b - a) * (b - c) * x 1 := by
  unfold observation2 observation1 observation0 nodalTrace
  ring

theorem recover_last_from_observations (a b c : K) (x : Fin 3 → K) :
    observation2 a b c x - (a + b) * observation1 a b c x +
      a * b * observation0 x = (c - a) * (c - b) * x 2 := by
  unfold observation2 observation1 observation0 nodalTrace
  ring

end Algebra

theorem three_observations_separate
    (a b c : ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin 3 → ℝ)
    (h0 : observation0 x = 0) (h1 : observation1 a b c x = 0)
    (h2 : observation2 a b c x = 0) : x = 0 := by
  have hx := recover_first_from_observations a b c x
  have hy := recover_middle_from_observations a b c x
  have hz := recover_last_from_observations a b c x
  rw [h0, h1, h2] at hx hy hz
  have hx0 : x 0 = 0 := (mul_eq_zero.mp (by simpa using hx.symm)).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac))
  have hx1 : x 1 = 0 := (mul_eq_zero.mp (by simpa using hy.symm)).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab.symm))
      (sub_ne_zero.mpr hbc))
  have hx2 : x 2 = 0 := (mul_eq_zero.mp (by simpa using hz.symm)).resolve_left
    (mul_ne_zero (sub_ne_zero.mpr hac.symm) (sub_ne_zero.mpr hbc.symm))
  funext i
  fin_cases i <;> assumption

theorem native_log_trace_gap_neg : Real.log 2 - 2 * Real.log 3 + Real.log 4 < 0 := by
  have h8 : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h9 : Real.log 9 = Real.log 3 + Real.log 3 := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h89 : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

theorem native_initialPulse_logTrace_ne_zero (u : ℝ) (hu : u ≠ 0) :
    trace (gradientClock (Real.log 2) (Real.log 3) (Real.log 4) ![u, 0, 0]) ≠ 0 := by
  rw [initialPulse_logTrace]
  exact mul_ne_zero (ne_of_lt native_log_trace_gap_neg) hu

/-- The real material clock is fully observable from this one bracket and
its first two log readouts on the three-node block. -/
theorem native_three_observations_separate (x : Fin 3 → ℝ)
    (h0 : observation0 x = 0)
    (h1 : observation1 (Real.log 2) (Real.log 3) (Real.log 4) x = 0)
    (h2 : observation2 (Real.log 2) (Real.log 3) (Real.log 4) x = 0) : x = 0 := by
  apply three_observations_separate (Real.log 2) (Real.log 3) (Real.log 4)
    (ne_of_lt (Real.log_lt_log (by norm_num) (by norm_num)))
    (ne_of_lt (Real.log_lt_log (by norm_num) (by norm_num)))
    (ne_of_lt (Real.log_lt_log (by norm_num) (by norm_num))) x h0 h1 h2

end CarrySelfAdjointOperator.C3TraceDynamics

import CarrySelfAdjointOperator.RealQuadratureDomainTransport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The material phase and its edge connection in the existing real product
metric. A common quarter-turn commutes with lifted real maps. A diagonal
material frequency does NOT commute with taking edges; the exact missing
term is retained here. No equality with the completion connection is assumed. -/
namespace CarrySelfAdjointOperator.RealQuadrature
open scoped InnerProductSpace RealInnerProductSpace
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rotation (theta : ℝ) (x : Space E) : Space E :=
  Real.cos theta • x + Real.sin theta • J x

theorem inner_J_self (x : Space E) : inner ℝ (J x) x = 0 := by
  have h := J_skew x x
  rw [real_inner_comm x (J x)] at h
  rw [real_inner_comm x (J x)]
  linarith

/-- Common phase preserves the COMPLETE polarized metric, not only each norm. -/
theorem rotation_inner (theta : ℝ) (x y : Space E) :
    inner ℝ (rotation theta x) (rotation theta y) = inner ℝ x y := by
  simp only [rotation, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, J_inner]
  rw [J_skew x y]
  calc
    _ = (Real.cos theta ^ 2 + Real.sin theta ^ 2) * inner ℝ x y := by ring
    _ = inner ℝ x y := by rw [Real.cos_sq_add_sin_sq, one_mul]

theorem rotation_norm (theta : ℝ) (x : Space E) : ‖rotation theta x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, rotation_inner]

theorem rotation_J (theta : ℝ) (x : Space E) :
    rotation theta (J x) = J (rotation theta x) := by
  simp only [rotation, map_add, map_smul, J_squared]

/-- U_t(n)=R(-t log n); positive material points are supplied by the source. -/
def materialPhase (t point : ℝ) (x : Space E) : Space E :=
  rotation (-t * Real.log point) x

theorem materialPhase_norm (t point : ℝ) (x : Space E) :
    ‖materialPhase t point x‖ = ‖x‖ := rotation_norm _ _

/-- This is the phase generator at a material frequency, not the height operator. -/
def phaseClock (frequency : ℝ) (x : Space E) : Space E := -frequency • J x

theorem phaseClock_J (frequency : ℝ) (x : Space E) :
    phaseClock frequency (J x) = J (phaseClock frequency x) := by
  simp only [phaseClock, map_smul]

theorem phaseClock_squared (frequency : ℝ) (x : Space E) :
    phaseClock frequency (phaseClock frequency x) = -(frequency ^ 2) • x := by
  simp only [phaseClock, map_smul, J_squared]
  module

/-- Raw material-time powers carry their own sign. A second generator power
cannot be identified with a positive shifted moment without a typed jet
conversion. This statement does not assert strong differentiability. -/
theorem phaseClock_second_head_pairing (frequency : ℝ) (x : Space E) :
    inner ℝ (phaseClock frequency (phaseClock frequency x)) x =
      -(frequency ^ 2) * ‖x‖ ^ 2 := by
  rw [phaseClock_squared, real_inner_smul_left, real_inner_self_eq_norm_sq]

theorem phaseClock_second_head_nonpositive (frequency : ℝ) (x : Space E) :
    inner ℝ (phaseClock frequency (phaseClock frequency x)) x ≤ 0 := by
  rw [phaseClock_second_head_pairing]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)

/-- Exact real edge-commutation identity. The right endpoint has its own
frequency; deleting the second term would change the physical evolution. -/
theorem phaseClock_edge_connection (a b : ℝ) (u v : Space E) :
    phaseClock a u - phaseClock b v =
      phaseClock b (u - v) - (a - b) • J u := by
  simp only [phaseClock, map_sub]
  module

theorem materialLogClock_edge_connection (n : ℕ) (u v : Space E) :
    phaseClock (Real.log ((n + 2 : ℕ) : ℝ)) u -
        phaseClock (Real.log ((n + 1 : ℕ) : ℝ)) v =
      phaseClock (Real.log ((n + 1 : ℕ) : ℝ)) (u - v) -
        (Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) • J u :=
  phaseClock_edge_connection _ _ _ _

/-- Narrow no-go: already material points 2 and 1 exclude the naive common
diagonal clock for this nonzero real sample. -/
theorem materialLogClock_first_edge_not_diagonal :
    let u : Space ℝ := WithLp.toLp 2 (1, 0)
    let v : Space ℝ := WithLp.toLp 2 (0, 0)
    phaseClock (Real.log 2) u - phaseClock (Real.log 1) v ≠
      phaseClock (Real.log 1) (u - v) := by
  dsimp only
  intro h
  have hs := congrArg (fun x : Space ℝ => x.snd) h
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simp [phaseClock, Real.log_one, J] at hs
  linarith

end
end CarrySelfAdjointOperator.RealQuadrature

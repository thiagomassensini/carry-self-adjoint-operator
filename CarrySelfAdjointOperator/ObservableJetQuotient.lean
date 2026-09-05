import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The observable state retained by a readout and its evolution

This is an algebraic construction on a generator-invariant domain. It does
not assert analytic continuation, Hilbert positivity, or self-adjointness.
For an unbounded generator the common invariant domain must be supplied first.
-/

namespace CarrySelfAdjointOperator.ObservableJet

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- Successive readouts Q, QL, QL², ... without choosing a spectral target. -/
def readout (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) : ℕ → X →ₗ[K] Y
  | 0 => Q
  | n + 1 => (readout L Q n).comp L

/-- Directions invisible to every successive readout. -/
def invisible (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) : Submodule K X where
  carrier := {x | ∀ n, readout L Q n x = 0}
  zero_mem' := by intro n; exact map_zero _
  add_mem' := by
    intro x y hx hy n
    rw [map_add, hx n, hy n, add_zero]
  smul_mem' := by
    intro c x hx n
    rw [map_smul, hx n, smul_zero]

theorem mem_invisible_iff (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) (x : X) :
    x ∈ invisible L Q ↔ ∀ n, readout L Q n x = 0 := Iff.rfl

theorem invisible_le_ker (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) :
    invisible L Q ≤ LinearMap.ker Q := by
  intro x hx
  exact hx 0

theorem invisible_invariant (L : X →ₗ[K] X) (Q : X →ₗ[K] Y)
    {x : X} (hx : x ∈ invisible L Q) : L x ∈ invisible L Q := by
  intro n
  exact hx (n + 1)

/-- The largest L-invariant submodule contained in the instantaneous kernel. -/
theorem invariant_submodule_le_invisible
    (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) (N : Submodule K X)
    (hzero : N ≤ LinearMap.ker Q)
    (hstable : ∀ x ∈ N, L x ∈ N) : N ≤ invisible L Q := by
  intro x hx n
  induction n generalizing x with
  | zero => exact hzero hx
  | succ n ih => exact ih (hstable x hx)

/-- A static quotient preserves the evolution precisely when its kernel is stable. -/
theorem invisible_eq_ker_iff (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) :
    invisible L Q = LinearMap.ker Q ↔
      ∀ x, Q x = 0 → Q (L x) = 0 := by
  constructor
  · intro h x hx
    have hmem : x ∈ invisible L Q := by rw [h]; exact hx
    exact invisible_le_ker L Q (invisible_invariant L Q hmem)
  · intro h
    apply le_antisymm (invisible_le_ker L Q)
    exact invariant_submodule_le_invisible L Q (LinearMap.ker Q)
      le_rfl (fun x hx => h x hx)

abbrev State (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) := X ⧸ invisible L Q

def generator (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) :
    State L Q →ₗ[K] State L Q :=
  (invisible L Q).mapQ (invisible L Q) L
    (fun _ hx => invisible_invariant L Q hx)

def observation (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) : State L Q →ₗ[K] Y :=
  (invisible L Q).liftQ Q (invisible_le_ker L Q)

theorem generator_mkQ (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) (x : X) :
    generator L Q ((invisible L Q).mkQ x) = (invisible L Q).mkQ (L x) := rfl

theorem observation_mkQ (L : X →ₗ[K] X) (Q : X →ₗ[K] Y) (x : X) :
    observation L Q ((invisible L Q).mkQ x) = Q x := rfl

end CarrySelfAdjointOperator.ObservableJet

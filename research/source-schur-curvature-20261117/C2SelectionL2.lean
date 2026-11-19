import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite C2 depth-class selection: energy scale versus amplitude scale

These finite inequalities apply to arbitrary subsets (including any class of
primes, composites, or twin-prime legs) after inserting the actual C2 shell
count. The shell count itself is a DISTINCT theorem in the C2 repository.

The norm bound by the square root of shell mass is automatic from
Cauchy--Schwarz / finite Bessel; it is NOT a proof of conditional
equidistribution or of the nonlinear Schur curvature inequality.
-/

namespace C2SelectionL2
open scoped BigOperators
noncomputable section
set_option autoImplicit false

variable {α : Type*}

def normalizedEnergy (s : Finset α) (N : ℕ) (f : α → ℝ) : ℝ :=
  (∑ i ∈ s, (f i)^2) / (N:ℝ)

def normalizedMass (s : Finset α) (N : ℕ) : ℝ :=
  (s.card:ℝ)/(N:ℝ)

theorem finiteShellEnergy_le_card (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) :
    ∑ i ∈ s, (f i)^2 ≤ (s.card:ℝ) := by
  calc
    (∑ i ∈ s, (f i)^2) ≤ ∑ i ∈ s, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := abs_le.mp (hf i hi)
      have hp : 0 ≤ (1-f i)*(1+f i) := by
        apply mul_nonneg <;> linarith [hi'.1, hi'.2]
      nlinarith
    _ = _ := by simp

theorem finiteShellNormalizedEnergy_le_mass
    (s : Finset α) (N : ℕ) (f : α → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) :
    normalizedEnergy s N f ≤ normalizedMass s N := by
  unfold normalizedEnergy normalizedMass
  apply div_le_div_of_nonneg_right (finiteShellEnergy_le_card s f hf)
  exact_mod_cast Nat.zero_le N

theorem finiteShellNormalizedEnergy_le_dyadic
    (s : Finset α) (N j : ℕ) (f : α → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1)
    (hweight : normalizedMass s N ≤ (2:ℝ)^(-(j:ℤ))) :
    normalizedEnergy s N f ≤ (2:ℝ)^(-(j:ℤ)) := by
  exact (finiteShellNormalizedEnergy_le_mass s N f hf).trans hweight

theorem finiteShellAmplitude_le_sqrtMass
    (s : Finset α) (N : ℕ) (f : α → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) :
    Real.sqrt (normalizedEnergy s N f) ≤
      Real.sqrt (normalizedMass s N) := by
  exact Real.sqrt_le_sqrt (finiteShellNormalizedEnergy_le_mass s N f hf)

/-- Given a certified dyadic shell count, its energy is at most 2^(-j);
its amplitude is therefore at most the square root of the weight.
This is the unconditional L2 portion of the proposed route, not a
physical C2-to-completed-Hankel map. -/
theorem finiteShellAmplitude_le_sqrtDyadic
    (s : Finset α) (N j : ℕ) (f : α → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1)
    (hweight : normalizedMass s N ≤ (2:ℝ)^(-(j:ℤ))) :
    Real.sqrt (normalizedEnergy s N f) ≤
      Real.sqrt ((2:ℝ)^(-(j:ℤ))) := by
  exact Real.sqrt_le_sqrt
    (finiteShellNormalizedEnergy_le_dyadic s N j f hf hweight)

/-- Finite Parseval/Cauchy--Schwarz for a selected depth shell. -/
theorem finiteShellCauchySchwarz
    (s : Finset α) (f g : α → ℝ) :
    (∑ i ∈ s, f i * g i)^2 ≤
      (∑ i ∈ s, (f i)^2) * (∑ i ∈ s, (g i)^2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

#print axioms finiteShellAmplitude_le_sqrtDyadic
#print axioms finiteShellCauchySchwarz

end
end C2SelectionL2

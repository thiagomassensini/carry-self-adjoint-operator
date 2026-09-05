import CarrySelfAdjointOperator.C3SeededClockShiftIdentity
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJets

/-!
# Exact phase and factorial transport of the seeded material clock

The material clock powers and the real-height Taylor coefficients have
different shift laws. This module retains the factor (-I)^n/n!, and identifies
the reconstructed slope coefficients with the existing native declaration.
-/

namespace CarrySelfAdjointOperator
namespace C3TraceDynamics

open CPFormal.Analytic.Cp
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- Real-height coefficient convention applied to the reconstructed orbit.
This packages existing material powers; it defines no native moments. -/
def seededClockTaylorCoefficient
    (d a b c : ℝ) (x : SeededC3Data) (n : ℕ) : EuclideanSpace ℂ (Fin 4) :=
  ((-Complex.I) ^ n / (n.factorial : ℂ)) •
    seededRecover ((seededClock d a b c)^[n] x)

/-- The exact coordinate coefficient, with its phase and factorial. -/
theorem seededClockTaylorCoefficient_apply
    (d a b c : ℝ) (x : SeededC3Data) (n : ℕ) (i : Fin 4) :
    seededClockTaylorCoefficient d a b c x n i =
      seededRecover x i *
        (-Complex.I * ((![d,a,b,c] i : ℝ) : ℂ)) ^ n / (n.factorial : ℂ) := by
  simp only [seededClockTaylorCoefficient, PiLp.smul_apply, smul_eq_mul,
    seededRecover_clock_iterate_apply, mul_pow]
  ring

/-- Height Taylor coefficients obey the weighted skew shift law, not the
unweighted material-clock law. The sign is forced by conjugating -I. -/
theorem seededClockTaylorCoefficient_weighted_inner_shift
    (d a b c : ℝ) (x y : SeededC3Data) (p q : ℕ) :
    (q + 1 : ℂ) * inner ℂ (seededClockTaylorCoefficient d a b c x p)
        (seededClockTaylorCoefficient d a b c y (q + 1)) =
      -(p + 1 : ℂ) * inner ℂ (seededClockTaylorCoefficient d a b c x (p + 1))
        (seededClockTaylorCoefficient d a b c y q) := by
  simp only [seededClockTaylorCoefficient, inner_smul_left, inner_smul_right]
  rw [seededClock_inner_shift]
  simp only [map_div₀, map_pow, map_mul, map_add, map_one, map_neg,
    Complex.conj_I, map_natCast, neg_neg,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- The slope coordinates are precisely the previously defined native
Dirichlet Taylor coefficients, on every complete three-edge block. -/
theorem nativeSeededClockTaylorCoefficient_slope_eq
    (m n : ℕ) (i : Fin 3) :
    let τ := seededClockTaylorCoefficient
      (Real.log (3*m+1 : ℕ)) (Real.log (3*m+2 : ℕ))
      (Real.log (3*m+3 : ℕ)) (Real.log (3*m+4 : ℕ))
      (nativeBlockSeededData m (1 / 2 : ℂ)) n
    τ ⟨i.val + 1, by omega⟩ - τ ⟨i.val, by omega⟩ =
      nativeDirichletSlopeTaylorCoefficient n (3*m + i.val) := by
  dsimp only
  rw [seededClockTaylorCoefficient_apply, seededClockTaylorCoefficient_apply,
    seededRecover_nativeBlockSeededData]
  fin_cases i <;>
    simp [nativeDirichletSlopeTaylorCoefficient, nativeCriticalDirichletAmplitude,
      positiveDirichletValue_eq_natDirichletTerm, Nat.add_assoc]

end
end C3TraceDynamics
end CarrySelfAdjointOperator

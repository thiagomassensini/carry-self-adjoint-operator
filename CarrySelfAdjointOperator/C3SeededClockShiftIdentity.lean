import CarrySelfAdjointOperator.C3DynamicCompletedGreenForm
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Shift identity in the reconstructed, seeded C3 clock geometry

The clock is the existing affine gradient clock, with its incoming seed
evolved by its own real logarithmic frequency. Reconstruction gives the four
nodal values. Their ordinary Hilbert pairing pulls back to a positive form on
the full seed/gradient ledger, including all cross terms.

Material clock powers satisfy the Hankel shift identity in this form. These
powers are not renamed as the normalized native moment jets.
-/

namespace CarrySelfAdjointOperator
namespace C3TraceDynamics

open CPFormal.Analytic.Cp
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-- The retained incoming value and the three existing gradient coordinates. -/
abbrev SeededC3Data := ℂ × (Fin 3 → ℂ)

/-- Recover all four nodal values from the same seed and gradient ledger. -/
def seededRecover (x : SeededC3Data) : EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 ![x.1, x.1 + x.2 0, x.1 + x.2 0 + x.2 1,
    x.1 + x.2 0 + x.2 1 + x.2 2]

/-- Bundle the existing affine clock with the evolution of its seed. -/
def seededClock (d a b c : ℝ) (x : SeededC3Data) : SeededC3Data :=
  ((d : ℂ) * x.1,
    gradientClock (a : ℂ) (b : ℂ) (c : ℂ) x.2 +
      x.1 • ![(a : ℂ) - d, (b : ℂ) - a, (c : ℂ) - b])

/-- Reconstruction is faithful on the full seed/gradient ledger. -/
theorem seededRecover_injective : Function.Injective seededRecover := by
  intro x y h
  have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 0) h
  have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 1) h
  have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 2) h
  have h3 := congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 3) h
  simp [seededRecover] at h0 h1 h2 h3
  apply Prod.ext h0
  funext i
  fin_cases i
  · change x.2 0 = y.2 0
    linear_combination h1 - h0
  · change x.2 1 = y.2 1
    linear_combination h2 - h1
  · change x.2 2 = y.2 2
    linear_combination h3 - h2

/-- The existing affine gradient clock becomes multiplication by the four
real material frequencies after full reconstruction. -/
theorem seededRecover_clock_apply
    (d a b c : ℝ) (x : SeededC3Data) (i : Fin 4) :
    seededRecover (seededClock d a b c x) i =
      ((![d,a,b,c] i : ℝ) : ℂ) * seededRecover x i := by
  fin_cases i <;> simp [seededRecover, seededClock, gradientClock] <;> ring

/-- Exact material powers, at every order, with the same incoming seed. -/
theorem seededRecover_clock_iterate_apply
    (d a b c : ℝ) (x : SeededC3Data) (n : ℕ) (i : Fin 4) :
    seededRecover ((seededClock d a b c)^[n] x) i =
      ((![d,a,b,c] i : ℝ) : ℂ) ^ n * seededRecover x i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', seededRecover_clock_apply, ih, pow_succ]
      ring

/-- Polarization of the reconstructed material orbit, including arbitrary
crossed initial states. The frequency enters only through the total order. -/
theorem inner_seededRecover_clock_iterate
    (d a b c : ℝ) (x y : SeededC3Data) (p q : ℕ) :
    inner ℂ (seededRecover ((seededClock d a b c)^[p] x))
      (seededRecover ((seededClock d a b c)^[q] y)) =
        ∑ i : Fin 4, (starRingEnd ℂ) (seededRecover x i) * seededRecover y i *
          ((![d,a,b,c] i : ℝ) : ℂ) ^ (p + q) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [seededRecover_clock_iterate_apply, seededRecover_clock_iterate_apply]
  simp only [RCLike.inner_apply, map_mul, map_pow, Complex.conj_ofReal, pow_add]
  ring

/-- The requested shift identity holds for the material clock powers in the
form induced by the complete nodal reconstruction. -/
theorem seededClock_inner_shift
    (d a b c : ℝ) (x y : SeededC3Data) (p q : ℕ) :
    inner ℂ (seededRecover ((seededClock d a b c)^[p] x))
        (seededRecover ((seededClock d a b c)^[q + 1] y)) =
      inner ℂ (seededRecover ((seededClock d a b c)^[p + 1] x))
        (seededRecover ((seededClock d a b c)^[q] y)) := by
  rw [inner_seededRecover_clock_iterate, inner_seededRecover_clock_iterate]
  rw [show p + (q + 1) = (p + 1) + q by omega]

/-- The same canonical native C3 seed and gradients already used by the
completed trace dynamics. -/
def nativeBlockSeededData (m : ℕ) (s : ℂ) : SeededC3Data :=
  (positiveDirichletValue s (3*m), nativeC3BlockGradient m s)

/-- No native coordinate is lost: the reconstruction is the original four
values at material indices 3m+1 through 3m+4. -/
theorem seededRecover_nativeBlockSeededData (m : ℕ) (s : ℂ) :
    seededRecover (nativeBlockSeededData m s) =
      WithLp.toLp 2 ![positiveDirichletValue s (3*m),
        positiveDirichletValue s (3*m+1), positiveDirichletValue s (3*m+2),
        positiveDirichletValue s (3*m+3)] := by
  ext i
  fin_cases i <;>
    simp [seededRecover, nativeBlockSeededData, nativeC3BlockGradient,
      positiveDirichletGradient, positiveDirichletValue_eq_natDirichletTerm,
      Nat.add_assoc]

/-- Its gradient component is exactly the previously proved dynamic log jet. -/
theorem seededClock_nativeBlockSeededData_snd (m : ℕ) (s : ℂ) :
    (seededClock (Real.log (3*m+1 : ℕ)) (Real.log (3*m+2 : ℕ))
      (Real.log (3*m+3 : ℕ)) (Real.log (3*m+4 : ℕ))
      (nativeBlockSeededData m s)).2 = nativeC3BlockDynamicLogJet m s := rfl

/-- The incoming value evolves into its actual native logarithmic value. -/
theorem seededClock_nativeBlockSeededData_fst (m : ℕ) (s : ℂ) :
    (seededClock (Real.log (3*m+1 : ℕ)) (Real.log (3*m+2 : ℕ))
      (Real.log (3*m+3 : ℕ)) (Real.log (3*m+4 : ℕ))
      (nativeBlockSeededData m s)).1 = positiveLogDirichletValue s (3*m) := by
  simp [seededClock, nativeBlockSeededData, positiveLogDirichletValue,
    positiveDirichletValue_eq_natDirichletTerm]

/-- Unconditional native material-clock specialization, at every complete
three-edge block and every pair of orders. -/
theorem nativeSeededC3Clock_inner_shift (m : ℕ) (s : ℂ) (p q : ℕ) :
    let L := seededClock (Real.log (3*m+1 : ℕ)) (Real.log (3*m+2 : ℕ))
      (Real.log (3*m+3 : ℕ)) (Real.log (3*m+4 : ℕ))
    let x := nativeBlockSeededData m s
    inner ℂ (seededRecover (L^[p] x)) (seededRecover (L^[q + 1] x)) =
      inner ℂ (seededRecover (L^[p + 1] x)) (seededRecover (L^[q] x)) :=
  seededClock_inner_shift _ _ _ _ _ _ p q

/-- Calibration is still necessary: the first native block retains the
unit seed, so its reconstructed nodal energy is at least one. -/
theorem nativeBlockSeededData_zero_energy_ge_one (s : ℂ) :
    (1 : ℝ) ≤ ‖seededRecover (nativeBlockSeededData 0 s)‖ ^ 2 := by
  have hcoord : seededRecover (nativeBlockSeededData 0 s) 0 = 1 := by
    simp [seededRecover, nativeBlockSeededData, positiveDirichletValue_eq_natDirichletTerm,
      natDirichletTerm, dirichletTerm]
  have hnorm : ‖seededRecover (nativeBlockSeededData 0 s) 0‖ ≤
      ‖seededRecover (nativeBlockSeededData 0 s)‖ := by
    exact PiLp.norm_apply_le _ _
  rw [hcoord] at hnorm
  norm_num at hnorm
  nlinarith [sq_nonneg (‖seededRecover (nativeBlockSeededData 0 s)‖ - 1)]

/-- The proved shift identity does not identify this nodal energy with the
native logarithmic moment normalization. -/
theorem nativeBlockSeededData_zero_energy_ne_nativeMoment (s : ℂ) :
    ‖seededRecover (nativeBlockSeededData 0 s)‖ ^ 2 ≠
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have h := nativeBlockSeededData_zero_energy_ge_one s
  have hn := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

end
end C3TraceDynamics
end CarrySelfAdjointOperator

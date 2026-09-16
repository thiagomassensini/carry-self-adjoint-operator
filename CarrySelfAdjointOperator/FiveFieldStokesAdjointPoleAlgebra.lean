import Mathlib

/-!
An exact finite-dimensional algebraic fragment of the rational-adjoint
obstruction recorded in the Stokes notes.  No connection or physical residue
is introduced here: the only input is square-zero nilpotence of a residue.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

abbrev TwoByTwo := Matrix (Fin 2) (Fin 2) ℂ

def matrixCommutator (A B : TwoByTwo) : TwoByTwo := A * B - B * A

theorem matrixCommutator_smul_right
    (A X : TwoByTwo) (r : ℂ) :
    matrixCommutator A (r • X) = r • matrixCommutator A X := by
  simp [matrixCommutator, smul_sub]

theorem matrixCommutator_two_eq_neg_sandwich
    (A X : TwoByTwo) (hA : A * A = 0) :
    matrixCommutator A (matrixCommutator A X) =
      -(A * X * A) - (A * X * A) := by
  calc
    matrixCommutator A (matrixCommutator A X) =
        (A * A) * X - (A * X * A) - (A * X * A) + X * (A * A) := by
      simp [matrixCommutator]
      noncomm_ring
    _ = -(A * X * A) - (A * X * A) := by
      rw [hA]
      simp

theorem matrixCommutator_three_nilpotent
    (A B : TwoByTwo) (hA : A * A = 0) :
    matrixCommutator A (matrixCommutator A (matrixCommutator A B)) = 0 := by
  have hsand : A * matrixCommutator A B * A = 0 := by
    calc
      A * matrixCommutator A B * A =
          (A * A) * B * A - A * B * (A * A) := by
        simp [matrixCommutator]
        noncomm_ring
      _ = 0 := by rw [hA]; simp
  rw [matrixCommutator_two_eq_neg_sandwich A (matrixCommutator A B) hA]
  simp [hsand]

theorem matrixCommutator_nonzero_eigenvector_vanishes
    (A B : TwoByTwo) (hA : A * A = 0)
    (r : ℂ) (hr : r ≠ 0)
    (heigen : matrixCommutator A B = r • B) :
    B = 0 := by
  have hdouble :
      matrixCommutator A (matrixCommutator A B) =
        r • matrixCommutator A B := by
    calc
      matrixCommutator A (matrixCommutator A B) =
          matrixCommutator A (r • B) := by rw [heigen]
      _ = r • matrixCommutator A B :=
        matrixCommutator_smul_right A B r
  have htriple :
      matrixCommutator A (matrixCommutator A (matrixCommutator A B)) =
        r • (r • (r • B)) := by
    calc
      matrixCommutator A (matrixCommutator A (matrixCommutator A B)) =
          matrixCommutator A (r • matrixCommutator A B) := by
            rw [hdouble]
      _ = r • matrixCommutator A (matrixCommutator A B) :=
        matrixCommutator_smul_right A (matrixCommutator A B) r
      _ = r • (r • matrixCommutator A B) := by rw [hdouble]
      _ = r • (r • (r • B)) := by rw [heigen]
  have hzero : r • (r • (r • B)) = 0 := by
    rw [← htriple]
    exact matrixCommutator_three_nilpotent A B hA
  have hzero' : (r * r * r) • B = 0 := by
    simpa [smul_smul, mul_assoc] using hzero
  exact (smul_eq_zero.mp hzero').resolve_left
    (mul_ne_zero (mul_ne_zero hr hr) hr)

end
end NativeCarryFiveFieldCapstone

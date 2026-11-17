import CarrySelfAdjointOperator.NativeHankelPencilCofactor

/-! Division-free Hankel determinant identities for arbitrary moment sequences.
The full Desnanot–Jacobi step is still under development. -/
namespace CarrySelfAdjointOperator

open Matrix

noncomputable section
set_option autoImplicit false

/-- Determinant of a shifted Hankel window of an arbitrary real sequence. -/
def arbitraryHankelWindowDet (m : ℕ → ℝ) (s n : ℕ) : ℝ :=
  (sourceMomentMatrix m s n).det

/-- The first Toda/Desnanot–Jacobi case, verified directly from the `2 × 2`
determinant. This is an unconditional algebraic base case. -/
theorem arbitraryHankelToda_one (m : ℕ → ℝ) (s : ℕ) :
    arbitraryHankelWindowDet m s 1 * arbitraryHankelWindowDet m (s + 2) 1 -
      (arbitraryHankelWindowDet m (s + 1) 1)^2 =
        arbitraryHankelWindowDet m s 2 * arbitraryHankelWindowDet m (s + 2) 0 := by
  simp [arbitraryHankelWindowDet, sourceMomentMatrix, Matrix.det_fin_two]
  ring

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.FiveFieldStokesAdjointPoleAlgebra

/-!
# Concrete decorated local nilpotent orbit

Exact formulas from `MONODROMIA_DECORADA_E_PARES_DARBOUX_LOCAIS.md` and
`native_carry_decorated_monodromy_darboux_lab.py`. This establishes the local
commutator/trace normalization. It does not identify the local orbit form
with a global fused form or prove a physical Jacobian pullback.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open scoped Matrix.Norms.Elementwise

def decoratedNilpotent (η : ℂ) : TwoByTwo :=
  !![-η, 1; -η ^ 2, η]

def decoratedNilpotentTangent (η : ℂ) : TwoByTwo :=
  !![-1, 0; -2 * η, 1]

def decoratedLowerGenerator : TwoByTwo := !![0, 0; 1, 0]

def decoratedLeveltResidue (κ a η : ℂ) : TwoByTwo :=
  (κ * a) • decoratedNilpotent η

def decoratedAmplitudeGenerator (a η : ℂ) : TwoByTwo :=
  (2 * a)⁻¹ • !![1, 0; 2 * η, -1]

theorem decoratedNilpotent_eq_conjugated (η : ℂ) :
    decoratedNilpotent η =
      !![1, 0; η, 1] * !![0, 1; 0, 0] * !![1, 0; -η, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decoratedNilpotent, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem decoratedNilpotent_square_zero (η : ℂ) :
    decoratedNilpotent η * decoratedNilpotent η = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decoratedNilpotent, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The fixed line is exactly the graph of multiplication by `η`. -/
theorem decoratedNilpotent_mulVec_eq_zero_iff (η : ℂ) (v : Fin 2 → ℂ) :
    (decoratedNilpotent η).mulVec v = 0 ↔ v 1 = η * v 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [decoratedNilpotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    linear_combination h0
  · intro h
    ext i
    fin_cases i <;>
      simp [decoratedNilpotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]
    all_goals ring

theorem decoratedLeveltResidue_square_zero (κ a η : ℂ) :
    decoratedLeveltResidue κ a η * decoratedLeveltResidue κ a η = 0 := by
  simp [decoratedLeveltResidue, decoratedNilpotent_square_zero]

theorem decoratedNilpotent_hasDerivAt (η : ℂ) :
    HasDerivAt decoratedNilpotent (decoratedNilpotentTangent η) η := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · convert! (hasDerivAt_id η).neg using 1
  · simpa [decoratedNilpotent, decoratedNilpotentTangent] using hasDerivAt_const η (1 : ℂ)
  · change HasDerivAt (fun z : ℂ => -(z ^ 2)) (-2 * η) η
    convert! ((hasDerivAt_id η).pow 2).neg using 1
    simp
  · convert! hasDerivAt_id η using 1

theorem decoratedLeveltResidue_hasDerivAt_amplitude (κ a η : ℂ) :
    HasDerivAt (fun b => decoratedLeveltResidue κ b η) (κ • decoratedNilpotent η) a := by
  convert! ((hasDerivAt_id a).const_mul κ).smul_const (decoratedNilpotent η) using 1
  simp

theorem decoratedLeveltResidue_hasDerivAt_decoration (κ a η : ℂ) :
    HasDerivAt (decoratedLeveltResidue κ a)
      ((κ * a) • decoratedNilpotentTangent η) η := by
  exact (decoratedNilpotent_hasDerivAt η).const_smul (κ * a)

theorem decoratedAmplitudeGenerator_commutator (κ a η : ℂ) (ha : a ≠ 0) :
    matrixCommutator (decoratedAmplitudeGenerator a η) (decoratedLeveltResidue κ a η) =
      κ • decoratedNilpotent η := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, decoratedAmplitudeGenerator, decoratedLeveltResidue,
      decoratedNilpotent] <;>
    field_simp <;> ring

theorem decoratedLowerGenerator_commutator (κ a η : ℂ) :
    matrixCommutator decoratedLowerGenerator (decoratedLeveltResidue κ a η) =
      (κ * a) • decoratedNilpotentTangent η := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCommutator, decoratedLowerGenerator, decoratedLeveltResidue,
      decoratedNilpotent, decoratedNilpotentTangent]
  all_goals ring

/-- Local Kirillov--Kostant coefficient, with the exact sign in the notes. -/
theorem decoratedLevelt_local_KK_trace (κ a η : ℂ) (ha : a ≠ 0) :
    Matrix.trace (decoratedLeveltResidue κ a η *
      matrixCommutator (decoratedAmplitudeGenerator a η) decoratedLowerGenerator) = -κ := by
  simp [Matrix.trace, Matrix.diag, matrixCommutator, decoratedAmplitudeGenerator,
    decoratedLowerGenerator, decoratedLeveltResidue, decoratedNilpotent,
    Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

/-- The previously proved adjoint-pole obstruction applies to this concrete residue. -/
theorem decoratedLevelt_nonzero_adjoint_eigenvector_vanishes
    (κ a η r : ℂ) (B : TwoByTwo) (hr : r ≠ 0)
    (h : matrixCommutator (decoratedLeveltResidue κ a η) B = r • B) : B = 0 :=
  matrixCommutator_nonzero_eigenvector_vanishes _ B
    (decoratedLeveltResidue_square_zero κ a η) r hr h

end

end NativeCarryFiveFieldCapstone

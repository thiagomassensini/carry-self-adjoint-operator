import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Division-free Green confinement

This module writes the final algebraic implication without dividing by the
completed characteristic.  If a completed scalar characteristic `F`, its
boundary companion `Psi`, and a Hilbert state `f_z` satisfy the polarized
Green/Wronskian identity

`Psi z * conj(F w) - F z * conj(Psi w)
    = (z - conj w) * <f_w, f_z>`,

then every zero with nonzero state is fixed by complex conjugation.  In the
centered height variable, this is exactly the real-axis confinement
statement.  Thus the final theorem needs no logarithmic division and no
multiplicity assumption: the two remaining analytic inputs are the genuine
Green identity and nonvanishing of the state at a zero.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

/-- Division-free scalar Wronskian of a characteristic and its boundary
companion. -/
def completedGreenWronskian
    (F Psi : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Psi z * (starRingEnd ℂ) (F w) -
    F z * (starRingEnd ℂ) (Psi w)

/-- The exact polarized Green identity required by the final confinement
step. -/
def HasDivisionFreeGreenRepresentation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F Psi : ℂ → ℂ) (state : ℂ → H) : Prop :=
  ∀ z w : ℂ,
    completedGreenWronskian F Psi z w =
      (z - (starRingEnd ℂ) w) * inner ℂ (state w) (state z)

/-- A zero carrying a nonzero Green state is forced onto the real axis of the
centered height variable. This is the division-free final implication. -/
theorem zero_fixedByConjugation_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F Psi : ℂ → ℂ} {state : ℂ → H} {z : ℂ}
    (hgreen : HasDivisionFreeGreenRepresentation F Psi state)
    (hzero : F z = 0) (hstate : state z ≠ 0) :
    z = (starRingEnd ℂ) z := by
  have hwronskian : completedGreenWronskian F Psi z z = 0 := by
    simp [completedGreenWronskian, hzero]
  have hproduct :
      (z - (starRingEnd ℂ) z) * inner ℂ (state z) (state z) = 0 := by
    rw [← hgreen z z, hwronskian]
  have hinner : inner ℂ (state z) (state z) ≠ 0 :=
    inner_self_ne_zero.mpr hstate
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hinner)

/-- Equivalent coordinate statement: the centered height has zero imaginary
part. -/
theorem zero_im_eq_zero_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F Psi : ℂ → ℂ} {state : ℂ → H} {z : ℂ}
    (hgreen : HasDivisionFreeGreenRepresentation F Psi state)
    (hzero : F z = 0) (hstate : state z ≠ 0) :
    z.im = 0 := by
  have hfixed :=
    zero_fixedByConjugation_of_divisionFreeGreen hgreen hzero hstate
  have him := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at him
  linarith

end

end CarrySelfAdjointOperator

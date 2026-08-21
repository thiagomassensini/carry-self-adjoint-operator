import CarrySelfAdjointOperator.CompletedOperatorCharacteristic
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

/-- Minimal off-axis diagonal form of the Green representation.  This is the
natural interface for gamma fields that are initially constructed only for
nonreal spectral parameters. -/
def HasOffAxisDiagonalGreenRepresentation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F Psi : ℂ → ℂ) (state : ℂ → H) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 →
    completedGreenWronskian F Psi z z =
      (z - (starRingEnd ℂ) z) * inner ℂ (state z) (state z)

/-- Scalar-energy version of the off-axis diagonal identity.  It is tailored
to the existing realified carry gamma field: its real squared norm can be
inserted into the complex Wronskian without manufacturing a complex scalar
action on the realification. -/
def HasOffAxisDiagonalGreenEnergy
    (F Psi : ℂ → ℂ) (energy : ℂ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 →
    completedGreenWronskian F Psi z z =
      (z - (starRingEnd ℂ) z) * (energy z : ℂ)

/-- A full polarized Green representation supplies its off-axis diagonal
restriction. -/
theorem HasDivisionFreeGreenRepresentation.toOffAxisDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F Psi : ℂ → ℂ} {state : ℂ → H}
    (hgreen : HasDivisionFreeGreenRepresentation F Psi state) :
    HasOffAxisDiagonalGreenRepresentation F Psi state := by
  intro z _hz
  exact hgreen z z

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

/-- The same confinement conclusion needs the Green identity only on the
off-axis diagonal.  Assuming the selected zero were nonreal activates that
identity and yields the contradiction. -/
theorem zero_im_eq_zero_of_offAxisDiagonalGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F Psi : ℂ → ℂ} {state : ℂ → H} {z : ℂ}
    (hgreen : HasOffAxisDiagonalGreenRepresentation F Psi state)
    (hzero : F z = 0) (hstate : state z ≠ 0) :
    z.im = 0 := by
  by_contra him
  have hwronskian : completedGreenWronskian F Psi z z = 0 := by
    simp [completedGreenWronskian, hzero]
  have hproduct :
      (z - (starRingEnd ℂ) z) * inner ℂ (state z) (state z) = 0 := by
    rw [← hgreen z him, hwronskian]
  have hinner : inner ℂ (state z) (state z) ≠ 0 :=
    inner_self_ne_zero.mpr hstate
  have hfixed : z = (starRingEnd ℂ) z :=
    sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hinner)
  have hcoord := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at hcoord
  exact him (by linarith [hcoord])

/-- Off-axis confinement from a nonzero real Green energy. -/
theorem zero_im_eq_zero_of_offAxisDiagonalGreenEnergy
    {F Psi : ℂ → ℂ} {energy : ℂ → ℝ} {z : ℂ}
    (hgreen : HasOffAxisDiagonalGreenEnergy F Psi energy)
    (hzero : F z = 0) (henergy : energy z ≠ 0) :
    z.im = 0 := by
  by_contra him
  have hwronskian : completedGreenWronskian F Psi z z = 0 := by
    simp [completedGreenWronskian, hzero]
  have hproduct :
      (z - (starRingEnd ℂ) z) * (energy z : ℂ) = 0 := by
    rw [← hgreen z him, hwronskian]
  have henergyComplex : (energy z : ℂ) ≠ 0 := by
    exact_mod_cast henergy
  have hfixed : z = (starRingEnd ℂ) z :=
    sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right henergyComplex)
  have hcoord := congrArg Complex.im hfixed
  simp only [Complex.conj_im] at hcoord
  exact him (by linarith [hcoord])

/-- Natural nonreal-domain form: the energy need only be nonzero under the
same off-axis assumption that activates the Green identity. -/
theorem zero_im_eq_zero_of_offAxisDiagonalGreenEnergy_of_offAxis_nonzero
    {F Psi : ℂ → ℂ} {energy : ℂ → ℝ} {z : ℂ}
    (hgreen : HasOffAxisDiagonalGreenEnergy F Psi energy)
    (hzero : F z = 0)
    (henergy : z.im ≠ 0 → energy z ≠ 0) :
    z.im = 0 := by
  by_contra him
  exact him (zero_im_eq_zero_of_offAxisDiagonalGreenEnergy
    hgreen hzero (henergy him))

/-- Completed Green representation specialized to the actual scalar used by
the native Jacobi/height operator. -/
def HasCompletedNativeOperatorGreenRepresentation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Psi : ℂ → ℂ) (state : ℂ → H) : Prop :=
  HasDivisionFreeGreenRepresentation
    completedNativeOperatorCharacteristic Psi state

/-- Minimal gamma-field interface for the actual completed native operator:
only the nonreal diagonal is required. -/
def HasCompletedNativeOperatorOffAxisDiagonalGreenRepresentation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Psi : ℂ → ℂ) (state : ℂ → H) : Prop :=
  HasOffAxisDiagonalGreenRepresentation
    completedNativeOperatorCharacteristic Psi state

/-- Real-energy diagonal Green interface for the actual completed native
operator characteristic. -/
def HasCompletedNativeOperatorOffAxisDiagonalGreenEnergy
    (Psi : ℂ → ℂ) (energy : ℂ → ℝ) : Prop :=
  HasOffAxisDiagonalGreenEnergy
    completedNativeOperatorCharacteristic Psi energy

/-- Canonical boundary companion of the completed characteristic, with the
sign convention `Psi = -F'` used by the Green Wronskian. -/
def completedNativeOperatorBoundaryCompanion (z : ℂ) : ℂ :=
  -deriv completedNativeOperatorCharacteristic z

/-- Final real-energy interface with no freely chosen scalar trace: the
boundary companion is fixed to the derivative of the actual completed native
operator characteristic. -/
def HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenEnergy
    (energy : ℂ → ℝ) : Prop :=
  HasCompletedNativeOperatorOffAxisDiagonalGreenEnergy
    completedNativeOperatorBoundaryCompanion energy

/-- Canonical real gamma-state interface: its squared norm is the diagonal
Green energy.  This matches the existing `ℝ²` realification exactly. -/
def HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (state : ℂ → H) : Prop :=
  HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenEnergy
    (fun z ↦ ‖state z‖ ^ 2)

/-- Final closure theorem specialized to the native completed operator
characteristic. Its only hypotheses are now the concrete completed Green
identity and nonvanishing of the associated state at the selected zero. -/
theorem completedNativeOperator_zero_im_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Psi : ℂ → ℂ} {state : ℂ → H} {z : ℂ}
    (hgreen : HasCompletedNativeOperatorGreenRepresentation Psi state)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (hstate : state z ≠ 0) :
    z.im = 0 :=
  zero_im_eq_zero_of_divisionFreeGreen hgreen hzero hstate

/-- Specialized closure theorem using only the off-axis diagonal identity
available from a nonreal-parameter gamma construction. -/
theorem completedNativeOperator_zero_im_eq_zero_of_offAxisDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Psi : ℂ → ℂ} {state : ℂ → H} {z : ℂ}
    (hgreen :
      HasCompletedNativeOperatorOffAxisDiagonalGreenRepresentation Psi state)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (hstate : state z ≠ 0) :
    z.im = 0 :=
  zero_im_eq_zero_of_offAxisDiagonalGreen hgreen hzero hstate

/-- Specialized closure theorem consuming only a nonzero real gamma energy
at the selected zero. -/
theorem completedNativeOperator_zero_im_eq_zero_of_offAxisDiagonalEnergy
    {Psi : ℂ → ℂ} {energy : ℂ → ℝ} {z : ℂ}
    (hgreen :
      HasCompletedNativeOperatorOffAxisDiagonalGreenEnergy Psi energy)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (henergy : energy z ≠ 0) :
    z.im = 0 :=
  zero_im_eq_zero_of_offAxisDiagonalGreenEnergy hgreen hzero henergy

/-- Canonical-companion specialization of the real-energy closure theorem. -/
theorem completedNativeOperator_zero_im_eq_zero_of_canonicalGreenEnergy
    {energy : ℂ → ℝ} {z : ℂ}
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenEnergy energy)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (henergy : energy z ≠ 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_offAxisDiagonalEnergy
    hgreen hzero henergy

/-- Canonical real-state specialization. -/
theorem completedNativeOperator_zero_im_eq_zero_of_canonicalGreenState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {state : ℂ → H} {z : ℂ}
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState state)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (hstate : state z ≠ 0) :
    z.im = 0 := by
  apply completedNativeOperator_zero_im_eq_zero_of_canonicalGreenEnergy
    hgreen hzero
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hstate)

/-- Canonical real-state closure where state nonvanishing is required only
under the hypothetical off-axis condition. -/
theorem completedNativeOperator_zero_im_eq_zero_of_canonicalGreenState_of_offAxis_nonzero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {state : ℂ → H} {z : ℂ}
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState state)
    (hzero : completedNativeOperatorCharacteristic z = 0)
    (hstate : z.im ≠ 0 → state z ≠ 0) :
    z.im = 0 := by
  by_contra him
  exact him (completedNativeOperator_zero_im_eq_zero_of_canonicalGreenState
    hgreen hzero (hstate him))

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.NativeScalarZetaIdentification
import CarrySelfAdjointOperator.DivisionFreeGreenConfinement
import Mathlib.Tactic

/-!
# Conditional critical-line confinement

This file performs the final coordinate conversion from a zero of
`riemannZeta s` in the open critical strip to a zero of the completed native
operator characteristic in the centered height coordinate.  The abstract
division-free Green theorem then forces that centered height to be real,
which is exactly `re s = 1/2`.

No zero list, target height, logarithmic division, or zero multiplicity is
used.  The only remaining construction hypotheses are the concrete polarized
Green representation of the completed native characteristic and nonvanishing
of its state at the selected zero.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Centered height coordinate inverse to `s = 1/2 + i z`. -/
def centeredHeightParameter (s : ℂ) : ℂ :=
  (s.im : ℂ) + ((1 / 2 : ℝ) - s.re) * Complex.I

/-- The centered-height and spectral-parameter coordinates are exact
inverses. -/
@[simp] theorem operatorHeightParameter_centeredHeightParameter (s : ℂ) :
    operatorHeightParameter (centeredHeightParameter s) = s := by
  apply Complex.ext <;>
    simp [operatorHeightParameter, centeredHeightParameter]

/-- The imaginary part of the centered height is precisely the horizontal
displacement from the critical line. -/
@[simp] theorem centeredHeightParameter_im (s : ℂ) :
    (centeredHeightParameter s).im = (1 / 2 : ℝ) - s.re := by
  simp [centeredHeightParameter]

/-- Final critical-line implication in zeta coordinates.  It states exactly
what remains after all algebraic and analytic identifications: a genuine
completed Green representation plus a nonzero state at the zero force every
open-critical-strip zeta zero onto `re s = 1/2`. -/
theorem riemannZeta_zero_re_eq_half_of_completedNativeOperatorGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Psi : ℂ → ℂ} {state : ℂ → H}
    (hgreen : HasCompletedNativeOperatorGreenRepresentation Psi state)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (hstate : state (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta
      hstrip]
    simp [hzero]
  have him : (centeredHeightParameter s).im = 0 :=
    completedNativeOperator_zero_im_eq_zero
      hgreen hcharacteristic hstate
  rw [centeredHeightParameter_im] at him
  linarith

/-- Stronger interface reduction: the same critical-line conclusion follows
when the completed Green identity is available only on nonreal diagonal
parameters, exactly the natural domain of the existing carry gamma field. -/
theorem riemannZeta_zero_re_eq_half_of_offAxisDiagonalGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Psi : ℂ → ℂ} {state : ℂ → H}
    (hgreen :
      HasCompletedNativeOperatorOffAxisDiagonalGreenRepresentation Psi state)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (hstate : state (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta
      hstrip]
    simp [hzero]
  have him : (centeredHeightParameter s).im = 0 :=
    completedNativeOperator_zero_im_eq_zero_of_offAxisDiagonal
      hgreen hcharacteristic hstate
  rw [centeredHeightParameter_im] at him
  linarith

/-- Critical-line confinement in the interface native to the realified carry
gamma field: a nonzero real diagonal Green energy suffices. -/
theorem riemannZeta_zero_re_eq_half_of_offAxisDiagonalGreenEnergy
    {Psi : ℂ → ℂ} {energy : ℂ → ℝ}
    (hgreen :
      HasCompletedNativeOperatorOffAxisDiagonalGreenEnergy Psi energy)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (henergy : energy (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta
      hstrip]
    simp [hzero]
  have him : (centeredHeightParameter s).im = 0 :=
    completedNativeOperator_zero_im_eq_zero_of_offAxisDiagonalEnergy
      hgreen hcharacteristic henergy
  rw [centeredHeightParameter_im] at him
  linarith

/-- Canonical final interface: the scalar companion is `-F'`, so the only
remaining datum is the real Green energy constructed from the enriched carry
state. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalGreenEnergy
    {energy : ℂ → ℝ}
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenEnergy energy)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (henergy : energy (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta
      hstrip]
    simp [hzero]
  have him : (centeredHeightParameter s).im = 0 :=
    completedNativeOperator_zero_im_eq_zero_of_canonicalGreenEnergy
      hgreen hcharacteristic henergy
  rw [centeredHeightParameter_im] at him
  linarith

/-- Final real-state form aligned with the existing carry gamma field. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalGreenState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {state : ℂ → H}
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState state)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (hstate : state (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta
      hstrip]
    simp [hzero]
  have him : (centeredHeightParameter s).im = 0 :=
    completedNativeOperator_zero_im_eq_zero_of_canonicalGreenState
      hgreen hcharacteristic hstate
  rw [centeredHeightParameter_im] at him
  linarith

/-- Natural gamma-domain form: nonvanishing is needed only if the centered
height is off the real axis. -/
theorem riemannZeta_zero_re_eq_half_of_canonicalGreenState_of_offAxis_nonzero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {state : ℂ → H}
    (hgreen :
      HasCanonicalCompletedNativeOperatorOffAxisDiagonalGreenState state)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : riemannZeta s = 0)
    (hstate :
      (centeredHeightParameter s).im ≠ 0 →
        state (centeredHeightParameter s) ≠ 0) :
    s.re = 1 / 2 := by
  have hstrip :
      operatorHeightParameter (centeredHeightParameter s) ∈
        genuineCriticalStrip := by
    simpa using hs
  have hcharacteristic :
      completedNativeOperatorCharacteristic
          (centeredHeightParameter s) = 0 := by
    rw [completedNativeOperatorCharacteristic_eq_completedRiemannZeta
      hstrip]
    simp [hzero]
  have him : (centeredHeightParameter s).im = 0 :=
    completedNativeOperator_zero_im_eq_zero_of_canonicalGreenState_of_offAxis_nonzero
      hgreen hcharacteristic hstate
  rw [centeredHeightParameter_im] at him
  linarith

end

end CarrySelfAdjointOperator

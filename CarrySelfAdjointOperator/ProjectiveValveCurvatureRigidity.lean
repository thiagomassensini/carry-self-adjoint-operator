import CarrySelfAdjointOperator.ProjectiveValveAlgebra
import Mathlib.Tactic

/-!
# Curvature rigidity for normalized projective-valve germs

The projective valve is canonically normalized at constant coefficient `1`,
but scalarization identities naturally produce germs with arbitrary nonzero
central value.  This file isolates the harmless scalar normalization and proves
that logarithmic curvature determines such a germ up to its central scalar.

This is the form needed when two independently constructed scalar germs are to
be compared by curvature rather than by expanding every Taylor coefficient.
-/

namespace CarrySelfAdjointOperator.ProjectiveValve

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The identity `curvature(A) * A = A'` only needs invertibility of the
constant coefficient; normalization to `1` is unnecessary. -/
theorem projectiveValveCurvature_mul_self_of_constantCoeff_ne_zero
    (A : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0) :
    projectiveValveCurvature A * A = d⁄dX K A := by
  unfold projectiveValveCurvature
  rw [mul_assoc, PowerSeries.inv_mul_cancel A hA0, mul_one]

/-- Canonical scalar normalization of a nonzero formal germ. -/
noncomputable def projectiveValveNormalize (A : PowerSeries K) : PowerSeries K :=
  (constantCoeff A)⁻¹ • A

/-- A germ with nonzero central value normalizes to constant coefficient one. -/
@[simp] theorem projectiveValveNormalize_constantCoeff
    (A : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0) :
    constantCoeff (projectiveValveNormalize A) = 1 := by
  simp [projectiveValveNormalize, hA0]

/-- Scalar normalization preserves the first-order projective ODE. -/
theorem derivative_projectiveValveNormalize
    (A : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0) :
    d⁄dX K (projectiveValveNormalize A) =
      projectiveValveCurvature A * projectiveValveNormalize A := by
  have hA := projectiveValveCurvature_mul_self_of_constantCoeff_ne_zero A hA0
  change A.derivativeFun = projectiveValveCurvature A * A at hA
  unfold projectiveValveNormalize
  rw [PowerSeries.derivativeFun_smul, hA]
  simp only [smul_eq_mul]
  ring

/-- Normalizing a nonzero germ does not change its logarithmic curvature. -/
@[simp] theorem projectiveValveCurvature_normalize
    (A : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0) :
    projectiveValveCurvature (projectiveValveNormalize A) =
      projectiveValveCurvature A := by
  exact projectiveValveCurvature_eq_of_ode
    (projectiveValveCurvature A)
    (projectiveValveNormalize A)
    (projectiveValveNormalize_constantCoeff A hA0)
    (derivative_projectiveValveNormalize A hA0)

/-- The normalized form of any nonzero germ is exactly the canonical valve
mass of its logarithmic curvature. -/
theorem projectiveValveNormalize_eq_mass_curvature
    (A : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0) :
    projectiveValveNormalize A =
      projectiveValveMass (projectiveValveCurvature A) := by
  exact projectiveValveMass_unique
    (projectiveValveCurvature A)
    (projectiveValveNormalize A)
    (projectiveValveNormalize_constantCoeff A hA0)
    (derivative_projectiveValveNormalize A hA0)

/-- Two nonzero germs with the same logarithmic curvature have the same
canonical normalization. -/
theorem projectiveValveNormalize_eq_of_curvature_eq
    (A B : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0)
    (hB0 : constantCoeff B ≠ 0)
    (hcurvature : projectiveValveCurvature A = projectiveValveCurvature B) :
    projectiveValveNormalize A = projectiveValveNormalize B := by
  rw [projectiveValveNormalize_eq_mass_curvature A hA0,
    projectiveValveNormalize_eq_mass_curvature B hB0,
    hcurvature]

/-- Curvature plus the central scalar determines a nonzero formal germ
uniquely.  This is the scalarization-ready rigidity statement. -/
theorem eq_of_constantCoeff_eq_of_projectiveValveCurvature_eq
    (A B : PowerSeries K)
    (hA0 : constantCoeff A ≠ 0)
    (hB0 : constantCoeff B ≠ 0)
    (hconstant : constantCoeff A = constantCoeff B)
    (hcurvature : projectiveValveCurvature A = projectiveValveCurvature B) :
    A = B := by
  have hnormalized :=
    projectiveValveNormalize_eq_of_curvature_eq A B hA0 hB0 hcurvature
  have hrecoverA : constantCoeff A • projectiveValveNormalize A = A := by
    unfold projectiveValveNormalize
    rw [smul_smul]
    simp [hA0]
  have hrecoverB : constantCoeff A • projectiveValveNormalize B = B := by
    unfold projectiveValveNormalize
    rw [smul_smul, hconstant]
    simp [hB0]
  calc
    A = constantCoeff A • projectiveValveNormalize A := hrecoverA.symm
    _ = constantCoeff A • projectiveValveNormalize B := by
      rw [hnormalized]
    _ = B := hrecoverB

end CarrySelfAdjointOperator.ProjectiveValve

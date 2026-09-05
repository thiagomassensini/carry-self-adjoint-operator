import CarrySelfAdjointOperator.ProjectiveValveAlgebra
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments

/-!
# The actual completed-native moments in the projective multiplicative valve

The existing native recurrence and the existing projective valve meet
literally in the same formal series ring. Writing Phi(v) for the real even
characteristic and Q(v) for its canonical logarithmic moments, the normalized
characteristic satisfies A' = -Q*A. Consequently the valve mass of Q is
A^{-1} = Phi(0)/Phi, and its tower log-derivative channel is v*Q.

These statements identify the scalar normalization and sign. They do not
supply a geometric Gram representation, nor identify a depth variable with
the height-squared variable without a further transport.
-/

namespace CarrySelfAdjointOperator

open PowerSeries
open scoped BigOperators
open ProjectiveValve GreenMultiplicativeValveBridge

noncomputable section

/-- The real even characteristic, as a formal series in height squared. -/
def completedNativeEvenFormalSeries : PowerSeries ℝ :=
  mk completedNativeRealEvenCharacteristicCoefficient

/-- The characteristic normalized to constant coefficient one. -/
def normalizedCompletedNativeEvenFormalSeries : PowerSeries ℝ :=
  C (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
    completedNativeEvenFormalSeries

@[simp] theorem normalizedCompletedNativeEvenFormalSeries_constantCoeff :
    constantCoeff normalizedCompletedNativeEvenFormalSeries = 1 := by
  simp [normalizedCompletedNativeEvenFormalSeries, completedNativeEvenFormalSeries,
    completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero]

/-- The native moment recurrence is exactly the formal differential equation
Phi' = -Q*Phi, with Q the already constructed native moment sequence. -/
theorem derivative_completedNativeEvenFormalSeries :
    d⁄dX ℝ completedNativeEvenFormalSeries =
      -(mk canonicalCompletedNativeLogDerivativeMoment) *
        completedNativeEvenFormalSeries := by
  ext n
  rw [coeff_derivative, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [completedNativeEvenFormalSeries, coeff_mk, map_neg, neg_mul]
  rw [Finset.sum_neg_distrib, Finset.sum_range_succ]
  simp only [Nat.sub_self]
  have h := canonicalCompletedNativeLogDerivativeMoment_real_recurrence n
  push_cast at h
  nlinarith

/-- Dividing by the nonzero central coefficient preserves the same equation. -/
theorem derivative_normalizedCompletedNativeEvenFormalSeries :
    d⁄dX ℝ normalizedCompletedNativeEvenFormalSeries =
      -(mk canonicalCompletedNativeLogDerivativeMoment) *
        normalizedCompletedNativeEvenFormalSeries := by
  unfold normalizedCompletedNativeEvenFormalSeries
  change (C (completedNativeRealEvenCharacteristicCoefficient 0)⁻¹ *
    completedNativeEvenFormalSeries).derivativeFun = _
  have h := derivative_completedNativeEvenFormalSeries
  change completedNativeEvenFormalSeries.derivativeFun = _ at h
  rw [derivativeFun_mul, derivativeFun_C, smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero, h]
  ring

/-- The normalized characteristic is the valve mass of minus the moments. -/
theorem normalizedCompletedNativeEvenFormalSeries_eq_valveMass_neg :
    normalizedCompletedNativeEvenFormalSeries =
      projectiveValveMass (-(mk canonicalCompletedNativeLogDerivativeMoment)) :=
  projectiveValveMass_unique _
    normalizedCompletedNativeEvenFormalSeries
    normalizedCompletedNativeEvenFormalSeries_constantCoeff
    derivative_normalizedCompletedNativeEvenFormalSeries

/-- The valve mass of the native moments is the reciprocal normalized
characteristic. This fixes the sign of the Green-to-moment comparison. -/
theorem projectiveValveMass_nativeMoments_eq_reciprocal :
    projectiveValveMass (mk canonicalCompletedNativeLogDerivativeMoment) =
      normalizedCompletedNativeEvenFormalSeries⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one
    (show constantCoeff normalizedCompletedNativeEvenFormalSeries ≠ 0 by simp)).2
  rw [normalizedCompletedNativeEvenFormalSeries_eq_valveMass_neg,
    ← projectiveValveMass_add]
  simp

/-- Extracting the curvature of the reciprocal characteristic gives the
actual native moment series, without any positivity assumption. -/
theorem projectiveValveCurvature_nativeReciprocal_eq_moments :
    projectiveValveCurvature normalizedCompletedNativeEvenFormalSeries⁻¹ =
      mk canonicalCompletedNativeLogDerivativeMoment := by
  rw [← projectiveValveMass_nativeMoments_eq_reciprocal,
    projectiveValveCurvature_projectiveValveMass]

/-- Equality of a proposed valve mass with the reciprocal native
characteristic is equivalent to the existing native moment obligation. -/
theorem isNativeMomentSequence_iff_valveMass_eq_nativeReciprocal
    (moments : ℕ → ℝ) :
    IsCompletedNativeLogDerivativeMomentSequence moments ↔
      projectiveValveMass (mk moments) =
        normalizedCompletedNativeEvenFormalSeries⁻¹ := by
  constructor
  · intro h
    rw [completedNativeLogDerivativeMoment_eq_canonical h]
    exact projectiveValveMass_nativeMoments_eq_reciprocal
  · intro h
    have hseries : mk moments = mk canonicalCompletedNativeLogDerivativeMoment :=
      projectiveValveMass_injective
        (h.trans projectiveValveMass_nativeMoments_eq_reciprocal.symm)
    have hm : moments = canonicalCompletedNativeLogDerivativeMoment := by
      funext n
      simpa only [coeff_mk] using congrArg (coeff n) hseries
    rw [hm]
    exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

/-- Exact comparison for a proposed original-depth Green curvature: its
projective mass has the native normalization precisely when its transported
curvature equals the native moment series. -/
theorem projectiveGreenMass_eq_nativeReciprocal_iff
    (curvature : PowerSeries ℝ) :
    projectiveGreenMass curvature =
        normalizedCompletedNativeEvenFormalSeries⁻¹ ↔
      ProjectiveDepth.toProjective curvature =
        mk canonicalCompletedNativeLogDerivativeMoment := by
  rw [← projectiveValveMass_toProjective,
    ← projectiveValveMass_nativeMoments_eq_reciprocal]
  exact projectiveValveMass_injective.eq_iff

end
end CarrySelfAdjointOperator

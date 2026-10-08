import CarrySelfAdjointOperator.CompletedNativeThetaTenthSourceCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaTenthPolynomialEnclosure

/-!
# The order-ten mixed source integral sign

The source recurrence and the signed Green boundary face were fixed before
this enclosure. This module closes only their next raw integral sign.
It uses the original theta source, curvature-corrected quadrature, all
higher modes and the exact Xi/theta integrations by parts. No downstream
moment positivity or target-defined carrier occurs in the proof.
-/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

/-- A source-only, strict rational margin for the existing mixed polynomial.
The six raw Xi integrals are not varied independently: their common theta
source and all integrations-by-parts correlations are retained. -/
theorem nativeSourceTenthMixedNumerator_gt_rational :
    (1/10000000000000:ℝ) < nativeSourceTenthMixedNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5) := by
  have h3 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 2
  have h4 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 3
  have h5 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 4
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at h3 h4 h5
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments, h3, h4, h5]
  convert nativeSourceTenthMixedNumerator_thetaIntegral_box_pos
    (completedNativeThetaTailMoment 0) (completedNativeThetaTailMoment 2)
    (completedNativeThetaTailMoment 4) (completedNativeThetaTailMoment 6)
    (completedNativeThetaTailMoment 8) (completedNativeThetaTailMoment 10)
    nativeSourceThetaIntegral_curvature_box_0 nativeSourceThetaIntegral_curvature_box_2
    nativeSourceThetaIntegral_curvature_box_4 nativeSourceThetaIntegral_curvature_box_6
    nativeSourceThetaIntegral_curvature_box_8 nativeSourceThetaIntegral_curvature_box_10 using 1
  ring

/-- The previously isolated new source sign is now unconditional. -/
theorem nativeSourceTenthMixedNumerator_pos :
    0 < nativeSourceTenthMixedNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5) :=
  lt_trans (by norm_num) nativeSourceTenthMixedNumerator_gt_rational

/-- Positivity of the actual source five-even discriminant, not a supplied
moment sign or a certificate hypothesis. -/
theorem nativeSourceFiveEvenDiscriminant_pos :
    0 < nativeSourceFiveEvenDiscriminant :=
  nativeSourceFiveEvenDiscriminant_pos_iff_rawIntegral.mpr nativeSourceTenthMixedNumerator_pos

/-- All three even coordinates and every mixed cross remain present. -/
theorem nativeSourceFiveEvenBoundaryEnergy_pos (u v w : ℂ)
    (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    0 < nativeSourceFiveEvenBoundaryEnergy u v w :=
  nativeSourceFiveEvenBoundaryEnergy_pos_iff.mpr nativeSourceFiveEvenDiscriminant_pos u v w h

/-- Strict positivity of the complete FIVE-COORDINATE BOUNDARY FACE.
This is not the radial storage at a finite nonzero step. Its uniform
remainder transport must still be proved separately. -/
theorem nativeSourceFiveBoundaryEnergy_pos (x : Fin 5 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiveBoundaryEnergy x :=
  nativeSourceFiveBoundaryEnergy_pos_iff.mpr nativeSourceFiveEvenDiscriminant_pos x hx

end
end CarrySelfAdjointOperator

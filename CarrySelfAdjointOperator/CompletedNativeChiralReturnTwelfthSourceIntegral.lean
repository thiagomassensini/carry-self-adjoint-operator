import CarrySelfAdjointOperator.CompletedNativeThetaTwelfthSourceCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaTwelfthPolynomialEnclosure

/-!
# The order-twelve mixed source integral sign

The original source polynomial is enclosed using this repository's theta
curvature quadrature, with all higher modes and both sides of the source tail.
The external enclosure audit that motivated the refinement is Liu--Mao,
*Infinite log-concavity of the Taylor coefficients of the Riemann xi-function*,
arXiv:2610.04972v1, https://arxiv.org/abs/2610.04972 . No external interval,
quadrature routine or log-concavity claim is a proof input here.

This closes the SIX-COORDINATE BOUNDARY FACE only. The exact analytic
remainder of the finite-step radial storage still needs uniform transport.
-/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

/-- A strict source-only rational margin, retaining the shared theta source. -/
theorem nativeSourceTwelfthMixedNumerator_gt_rational :
    (1/10000000000000000000:ℝ) < nativeSourceTwelfthMixedNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
      (completedNativeXiCosineMoment 6) := by
  have h3 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 2
  have h4 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 3
  have h5 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 4
  have h6 := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 5
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at h3 h4 h5 h6
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_one_eq_thetaTailMoments,
    completedNativeXiCosineMoment_two_eq_thetaTailMoments, h3, h4, h5, h6]
  convert nativeSourceTwelfthMixedNumerator_thetaIntegral_box_pos
    (completedNativeThetaTailMoment 0) (completedNativeThetaTailMoment 2)
    (completedNativeThetaTailMoment 4) (completedNativeThetaTailMoment 6)
    (completedNativeThetaTailMoment 8) (completedNativeThetaTailMoment 10)
    (completedNativeThetaTailMoment 12)
    nativeSourceThetaIntegral_twelfth_box_0 nativeSourceThetaIntegral_twelfth_box_2
    nativeSourceThetaIntegral_twelfth_box_4 nativeSourceThetaIntegral_twelfth_box_6
    nativeSourceThetaIntegral_twelfth_box_8 nativeSourceThetaIntegral_twelfth_box_10
    nativeSourceThetaIntegral_twelfth_box_12 using 1
  ring

/-- The actual source sign is unconditional. -/
theorem nativeSourceTwelfthMixedNumerator_pos :
    0 < nativeSourceTwelfthMixedNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
      (completedNativeXiCosineMoment 6) :=
  lt_trans (by norm_num) nativeSourceTwelfthMixedNumerator_gt_rational

/-- Strict positivity of the actual three-coordinate odd source discriminant. -/
theorem nativeSourceSixOddDiscriminant_pos : 0 < nativeSourceSixOddDiscriminant :=
  nativeSourceSixOddDiscriminant_pos_iff_rawIntegral.mpr nativeSourceTwelfthMixedNumerator_pos

/-- All three odd coordinates and their cross terms remain present. -/
theorem nativeSourceSixOddBoundaryEnergy_pos (u v w : ℂ)
    (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) :
    0 < nativeSourceSixOddBoundaryEnergy u v w :=
  nativeSourceSixOddBoundaryEnergy_pos_iff.mpr nativeSourceSixOddDiscriminant_pos u v w h

/-- Strict positivity of the whole limiting face; this does not yet control
its finite-step analytic remainder uniformly over coefficient vectors. -/
theorem nativeSourceSixBoundaryEnergy_pos (x : Fin 6 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceSixBoundaryEnergy x :=
  nativeSourceSixBoundaryEnergy_pos_iff_rawIntegral.mpr nativeSourceTwelfthMixedNumerator_pos x hx
end
end CarrySelfAdjointOperator

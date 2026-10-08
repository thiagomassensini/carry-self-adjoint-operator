import CarrySelfAdjointOperator.CompletedNativeThetaFourteenthSourceCertificate
import CarrySelfAdjointOperator.CompletedNativeThetaFourteenthPolynomialEnclosure

/-! Close the original seven-coordinate SOURCE sign using only the unchanged
theta integral kernel. The complete boundary face retains all cross terms.
This does not assert arbitrary-order contractivity or a new Hilbert metric. -/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Strict rational margin for the raw integral polynomial, before moments. -/
theorem nativeSourceFourteenthMixedNumerator_integral_pos :
    0 < nativeSourceFourteenthMixedNumerator
      (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
      (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
      (completedNativeXiCosineMoment 4) (completedNativeXiCosineMoment 5)
      (completedNativeXiCosineMoment 6) (completedNativeXiCosineMoment 7) := by
  have h := nativeSourceFourteenthMixedNumerator_thetaIntegral_box_pos
    (completedNativeThetaTailMoment 0) (completedNativeThetaTailMoment 2)
    (completedNativeThetaTailMoment 4) (completedNativeThetaTailMoment 6)
    (completedNativeThetaTailMoment 8) (completedNativeThetaTailMoment 10)
    (completedNativeThetaTailMoment 12) (completedNativeThetaTailMoment 14)
    nativeSourceThetaIntegral_fourteenth_box_0 nativeSourceThetaIntegral_fourteenth_box_2
    nativeSourceThetaIntegral_fourteenth_box_4 nativeSourceThetaIntegral_fourteenth_box_6
    nativeSourceThetaIntegral_fourteenth_box_8 nativeSourceThetaIntegral_fourteenth_box_10
    nativeSourceThetaIntegral_fourteenth_box_12 nativeSourceThetaIntegral_fourteenth_box_14
  rw [completedNativeXiCosineMoment_zero_eq_thetaTailMoments,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 0,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 1,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 2,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 3,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 4,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 5,
    completedNativeXiCosineMoment_succ_eq_thetaTailMoments 6]
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.cast_ofNat,pow_one,one_mul,zero_mul] at h ⊢
  convert (lt_trans (show (0:ℝ) < 1/10000000000000000000000 by norm_num) h) using 1
  congr 1
  all_goals ring

/-- The only remaining source sign in the complete seven-coordinate face. -/
theorem nativeSourceSevenEvenDiscriminant_pos : 0 < nativeSourceSevenEvenDiscriminant := by
  rw [nativeSourceSevenEvenDiscriminant_integral_formula]
  exact div_pos nativeSourceFourteenthMixedNumerator_integral_pos
    (by positivity [completedNativeXiCosineMoment_pos 0])

theorem nativeSourceSevenEvenBoundaryEnergy_pos (u v w t : ℂ)
    (hn : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0 ∨ t ≠ 0) :
    0 < nativeSourceSevenEvenBoundaryEnergy u v w t :=
  nativeSourceSevenEvenBoundaryEnergy_pos_iff.mpr nativeSourceSevenEvenDiscriminant_pos u v w t hn

theorem nativeSourceSevenBoundaryEnergy_pos (x : Fin 7 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceSevenBoundaryEnergy x :=
  nativeSourceSevenBoundaryEnergy_pos_iff.mpr nativeSourceSevenEvenDiscriminant_pos x hx

/-- Uniform margin in the already existing finite coordinate norm. -/
theorem nativeSourceSevenBoundaryEnergy_uniform_margin :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin 7 → ℂ, ε*‖x‖^2 ≤ nativeSourceSevenBoundaryEnergy x :=
  nativeSourceSevenBoundaryEnergy_uniform_margin_iff.mpr nativeSourceSevenEvenDiscriminant_pos
end
end CarrySelfAdjointOperator

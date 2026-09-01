import CarrySelfAdjointOperator.CompletedC3CoisometricWronskianEnergyGate
import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization
import CarrySelfAdjointOperator.CompletedC3GammaFullWronskianOperatorBridge
import Mathlib.Tactic

/-!
# Coisometric chiral energy block

The diagonal completed TFVD Wronskian is a signed difference of two
orthogonal chiral energies.  The coisometric boundary contributes an
independent positive ambient-response energy.  This module retains both
pieces by adjoining the ambient response to the negative chiral channel.

The remaining sewing equation then becomes one literal equality of squared
Hilbert norms.  No positivity, zero, confinement, or spectral premise is used
in that reduction.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Direct-sum carrier containing the scaled ambient response and the
negative full-Wronskian chirality. -/
abbrev CanonicalCompletedC3CoisometricChiralEnergyCarrier :=
  WithLp 2
    (CarryGammaComplexNaimark ×
      CanonicalCompletedC3FullWronskianOperatorCarrier)

/-- The positive block naturally compared with the positive Wronskian
chirality in the upper half-plane. -/
def canonicalCompletedC3CoisometricChiralEnergyState
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3CoisometricChiralEnergyCarrier :=
  WithLp.toLp 2
    (((Real.sqrt (2 * z.im) : ℝ) : ℂ) •
        canonicalCompletedC3AmbientResponseState z hzHalf,
      canonicalCompletedC3FullWronskianNegativePolarization
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z))

/-- The completed TFVD diagonal Wronskian is exactly the positive chiral
energy minus the negative chiral energy. -/
theorem canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_im_eq_chiralEnergyDifference
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalC3BracketTfvdCompletedWronskianReadout M z z).im =
      ‖canonicalCompletedC3FullWronskianPositivePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 -
        ‖canonicalCompletedC3FullWronskianNegativePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_fullOperatorInner
    M hzStrip hzStrip]
  simpa [Complex.mul_re, Complex.mul_im] using
    (canonicalCompletedC3FullWronskian_chiralityBalance
      (canonicalCompletedC3NormalizedFullWronskianOperatorState M z))

/-- Pythagoras for the enlarged coisometric/chiral state. -/
theorem norm_sq_canonicalCompletedC3CoisometricChiralEnergyState
    (M : ℕ) (z : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hzIm : 0 ≤ z.im) :
    ‖canonicalCompletedC3CoisometricChiralEnergyState M z hzHalf‖ ^ 2 =
      2 * z.im * ‖canonicalCompletedC3AmbientResponseState z hzHalf‖ ^ 2 +
        ‖canonicalCompletedC3FullWronskianNegativePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  unfold canonicalCompletedC3CoisometricChiralEnergyState
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖(((Real.sqrt (2 * z.im) : ℝ) : ℂ) •
        canonicalCompletedC3AmbientResponseState z hzHalf)‖ ^ 2 +
        ‖canonicalCompletedC3FullWronskianNegativePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 = _
  rw [norm_smul]
  have htwoIm : 0 ≤ 2 * z.im := by positivity
  have hsqrt : (Real.sqrt (2 * z.im)) ^ 2 = 2 * z.im :=
    Real.sq_sqrt htwoIm
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith

/-- The explicit coisometric/Wronskian balance is the difference between the
enlarged positive block and the positive Wronskian chirality. -/
theorem canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_chiralBlockDifference
    (M : ℕ) (z : ℂ)
    (hzIm : 0 ≤ z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
        M z hzStrip.1 =
      ‖canonicalCompletedC3CoisometricChiralEnergyState M z hzStrip.1‖ ^ 2 -
        ‖canonicalCompletedC3FullWronskianPositivePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  unfold canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance
  rw [← canonicalCompletedC3AmbientResponseEnergy_eq_gradient z hzStrip.1,
    canonicalC3BracketTfvdCompletedWronskianReadout_diagonal_im_eq_chiralEnergyDifference
      M z hzStrip,
    norm_sq_canonicalCompletedC3CoisometricChiralEnergyState M z hzStrip.1 hzIm]
  ring

/-- In the upper half-plane, coisometric diagonal sewing is exactly equality
of the two concrete Hilbert energies. -/
theorem canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_chiralBlockNorm
    (M : ℕ) (z : ℂ) (hzIm : 0 < z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3CoisometricCompressedBoundaryReadout
          z z hzStrip.1 hzStrip.1 =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z ↔
      ‖canonicalCompletedC3CoisometricChiralEnergyState M z hzStrip.1‖ ^ 2 =
        ‖canonicalCompletedC3FullWronskianPositivePolarization
          (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  rw [canonicalCompletedC3CoisometricBoundaryReadout_diagonal_eq_wronskian_iff_energyBalance
    M z (ne_of_gt hzIm) hzStrip]
  rw [canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_chiralBlockDifference
    M z hzIm.le hzStrip]
  exact sub_eq_zero

/-- At a hypothetical upper-half-plane characteristic zero the enlarged
block has strictly more energy than the positive Wronskian chirality.  Thus
the norm equality above cannot be obtained by collapsing the two chiral
channels at a scalar zero. -/
theorem norm_sq_positiveChirality_lt_coisometricChiralEnergyState_of_characteristicZero
    (M : ℕ) (z : ℂ) (hzIm : 0 < z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    ‖canonicalCompletedC3FullWronskianPositivePolarization
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 <
      ‖canonicalCompletedC3CoisometricChiralEnergyState M z hzStrip.1‖ ^ 2 := by
  have hbalance :=
    canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_pos_of_characteristicZero
      M z hzIm hzStrip hzero
  rw [canonicalCompletedC3CoisometricDiagonalWronskianEnergyBalance_eq_chiralBlockDifference
    M z hzIm.le hzStrip] at hbalance
  linarith

/-- Consequently the concrete chiral-block norm identity fails at any
hypothetical upper-half-plane characteristic zero. -/
theorem norm_sq_coisometricChiralEnergyState_ne_positiveChirality_of_characteristicZero
    (M : ℕ) (z : ℂ) (hzIm : 0 < z.im)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    ‖canonicalCompletedC3CoisometricChiralEnergyState M z hzStrip.1‖ ^ 2 ≠
      ‖canonicalCompletedC3FullWronskianPositivePolarization
        (canonicalCompletedC3NormalizedFullWronskianOperatorState M z)‖ ^ 2 := by
  exact ne_of_gt
    (norm_sq_positiveChirality_lt_coisometricChiralEnergyState_of_characteristicZero
      M z hzIm hzStrip hzero)

end

end CarrySelfAdjointOperator

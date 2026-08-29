import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerBoundaryDefect
import CarrySelfAdjointOperator.CanonicalC3GammaEnergyNormalization
import Mathlib.Tactic

/-!
# Normalized pointwise C3 gamma sewing

The raw gamma Gram represents a division-free boundary Wronskian.  The
completed ledger `dslope`, however, is normalized by

`2 * conj (F z) * F w`.

This file keeps those two levels distinct.  It defines the correctly
normalized gamma boundary and kernel, then proves that their pointwise sewing
with the completed ledger is equivalent to the raw Cauchy boundary readout
being exactly the completed Wronskian.  No factor is cancelled at a zero.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Characteristic normalization shared by the completed Wronskian numerator
and the normalized gamma Gram. -/
def canonicalCompletedC3GammaCharacteristicWeight (z w : ℂ) : ℂ :=
  (2 : ℂ) * conj (completedNativeOperatorCharacteristic z) *
    completedNativeOperatorCharacteristic w

/-- Raw positive gamma kernel after the exact characteristic normalization
used by the completed response. -/
def canonicalCompletedC3NormalizedPolarizedGammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3PolarizedGammaKernel z w hz hw /
    canonicalCompletedC3GammaCharacteristicWeight z w

/-- The concrete Gamma/Naimark response with the exact `sqrt 2 * F`
normalization used by the completed native moment construction. -/
def canonicalCompletedC3NormalizedPolarizedGammaState
    (z : ℂ) (hz : z.im ≠ 0) : CarryGammaComplexNaimark :=
  ((((Real.sqrt 2 : ℝ) : ℂ) *
      completedNativeOperatorCharacteristic z)⁻¹) •
    canonicalCompletedC3PolarizedGammaState z hz

/-- The normalized Gamma kernel is literally the Gram kernel of the
normalized Gamma/Naimark responses.  In particular, its positivity does not
use the pending Gamma--Wronskian sewing. -/
theorem canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_inner
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
      inner ℂ
        (canonicalCompletedC3NormalizedPolarizedGammaState z hz)
        (canonicalCompletedC3NormalizedPolarizedGammaState w hw) := by
  unfold canonicalCompletedC3NormalizedPolarizedGammaKernel
    canonicalCompletedC3GammaCharacteristicWeight
    canonicalCompletedC3NormalizedPolarizedGammaState
    canonicalCompletedC3PolarizedGammaKernel
  have hsqrt_sq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsqrt_inv_sq : (2 : ℂ)⁻¹ =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [← hsqrt_sq, ← inv_pow, pow_two]
  rw [inner_smul_left, inner_smul_right]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal]
  simp only [div_eq_mul_inv, mul_inv]
  rw [hsqrt_inv_sq]
  ring

/-- Every finite section of the normalized Gamma kernel is positive
semidefinite.  The statement uses Lean's total inverse at characteristic
zeros; it does not assert a continuous extension through such a zero. -/
theorem canonicalCompletedC3NormalizedPolarizedGammaKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hoffAxis : ∀ i, (point i).im ≠ 0) :
    (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedPolarizedGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)).PosSemidef := by
  rw [show (Matrix.of fun i j =>
      canonicalCompletedC3NormalizedPolarizedGammaKernel
        (point i) (point j) (hoffAxis i) (hoffAxis j)) =
      Matrix.gram ℂ (fun i =>
        canonicalCompletedC3NormalizedPolarizedGammaState
          (point i) (hoffAxis i)) by
    ext i j
    exact canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_inner
      (point i) (point j) (hoffAxis i) (hoffAxis j)]
  exact Matrix.posSemidef_gram ℂ _

/-- Cauchy boundary readout with the same characteristic normalization. -/
def canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw /
    canonicalCompletedC3GammaCharacteristicWeight z w

/-- Normalization commutes exactly with the two-parameter gamma Green
identity. -/
theorem canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout_eq_kernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw =
      (w - conj z) *
        canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw := by
  rw [canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout,
    canonicalCompletedC3NormalizedPolarizedGammaKernel,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]
  ring

/-- Away from characteristic zeros, the completed ledger numerator is the
completed Wronskian divided by the same characteristic weight. -/
theorem canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_wronskian_div_weight
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w =
      completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z /
        canonicalCompletedC3GammaCharacteristicWeight z w := by
  have hzChart : canonicalC3ChartFactorHeight z ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hzStrip
  have hwChart : canonicalC3ChartFactorHeight w ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hwStrip
  have hzChartStar : conj (canonicalC3ChartFactorHeight z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzChart
  have hchartWeight :
      mixedHermitianWeight canonicalC3ChartFactorHeight w z ≠ 0 :=
    mul_ne_zero hwChart hzChartStar
  have hzFStar : conj (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  have hweight : canonicalCompletedC3GammaCharacteristicWeight z w ≠ 0 := by
    unfold canonicalCompletedC3GammaCharacteristicWeight
    exact mul_ne_zero (mul_ne_zero (by norm_num) hzFStar) hwF
  have hcompanion :
      (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator,
    canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_eq_completedWronskian
      M hwStrip hzStrip,
    hcompanion]
  unfold canonicalCompletedC3GammaCharacteristicWeight
  field_simp [hchartWeight, hweight]

/-- Correctly normalized final gate: the normalized positive gamma kernel is
the completed `dslope` exactly when the normalized Cauchy boundary equals the
normalized completed ledger. -/
theorem canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_ledger
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w ↔
      canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw =
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w := by
  rw [canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout_eq_kernel,
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
      M hzStrip hwStrip hzF hwF hsep]
  constructor
  · intro h
    rw [h]
  · intro h
    exact mul_left_cancel₀ (sub_ne_zero.mpr hsep) h

/-- Pointwise raw form of the same gate.  After the normalization is placed
on both sides, sewing is exactly `Cauchy boundary = completed Wronskian`. -/
theorem canonicalCompletedC3NormalizedBoundaryReadout_eq_ledger_iff_rawWronskian
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw =
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w ↔
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  have hzFStar : conj (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  have hweight : canonicalCompletedC3GammaCharacteristicWeight z w ≠ 0 := by
    unfold canonicalCompletedC3GammaCharacteristicWeight
    exact mul_ne_zero (mul_ne_zero (by norm_num) hzFStar) hwF
  rw [canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout,
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_wronskian_div_weight
      M hzStrip hwStrip hzF hwF]
  exact div_left_inj' hweight

/-- Capstone of the normalization audit: the normalized gamma--`dslope`
identity is equivalent to the literal division-free pointwise
Green--Wronskian identity. -/
theorem canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w ↔
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  rw [canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_ledger
      M z w hz hw hzStrip hwStrip hzF hwF hsep,
    canonicalCompletedC3NormalizedBoundaryReadout_eq_ledger_iff_rawWronskian
      M z w hz hw hzStrip hwStrip hzF hwF]

/-! ## Pointwise defect identity -/

/-- Literal unnormalized mismatch between the C3 Gamma boundary and the
completed Wronskian.  Both objects retain their native normalization. -/
def canonicalCompletedC3RawGammaWronskianDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
    completedGreenWronskian
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion w z

/-- After characteristic normalization, the complete boundary mismatch is
exactly the raw pointwise defect divided by the characteristic weight. -/
theorem canonicalCompletedC3NormalizedBoundary_sub_ledger_eq_rawDefect_div_weight
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw /
        canonicalCompletedC3GammaCharacteristicWeight z w := by
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_wronskian_div_weight
    M hzStrip hwStrip hzF hwF]
  unfold canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout
    canonicalCompletedC3RawGammaWronskianDefect
  ring

/-- Division-free propagation of the same defect through the positive Gamma
kernel and the completed `dslope`.  The spectral-separation factor is kept
explicit rather than cancelled. -/
theorem canonicalCompletedC3Separation_mul_normalizedKernel_sub_dslope_eq_rawDefect_div_weight
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    (w - conj z) *
        (canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw -
          canonicalCompletedNativePolarizedDslopeKernel z w) =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw /
        canonicalCompletedC3GammaCharacteristicWeight z w := by
  calc
    (w - conj z) *
          (canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw -
            canonicalCompletedNativePolarizedDslopeKernel z w) =
        canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw -
          canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w := by
            rw [canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout_eq_kernel,
              canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
                M hzStrip hwStrip hzF hwF hsep]
            ring
    _ = canonicalCompletedC3RawGammaWronskianDefect z w hz hw /
          canonicalCompletedC3GammaCharacteristicWeight z w :=
      canonicalCompletedC3NormalizedBoundary_sub_ledger_eq_rawDefect_div_weight
        M z w hz hw hzStrip hwStrip hzF hwF

/-- On the diagonal the raw two-parameter Gamma boundary is exactly the
already formalized global Cauchy-skew boundary measure. -/
theorem canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_eq_cauchySkew
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z z hz hz =
      (-(2 : ℂ) * Complex.I) *
        (completedGammaCauchySkew canonicalCompletedC3SixCameraSource z hz : ℂ) := by
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel,
    canonicalCompletedC3PolarizedGammaKernel_diagonal_eq_norm_sq,
    neg_two_i_mul_completedGammaCauchySkew_eq_centeredFactor_mul_energy]
  unfold canonicalCompletedC3PolarizedGammaState carryGammaComplexState
    completedGammaEnergy
  rw [totalCarryGammaState_of_im_ne_zero canonicalCompletedC3SixCameraSource hz]
  norm_cast

/-- Consequently the diagonal pointwise defect is exactly the old Cauchy
boundary measure minus the completed Wronskian, with no normalization or
channel hidden. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_diagonal_eq_cauchy_sub_wronskian
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3RawGammaWronskianDefect z z hz hz =
      (-(2 : ℂ) * Complex.I) *
          (completedGammaCauchySkew canonicalCompletedC3SixCameraSource z hz : ℂ) -
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z z := by
  rw [canonicalCompletedC3RawGammaWronskianDefect,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_eq_cauchySkew]

end

end CarrySelfAdjointOperator

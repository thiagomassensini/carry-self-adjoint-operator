import CarrySelfAdjointOperator.CompletedGreenHeightChannelBridge
import CarrySelfAdjointOperator.CanonicalCompletedC3GammaLedgerNumerator
import Mathlib.Tactic

/-!
# Reconciliation of the height-channel bridge with the polarized `dslope`

The height-channel bridge (`CompletedGreenHeightChannelBridge`) expresses the
Herglotz/Pick object as the divided difference
`(a z − conj a w)/(z − conj w)` of the coordinate
`a = completedNativeLogDerivativeHerglotzCoordinate = −F'/F`.

The completed-native transport machinery instead uses the polarized `dslope`
of the normalized response `Psi/(2F) = a/2`, with the conjugate-first
separation `w − conj z` (`canonicalCompletedNativePolarizedDslopeKernel`).

This file proves they are the same object.  The build's polarized `dslope`
kernel is exactly the bridge's Herglotz divided difference, halved, in the
conjugate-first separation.  This closes the `z − conj w` factor end to end:
from the finite native/camera Green identity through to the height spectral
kernel, the separation is carried, not re-derived.
-/

open scoped ComplexConjugate ComplexOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The completed-native normalized response is half the bridge's Herglotz
coordinate `a = −F'/F`; this is the `Psi/(2F)` versus `Psi/F` normalization. -/
theorem completedGreenNormalizedResponse_native_eq_half_coordinate (z : ℂ) :
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z =
      completedNativeLogDerivativeHerglotzCoordinate z / 2 := by
  unfold completedGreenNormalizedResponse
    completedNativeLogDerivativeHerglotzCoordinate
    completedNativeOperatorBoundaryCompanion
  ring

/-- The Hermitian-polarized response numerator is the coordinate divided
difference numerator, halved. -/
theorem canonicalCompletedNativePolarizedResponseNumerator_eq_coordinate
    (z w : ℂ) :
    canonicalCompletedNativePolarizedResponseNumerator z w =
      (completedNativeLogDerivativeHerglotzCoordinate w -
          conj (completedNativeLogDerivativeHerglotzCoordinate z)) / 2 := by
  simp only [canonicalCompletedNativePolarizedResponseNumerator,
    completedGreenNormalizedResponse_native_eq_half_coordinate,
    map_div₀, map_ofNat]
  ring

/-- **End-to-end reconciliation.**  The transport machinery's polarized
`dslope` kernel is exactly the bridge's Herglotz divided difference of
`a = −F'/F`, halved, in the conjugate-first separation `w − conj z`.  The
`z − conj w` factor from the finite Green identity is carried verbatim to the
height spectral kernel. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_eq_herglotzDividedDifference
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      (completedNativeLogDerivativeHerglotzCoordinate w -
          conj (completedNativeLogDerivativeHerglotzCoordinate z)) /
        ((2 : ℂ) * (w - conj z)) := by
  have hsepNe : w - conj z ≠ 0 := sub_ne_zero.mpr hsep
  have hdslope :
      canonicalCompletedNativePolarizedDslopeKernel z w =
        canonicalCompletedNativePolarizedResponseNumerator z w /
          (w - conj z) := by
    rw [canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope
      hzStrip hsep, mul_comm, mul_div_assoc, div_self hsepNe, mul_one]
  rw [hdslope, canonicalCompletedNativePolarizedResponseNumerator_eq_coordinate,
    div_div]

/-- **Diagonal of the reconciliation.**  Off the real axis, the polarized
`dslope` kernel on the diagonal is the real ratio `Im a(z) / (2 Im z)` — the
Herglotz sign, halved.  Unconditional. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_diagonal_eq_coordinate_im
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzIm : z.im ≠ 0) :
    canonicalCompletedNativePolarizedDslopeKernel z z =
      (((completedNativeLogDerivativeHerglotzCoordinate z).im /
        (2 * z.im) : ℝ) : ℂ) := by
  have hsep : z ≠ conj z := by
    intro h
    apply hzIm
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  rw [canonicalCompletedNativePolarizedDslopeKernel_eq_herglotzDividedDifference
    hzStrip hsep, Complex.sub_conj, Complex.sub_conj]
  push_cast
  field_simp

/-- **Diagonal Herglotz positivity, transported.**  Under a division-free Green
representation, the polarized `dslope` kernel on the nonreal diagonal has
nonnegative real part — the height sign gate expressed directly on the build's
kernel, via the bridge's `Im a / Im z ≥ 0`. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_diagonal_re_nonneg_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {state : ℂ → H}
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzIm : z.im ≠ 0) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re := by
  rw [canonicalCompletedNativePolarizedDslopeKernel_diagonal_eq_coordinate_im
      hzStrip hzIm, Complex.ofReal_re,
    show (completedNativeLogDerivativeHerglotzCoordinate z).im / (2 * z.im) =
        ((completedNativeLogDerivativeHerglotzCoordinate z).im / z.im) / 2 by
      ring]
  exact div_nonneg
    (completedNativeLogDerivative_im_div_nonneg_of_divisionFreeGreen
      hgreen z hzF hzIm)
    (by norm_num)

/-- **Sampled positive semidefiniteness.**  Under a division-free Green
representation, the polarized `dslope` (height Pick) kernel is a Gram matrix on
every finite conjugate-separated sample, hence positive semidefinite.  This is
the finite face of the Herglotz/Pick positivity, obtained directly from the
Green representation — a Green-side counterpart of the Schur-product route
`canonicalCompletedNativePolarizedDslopeKernel_posSemidef_of_chiralPick`.  The
scaling `1/√2` absorbs the `2F` normalization into the Gram vectors. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_posSemidef_of_divisionFreeGreen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {state : ℂ → H}
    (hgreen : HasDivisionFreeGreenRepresentation
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion state)
    {ι : Type*} [Fintype ι]
    (point : ι → ℂ)
    (hstrip : ∀ i, operatorHeightParameter (point i) ∈ genuineCriticalStrip)
    (hF : ∀ i, completedNativeOperatorCharacteristic (point i) ≠ 0)
    (hsep : ∀ i j, point i ≠ conj (point j)) :
    (Matrix.of fun i j =>
      canonicalCompletedNativePolarizedDslopeKernel
        (point i) (point j)).PosSemidef := by
  have hrw : (Matrix.of fun i j =>
      canonicalCompletedNativePolarizedDslopeKernel (point i) (point j)) =
      Matrix.gram ℂ (fun i =>
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
          (completedNativeOperatorCharacteristic (point i))⁻¹ •
            state (point i)) := by
    ext i j
    rw [Matrix.of_apply, Matrix.gram_apply,
      canonicalCompletedNativePolarizedDslopeKernel_eq_herglotzDividedDifference
        (hstrip i) (hsep j i),
      inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ← completedNativeHerglotzKernel_eq_gram_of_divisionFreeGreen
        hgreen (point j) (point i) (hF j) (hF i) (hsep j i),
      ← mul_assoc, ← Complex.ofReal_mul,
      show ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 by
        rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      div_mul_div_comm, one_mul]
  rw [hrw]
  exact Matrix.posSemidef_gram ℂ _

/-- **Diagonal equivalence.**  Off the real axis, the diagonal `dslope`
positivity is *equivalent* to the Herglotz sign of `a = −F'/F` — not merely
implied by it.  Unconditional. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_herglotz
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzIm : z.im ≠ 0) :
    0 ≤ (canonicalCompletedNativePolarizedDslopeKernel z z).re ↔
      0 ≤ (completedNativeLogDerivativeHerglotzCoordinate z).im / z.im := by
  rw [canonicalCompletedNativePolarizedDslopeKernel_diagonal_eq_coordinate_im
      hzStrip hzIm, Complex.ofReal_re,
    show (completedNativeLogDerivativeHerglotzCoordinate z).im / (2 * z.im) =
        ((completedNativeLogDerivativeHerglotzCoordinate z).im / z.im) / 2 from by
      ring]
  constructor <;> intro h <;> linarith

/-- **Converse aggregation.**  If the sampled polarized `dslope` (height Pick)
matrix is positive semidefinite on a finite off-axis sample, then the Herglotz
sign `Im a / Im z ≥ 0` holds at every sample point — read off the diagonal of
the positive semidefinite matrix.  Together with the forward Gram direction,
sampled positivity is *equivalent* to pointwise Herglotz positivity. -/
theorem herglotz_of_sampled_polarizedDslopePosSemidef
    {ι : Type*} [Fintype ι]
    (point : ι → ℂ)
    (hstrip : ∀ i, operatorHeightParameter (point i) ∈ genuineCriticalStrip)
    (hzIm : ∀ i, (point i).im ≠ 0)
    (hPSD : (Matrix.of fun i j =>
      canonicalCompletedNativePolarizedDslopeKernel
        (point i) (point j)).PosSemidef)
    (i : ι) :
    0 ≤ (completedNativeLogDerivativeHerglotzCoordinate (point i)).im /
      (point i).im := by
  rw [← canonicalCompletedNativePolarizedDslopeKernel_diagonal_re_nonneg_iff_herglotz
    (hstrip i) (hzIm i)]
  have hdiag : (0 : ℂ) ≤
      canonicalCompletedNativePolarizedDslopeKernel (point i) (point i) := by
    simpa [Matrix.of_apply] using hPSD.2 (Finsupp.single i (1 : ℂ))
  simpa using (Complex.le_def.mp hdiag).1

end

end CarrySelfAdjointOperator

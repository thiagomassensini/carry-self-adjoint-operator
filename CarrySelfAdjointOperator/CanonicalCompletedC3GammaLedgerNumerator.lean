import CarrySelfAdjointOperator.CanonicalCompletedC3GammaDslopeGram
import CarrySelfAdjointOperator.CompletedC3FinalReadoutKernelBridge
import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Canonical completed C3 gamma/ledger numerator

The completed ledger and the positive gamma Gram use the same Hermitian
orientation only after centered Schwarz reflection has been transported from
the characteristic to its derivative and normalized response.  This file
performs that transport and keeps the comparison division-free.

At a separated pair `(z,w)`, the enriched ledger numerator is proved to be

`R(w) - conj (R(z)) = (w - conj z) * dslope R (conj z) w`,

where `R = -F'/(2F)`.  Consequently the remaining gamma-to-ledger gate is one
literal equality between two concrete boundary readouts.  No scalar channel
is removed in this reduction.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

private abbrev completedNativeResponse : ℂ → ℂ :=
  completedGreenNormalizedResponse
    completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion

/-! ## Centered Schwarz reflection of the completed response -/

/-- Centered Schwarz reflection passes from the completed characteristic to
its derivative.  The proof differentiates the already-proved native
reflection identity on the open centered-height strip. -/
theorem completedNativeOperatorCharacteristic_deriv_centeredReflection
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    deriv completedNativeOperatorCharacteristic (conj z) =
      conj (deriv completedNativeOperatorCharacteristic z) := by
  have hzDomain : z ∈ completedNativeHeightDomain := hs
  have hzConjDomain : conj z ∈ completedNativeHeightDomain :=
    operatorHeightParameter_conj_mem_genuineCriticalStrip hs
  have heq :
      completedNativeOperatorCharacteristic =ᶠ[nhds (conj z)]
        (conj ∘ completedNativeOperatorCharacteristic ∘ conj) := by
    filter_upwards
      [isOpen_completedNativeHeightDomain.eventually_mem hzConjDomain] with u hu
    have hreflection :=
      completedNativeOperatorCharacteristic_centeredReflection_via_nativeConjugation
        hu
    have hconj := congrArg conj hreflection
    simpa [Function.comp_def] using hconj.symm
  rw [heq.deriv_eq]
  simp

/-- The completed boundary companion `-F'` obeys the same centered Schwarz
reflection as `F`. -/
theorem completedNativeOperatorBoundaryCompanion_centeredReflection
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeOperatorBoundaryCompanion (conj z) =
      conj (completedNativeOperatorBoundaryCompanion z) := by
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
    completedNativeOperatorCharacteristic_deriv_centeredReflection hs]
  simp

/-- The normalized completed response is centered-Schwarz equivariant.  This
is an identity of the totalized quotient, so no nonvanishing assumption is
needed. -/
theorem completedNativeGreenNormalizedResponse_centeredReflection
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    completedNativeResponse (conj z) =
      conj (completedNativeResponse z) := by
  unfold completedNativeResponse completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_centeredReflection hs,
    completedNativeOperatorCharacteristic_centeredReflection_via_nativeConjugation
      hs]
  simp only [map_div₀, map_mul, map_ofNat]

/-! ## The two concrete numerators -/

/-- Hermitian-polarized numerator of the completed normalized response. -/
def canonicalCompletedNativePolarizedResponseNumerator
    (z w : ℂ) : ℂ :=
  completedNativeResponse w - conj (completedNativeResponse z)

/-- After centered Schwarz reflection, the polarized numerator is exactly
the separation factor multiplying Mathlib's total `dslope`. -/
theorem canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hsep : w ≠ conj z) :
    canonicalCompletedNativePolarizedResponseNumerator z w =
      (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w := by
  unfold canonicalCompletedNativePolarizedResponseNumerator
    completedNativeResponse
  rw [canonicalCompletedNativePolarizedDslopeKernel,
    dslope_of_ne _ hsep, slope_def_module]
  simp only [smul_eq_mul]
  rw [show
    completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (conj z) =
      conj (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z) from
    completedNativeGreenNormalizedResponse_centeredReflection hzStrip]
  field_simp [sub_ne_zero.mpr hsep]

/-- Remove the non-spectral chart and characteristic cross factors from the
completed all-cutoff ledger, but retain the spectral separation.  The point
order matches the gamma Gram: first `z`, then `w`. -/
def canonicalCompletedC3AllCutoffPolarizedLedgerNumerator
    (M : ℕ) (z w : ℂ) : ℂ :=
  (canonicalCompletedC3AllCutoffKernelLedgerState M w z).finalReadout /
    (mixedHermitianWeight canonicalC3ChartFactorHeight w z *
      ((2 : ℂ) *
        conj (completedNativeOperatorCharacteristic z) *
        completedNativeOperatorCharacteristic w))

/-- The complete enriched ledger numerator is exactly the Hermitian-polarized
normalized response.  Radial, provenance, off-diagonal, residual, tail, xi,
and archimedean channels have already remained separate inside the ledger
state up to this final normalization. -/
theorem canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_response
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w =
      canonicalCompletedNativePolarizedResponseNumerator z w := by
  have hzChart : canonicalC3ChartFactorHeight z ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hzStrip
  have hwChart : canonicalC3ChartFactorHeight w ≠ 0 :=
    canonicalC3ChartFactorHeight_ne_zero hwStrip
  have hzChartStar : conj (canonicalC3ChartFactorHeight z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzChart
  have hzFStar : conj (completedNativeOperatorCharacteristic z) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hzF
  have hchartWeight :
      mixedHermitianWeight canonicalC3ChartFactorHeight w z ≠ 0 :=
    mul_ne_zero hwChart hzChartStar
  have hcharacteristicWeight :
      (2 : ℂ) * conj (completedNativeOperatorCharacteristic z) *
          completedNativeOperatorCharacteristic w ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hzFStar) hwF
  have hcompanion :
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator,
    canonicalCompletedC3AllCutoffKernelLedgerState_finalReadout_eq_completedWronskian
      M hwStrip hzStrip,
    hcompanion,
    completedGreenWronskian_eq_normalizedResponse_cross_mul
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion w z hwF hzF]
  unfold canonicalCompletedNativePolarizedResponseNumerator
    completedNativeResponse
  field_simp [hchartWeight, hcharacteristicWeight]

/-- Hence the completed ledger numerator is the exact division-free numerator
of the polarized `dslope`. -/
theorem canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
    (M : ℕ) {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w =
      (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_response
      M hzStrip hwStrip hzF hwF,
    canonicalCompletedNativePolarizedResponseNumerator_eq_mul_dslope
      hzStrip hsep]

/-! ## Exact positive-realization gate -/

/-- The positive gamma Gram realizes the completed-native polarized `dslope`
exactly when its concrete Cauchy boundary readout is the concrete completed
ledger numerator.  This is the final readout equality, with no free defect or
abstract kernel parameter. -/
theorem canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_ledgerNumerator
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3PolarizedGammaKernel z w hz hw =
        canonicalCompletedNativePolarizedDslopeKernel z w ↔
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w := by
  rw [canonicalCompletedC3PolarizedGammaKernel_eq_dslope_iff_boundaryReadout
      z w hz hw (sub_ne_zero.mpr hsep),
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
      M hzStrip hwStrip hzF hwF hsep]

end

end CarrySelfAdjointOperator

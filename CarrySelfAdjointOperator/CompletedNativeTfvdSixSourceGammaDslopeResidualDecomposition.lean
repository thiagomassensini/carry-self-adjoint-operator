import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceGammaEscapeRadialAudit
import CarrySelfAdjointOperator.CanonicalCompletedC3NormalizedGammaSewing
import Mathlib.Tactic

/-!
# Gamma--`dslope` residual decomposed into the pre-existing sewing gates

The six-source radial audit left the literal kernel residual

`dslope - GammaCorrection`.

This file does not make that residual vanish.  Instead, it separates it into
the old Gamma--`dslope` sewing difference and a named Gamma-versus-correction
gap.  A companion division-free formula identifies the corresponding boundary
residual as the old all-channel ledger defect plus one explicit correction
boundary channel.  The characteristic normalization is kept separate: the
old unnormalized boundary defect and the normalized raw Wronskian defect are
different objects.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The actual kernel residual sampled by the preceding six-source radial
audit.  It uses the *raw* Gamma--correction kernel, so it intentionally is
not the normalized Gamma or normalized ambient comparison. -/
def canonicalCompletedNativeGammaDslopeResidual
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedNativePolarizedDslopeKernel z w -
    canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf

/-- The explicit second summand in the raw residual decomposition.  This is
not a symmetry assertion: it compares the positive Gamma Gram in its own
orientation with the Gamma--correction cross kernel in that orientation. -/
def canonicalCompletedC3GammaCorrectionGap
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3PolarizedGammaKernel z w hz hw -
    canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf

/-- The residual from the radial audit is literally `dslope -
GammaCorrection`; the older Cauchy--escape name is interchangeable only by
the already proved polarized cross-channel cancellation. -/
theorem canonicalCompletedNativeGammaDslopeResidual_eq_radialBalanceResidual
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedNativeGammaDslopeResidual z w hz hw hwHalf =
      canonicalCompletedNativePolarizedDslopeKernel z w -
        canonicalCompletedC3GammaCauchyEscapeBalanceKernel z w hz hw hwHalf := by
  unfold canonicalCompletedNativeGammaDslopeResidual
  rw [canonicalCompletedC3GammaCorrectionKernel_eq_gammaCauchyEscapeBalance]

/-- Exact raw decomposition of the six-source residual.  No completion,
normalization, positivity, or cancellation premise is used:

`dslope - GammaCorrection = (dslope - GammaGram) + (GammaGram - GammaCorrection)`.
-/
theorem canonicalCompletedNativeGammaDslopeResidual_eq_oldSewingDefect_add_correctionGap
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedNativeGammaDslopeResidual z w hz hw hwHalf =
      (canonicalCompletedNativePolarizedDslopeKernel z w -
        canonicalCompletedC3PolarizedGammaKernel z w hz hw) +
      canonicalCompletedC3GammaCorrectionGap z w hz hw hwHalf := by
  unfold canonicalCompletedNativeGammaDslopeResidual
    canonicalCompletedC3GammaCorrectionGap
  ring

/-- Boundary version of the named Gamma--correction gap.  The spectral
separation is deliberately retained instead of being divided out. -/
def canonicalCompletedC3GammaCorrectionBoundaryDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
    (w - conj z) *
      canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf

/-- Division-free provenance formula for the raw six-source residual.  The
first summand is the negative of the pre-existing all-channel Gamma/ledger
boundary defect; the second is exactly the named correction boundary defect.
Thus none of the radial, provenance, off-diagonal, readout-residual, tail,
xi, or archimedean ledger channels is hidden. -/
theorem canonicalCompletedNativeGammaDslopeResidual_boundary_eq_neg_oldLedger_add_correction
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    (w - conj z) *
        canonicalCompletedNativeGammaDslopeResidual z w hz hw hwHalf =
      - canonicalCompletedC3GammaLedgerBoundaryDefect M z w hz hw +
        canonicalCompletedC3GammaCorrectionBoundaryDefect z w hz hw hwHalf := by
  unfold canonicalCompletedNativeGammaDslopeResidual
    canonicalCompletedC3GammaLedgerBoundaryDefect
    canonicalCompletedC3GammaCorrectionBoundaryDefect
  rw [canonicalCompletedC3AllCutoffPolarizedLedgerNumerator_eq_mul_dslope
    M hzStrip hwStrip hzF hwF hsep]
  ring

/-- The raw Gamma/ledger defect has a normalized counterpart.  This
definition makes the characteristic weight explicit rather than treating the
two boundary defects as interchangeable. -/
def canonicalCompletedC3NormalizedGammaLedgerBoundaryDefect
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw -
    canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M z w

/-- The remaining difference between the old and normalized ledger defects
is solely the displayed characteristic-normalization gap of the Gamma
boundary.  Lean's total inverse is intentional, so this identity also holds
at characteristic zeros without cancelling a factor. -/
def canonicalCompletedC3GammaBoundaryNormalizationGap
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
    canonicalCompletedC3NormalizedPolarizedGammaBoundaryReadout z w hz hw

theorem canonicalCompletedC3GammaLedgerBoundaryDefect_eq_normalizedDefect_add_normalizationGap
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3GammaLedgerBoundaryDefect M z w hz hw =
      canonicalCompletedC3NormalizedGammaLedgerBoundaryDefect M z w hz hw +
        canonicalCompletedC3GammaBoundaryNormalizationGap z w hz hw := by
  unfold canonicalCompletedC3GammaLedgerBoundaryDefect
    canonicalCompletedC3NormalizedGammaLedgerBoundaryDefect
    canonicalCompletedC3GammaBoundaryNormalizationGap
  ring

/-- Once the characteristic is nonzero in both slots, the normalized old
ledger defect is exactly the raw Gamma--Wronskian defect divided by the
canonical weight `2 * conj(F z) * F w`. -/
theorem canonicalCompletedC3NormalizedGammaLedgerBoundaryDefect_eq_rawDefect_div_weight
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    canonicalCompletedC3NormalizedGammaLedgerBoundaryDefect M z w hz hw =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw /
        canonicalCompletedC3GammaCharacteristicWeight z w := by
  exact canonicalCompletedC3NormalizedBoundary_sub_ledger_eq_rawDefect_div_weight
    M z w hz hw hzStrip hwStrip hzF hwF

/-- The correctly normalized Gamma--`dslope` mismatch has the opposite sign
to the raw Wronskian defect.  This is the normalization-safe counterpart of
the raw residual decomposition; it is not substituted into the raw radial
residual above. -/
theorem canonicalCompletedC3Separation_mul_dslope_sub_normalizedGamma_eq_neg_rawDefect_div_weight
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    (w - conj z) *
        (canonicalCompletedNativePolarizedDslopeKernel z w -
          canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw) =
      - (canonicalCompletedC3RawGammaWronskianDefect z w hz hw /
        canonicalCompletedC3GammaCharacteristicWeight z w) := by
  have h := canonicalCompletedC3Separation_mul_normalizedKernel_sub_dslope_eq_rawDefect_div_weight
    M z w hz hw hzStrip hwStrip hzF hwF hsep
  linear_combination -h

/-- Entrywise bridge from the old shifted-radial residual matrix to the new
named raw residual.  This lets the existing one-, two-, and three-point Pick
microscopes be read as microscopes for the decomposed residual without
changing their amplitudes or Cauchy factors. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix_apply_eq_gammaDslopeResidual
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (i j : Fin N) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k N hhalf i j =
      canonicalCompletedNativeGammaDslopeResidual
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
        (hhalf j) := by
  rw [canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix_apply,
    canonicalCompletedNativeGammaDslopeResidual_eq_radialBalanceResidual]

/-- The one-point microscope is the raw residual at the same shifted radial
sample; its fully scalar Pick expansion remains available from the preceding
radial-audit module. -/
theorem canonicalCompletedNativeGammaDslopeResidual_one_apply_zero
    (k : ℕ)
    (hhalf : ∀ i : Fin 1,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k 1 hhalf 0 0 =
      canonicalCompletedNativeGammaDslopeResidual
        (canonicalCompletedC3RadialTiltPoint k 0)
        (canonicalCompletedC3RadialTiltPoint k 0)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
        (hhalf 0) :=
  canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix_apply_eq_gammaDslopeResidual
    k 1 hhalf 0 0

/-- Every entry of the two-point microscope is the same named residual at
the corresponding pair.  No Hermitian reduction is used. -/
theorem canonicalCompletedNativeGammaDslopeResidual_two_apply
    (k : ℕ)
    (hhalf : ∀ i : Fin 2,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (i j : Fin 2) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k 2 hhalf i j =
      canonicalCompletedNativeGammaDslopeResidual
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
        (hhalf j) :=
  canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix_apply_eq_gammaDslopeResidual
    k 2 hhalf i j

/-- Every entry of the three-point microscope is the same named residual at
the corresponding pair.  This remains entrywise deliberately: no determinant
or positivity claim is introduced. -/
theorem canonicalCompletedNativeGammaDslopeResidual_three_apply
    (k : ℕ)
    (hhalf : ∀ i : Fin 3,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (i j : Fin 3) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k 3 hhalf i j =
      canonicalCompletedNativeGammaDslopeResidual
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
        (hhalf j) :=
  canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix_apply_eq_gammaDslopeResidual
    k 3 hhalf i j

end

end CarrySelfAdjointOperator

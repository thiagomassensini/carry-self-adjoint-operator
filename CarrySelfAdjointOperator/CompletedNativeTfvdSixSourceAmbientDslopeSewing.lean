import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceGammaDslopeResidualDecomposition
import CarrySelfAdjointOperator.CompletedC3AmbientRadialTiltSamplePositivity
import Mathlib.Tactic

/-!
# Full ambient Gram versus completed-native `dslope`

The raw six-source residual compares `dslope` only with the first
Gamma--correction cross channel.  The source-matched ambient carrier instead
has a four-channel Gram expansion.  This module records that expansion at the
boundary before any spectral separation is cancelled, and then defines the
only normalization-compatible ambient-versus-`dslope` residual.

No ambient sewing equality is assumed or proved here.  The resulting residual
is the full raw Gamma--Wronskian defect plus all three non-Gamma Gram channels,
divided only by the already canonical characteristic weight.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The three correction channels which must be added to the positive Gamma
Gram to recover the full source-matched ambient Gram.  The two cross terms
remain ordered, and the correction Gram is retained as a third term. -/
def canonicalCompletedC3FullAmbientGramCorrectionKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3GammaCorrectionKernel z w hz hw hwHalf +
    canonicalCompletedC3CorrectionGammaKernel z w hz hw hzHalf +
    canonicalCompletedC3CorrectionKernel z w hz hw hzHalf hwHalf

/-- Exact four-channel synthesis of the source-matched ambient Gram.  This
is a re-exposure of the pre-existing Hilbert expansion with the correction
sum named, not a claim that any channel vanishes or is Hermitian by itself. -/
theorem canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_fullCorrection
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientResponseKernel z w hzHalf hwHalf =
      canonicalCompletedC3PolarizedGammaKernel z w hz hw +
        canonicalCompletedC3FullAmbientGramCorrectionKernel
          z w hz hw hzHalf hwHalf := by
  rw [canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_threeCorrections
    z w hz hw hzHalf hwHalf]
  unfold canonicalCompletedC3FullAmbientGramCorrectionKernel
  ring

/-- A raw (therefore deliberately noncanonical) ambient comparison.  It is
useful only to locate the omitted channels inside the already raw residual
`dslope - GammaCorrection`; the normalized residual below is the comparison
appropriate to a genuine ambient Gram realization of `dslope`. -/
def canonicalCompletedC3RawAmbientDslopeResidual
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedNativePolarizedDslopeKernel z w -
    canonicalCompletedC3AmbientResponseKernel z w hzHalf hwHalf

/-- The channels that remain after subtracting only the first ordered
Gamma--correction cross term from the complete raw ambient Gram.  In
particular, this name keeps the reverse cross term and the correction Gram
visible. -/
def canonicalCompletedC3AmbientNonfirstCorrectionChannels
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3PolarizedGammaKernel z w hz hw +
    canonicalCompletedC3CorrectionGammaKernel z w hz hw hzHalf +
    canonicalCompletedC3CorrectionKernel z w hz hw hzHalf hwHalf

/-- Raw ambient provenance tree for the original residual.  The equality is
purely algebraic, but it is structurally informative: comparing with only
`KΓ,corr` leaves the Gamma Gram, the reverse ordered cross channel, and the
correction Gram unaccounted for.  It makes no normalization claim. -/
theorem canonicalCompletedNativeGammaDslopeResidual_eq_rawAmbientResidual_add_nonfirstChannels
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedNativeGammaDslopeResidual z w hz hw hwHalf =
      canonicalCompletedC3RawAmbientDslopeResidual z w hzHalf hwHalf +
        canonicalCompletedC3AmbientNonfirstCorrectionChannels
          z w hz hw hzHalf hwHalf := by
  unfold canonicalCompletedNativeGammaDslopeResidual
    canonicalCompletedC3RawAmbientDslopeResidual
    canonicalCompletedC3AmbientNonfirstCorrectionChannels
  rw [canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_threeCorrections
    z w hz hw hzHalf hwHalf]
  ring

/-- Boundary channel obtained from all three non-Gamma Gram terms.  The
separation factor is part of its definition, so this is meaningful without a
noncollision assumption. -/
def canonicalCompletedC3FullAmbientGramCorrectionBoundary
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  (w - conj z) * canonicalCompletedC3FullAmbientGramCorrectionKernel
    z w hz hw hzHalf hwHalf

/-- Boundary-first form of the full Gram synthesis.  In particular, the
ambient source-response boundary differs from the Gamma boundary by exactly
the ordered Gamma/correction, correction/Gamma, and correction/correction
channels together. -/
theorem canonicalCompletedC3AmbientBoundary_sub_gamma_eq_fullGramCorrection
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf -
        canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      canonicalCompletedC3FullAmbientGramCorrectionBoundary
        z w hz hw hzHalf hwHalf := by
  rw [canonicalCompletedC3AmbientBoundaryReadout_eq_kernel
      z w hz hw hzHalf hwHalf,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel z w hz hw]
  change
    (w - conj z) * canonicalCompletedC3AmbientResponseKernel z w hzHalf hwHalf -
        (w - conj z) * canonicalCompletedC3PolarizedGammaKernel z w hz hw = _
  rw [canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_fullCorrection
    z w hz hw hzHalf hwHalf]
  unfold canonicalCompletedC3FullAmbientGramCorrectionBoundary
  ring

/-- The full ambient boundary/Wronskian mismatch.  It is the old raw Gamma
defect plus the boundary form of all three omitted Gram channels.  This is an
identity, not a sewing premise. -/
theorem canonicalCompletedC3AmbientBoundary_sub_wronskian_eq_rawGamma_add_fullGramCorrection
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) :
    canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf -
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw +
        canonicalCompletedC3FullAmbientGramCorrectionBoundary
          z w hz hw hzHalf hwHalf := by
  have hboundary := canonicalCompletedC3AmbientBoundary_sub_gamma_eq_fullGramCorrection
    z w hz hw hzHalf hwHalf
  unfold canonicalCompletedC3RawGammaWronskianDefect
  calc
    canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf -
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z =
        (canonicalCompletedC3AmbientBoundaryReadout z w hzHalf hwHalf -
          canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw) +
        (canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z) := by ring
    _ = canonicalCompletedC3FullAmbientGramCorrectionBoundary
          z w hz hw hzHalf hwHalf +
        (canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
          completedGreenWronskian
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w z) := by rw [hboundary]
    _ = _ := by ring

/-- The normalization-compatible kernel residual for the full ambient
carrier.  Unlike the preceding raw six-source residual, it compares `dslope`
with the canonical `sqrt 2 * F` normalized ambient Gram. -/
def canonicalCompletedC3NormalizedAmbientDslopeResidual
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedNativePolarizedDslopeKernel z w -
    canonicalCompletedC3NormalizedAmbientResponseKernel z w hzHalf hwHalf

/-- Division-free boundary residual associated with the normalized ambient
kernel residual.  Its sign follows the old convention `ambient - dslope`. -/
def canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect
    (z w : ℂ)
    (hzHalf : 0 < (operatorHeightParameter z).re)
    (hwHalf : 0 < (operatorHeightParameter w).re) : ℂ :=
  canonicalCompletedC3NormalizedAmbientBoundaryReadout z w hzHalf hwHalf -
    (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w

/-- The normalized ambient boundary residual is the entire ambient
boundary/TFVD-Wronskian residual divided by the existing characteristic
weight.  The theorem keeps the TFVD completed Wronskian readout explicit so
the all-cutoff ledger provenance is not bypassed. -/
theorem canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect_eq_ambient_sub_tfvdWronskian_div_weight
    (M : ℕ) (z w : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect
        z w hzStrip.1 hwStrip.1 =
      (canonicalCompletedC3AmbientBoundaryReadout z w hzStrip.1 hwStrip.1 -
        canonicalC3BracketTfvdCompletedWronskianReadout M w z) /
        canonicalCompletedC3GammaCharacteristicWeight z w := by
  unfold canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect
    canonicalCompletedC3NormalizedAmbientBoundaryReadout
  rw [← canonicalC3BracketTfvdCompletedWronskianReadout_div_weight_eq_mul_dslope
    M hzStrip hwStrip hzF hwF hsep]
  ring

/-- Full channel form of the normalized ambient residual.  It says exactly
what would have to vanish to identify the geometrically constructed ambient
Gram with `dslope`: the old raw Gamma defect must cancel the complete ordered
three-channel Gram correction. -/
theorem canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect_eq_rawGamma_add_fullCorrection_div_weight
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect
        z w hzStrip.1 hwStrip.1 =
      (canonicalCompletedC3RawGammaWronskianDefect z w hz hw +
        canonicalCompletedC3FullAmbientGramCorrectionBoundary
          z w hz hw hzStrip.1 hwStrip.1) /
        canonicalCompletedC3GammaCharacteristicWeight z w := by
  rw [canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect_eq_ambient_sub_tfvdWronskian_div_weight
    M z w hzStrip hwStrip hzF hwF hsep]
  have hcompanion :
      (fun u : ℂ => -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
    M hwStrip hzStrip, hcompanion]
  rw [canonicalCompletedC3AmbientBoundary_sub_wronskian_eq_rawGamma_add_fullGramCorrection
    z w hz hw hzStrip.1 hwStrip.1]

/-- Kernel-level version of the preceding boundary equation.  Spectral
separation remains on the left, and the sign records the definition
`dslope - normalizedAmbient`. -/
theorem canonicalCompletedC3Separation_mul_normalizedAmbientDslopeResidual_eq_neg_rawGamma_add_fullCorrection_div_weight
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    (w - conj z) *
        canonicalCompletedC3NormalizedAmbientDslopeResidual
          z w hzStrip.1 hwStrip.1 =
      - ((canonicalCompletedC3RawGammaWronskianDefect z w hz hw +
        canonicalCompletedC3FullAmbientGramCorrectionBoundary
          z w hz hw hzStrip.1 hwStrip.1) /
        canonicalCompletedC3GammaCharacteristicWeight z w) := by
  have h := canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect_eq_rawGamma_add_fullCorrection_div_weight
    M z w hz hw hzStrip hwStrip hzF hwF hsep
  unfold canonicalCompletedC3NormalizedAmbientDslopeBoundaryDefect at h
  rw [canonicalCompletedC3NormalizedAmbientBoundaryReadout_eq_kernel
    z w hz hw hzStrip.1 hwStrip.1] at h
  unfold canonicalCompletedC3NormalizedAmbientDslopeResidual
  calc
    (w - conj z) *
          (canonicalCompletedNativePolarizedDslopeKernel z w -
            canonicalCompletedC3NormalizedAmbientResponseKernel
              z w hzStrip.1 hwStrip.1) =
        - ((w - conj z) *
          canonicalCompletedC3NormalizedAmbientResponseKernel
            z w hzStrip.1 hwStrip.1 -
          (w - conj z) * canonicalCompletedNativePolarizedDslopeKernel z w) := by ring
    _ = _ := congrArg Neg.neg h

/-! ## Radial microscopes -/

/-- The four raw kernels requested by the original shifted radial audit.
They are sampled on its grid with an explicit half-plane witness; this is
separate from the smaller ambient admissible grid used below for normalized
sewing. -/
def canonicalCompletedNativeRadialGammaGramSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3PolarizedGammaKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)

def canonicalCompletedNativeRadialGammaCorrectionSampleMatrix
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3GammaCorrectionKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
      (hhalf j)

def canonicalCompletedNativeRadialAmbientResponseSampleMatrix
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3AmbientResponseKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (hhalf i) (hhalf j)

/-- The ambient raw radial matrix contains the Gamma Gram, both ordered
cross channels, and the correction Gram.  This supplies the requested
entrywise four-channel microscope without silently identifying the reverse
cross channel with the first one. -/
theorem canonicalCompletedNativeRadialAmbientResponseSampleMatrix_apply_eq_fourChannels
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (i j : Fin N) :
    canonicalCompletedNativeRadialAmbientResponseSampleMatrix k N hhalf i j =
      canonicalCompletedNativeRadialGammaGramSampleMatrix k N i j +
        canonicalCompletedNativeRadialGammaCorrectionSampleMatrix k N hhalf i j +
        canonicalCompletedC3CorrectionGammaKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
          (hhalf i) +
        canonicalCompletedC3CorrectionKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
          (hhalf i) (hhalf j) := by
  exact canonicalCompletedC3AmbientResponseKernel_eq_gamma_add_threeCorrections
    (canonicalCompletedC3RadialTiltPoint k i)
    (canonicalCompletedC3RadialTiltPoint k j)
    (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
    (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
    (hhalf i) (hhalf j)

/-- The normalized ambient-minus-`dslope` residual matrix on the admissible
ambient grid.  This is the new residual required after the full ambient Gram
is tested; it makes no equality or PSD transfer claim. -/
def canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  canonicalCompletedNativeAmbientRadialDslopeSampleMatrix k N -
    canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix k N

/-- The old division-free normalized ambient defect is exactly separation
times the negative of the new kernel residual. -/
theorem canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eq_neg_separation_mul_residual
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedC3NormalizedAmbientRadialDslopeDefect k N i j =
      - (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
          k N i j := by
  unfold canonicalCompletedC3NormalizedAmbientRadialDslopeDefect
    canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
  rw [canonicalCompletedC3NormalizedAmbientRadialBoundarySampleMatrix_apply]
  simp only [Matrix.sub_apply,
    canonicalCompletedNativeAmbientRadialDslopeSampleMatrix,
    canonicalCompletedC3NormalizedAmbientRadialResponseSampleMatrix,
    Matrix.of_apply]
  ring

/-- On every fixed admissible radial entry, the new kernel residual is tied
to the pre-existing normalized four-channel correction ledger exactly after
the still-visible spectral separation is applied.  This is an eventual
identity only because characteristic nonvanishing near the Taylor center is
eventual; no pointwise ambient sewing has been inferred. -/
theorem canonicalCompletedC3NormalizedAmbientRadial_neg_separation_mul_residual_eventually_eq_fourChannelLedger
    (M N : ℕ) (i j : Fin N) :
    (fun k : ℕ =>
      - (canonicalCompletedC3AmbientRadialTiltPoint k N j -
          conj (canonicalCompletedC3AmbientRadialTiltPoint k N i)) *
        canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
          k N i j) =ᶠ[Filter.atTop]
      (fun k : ℕ =>
        canonicalCompletedC3NormalizedAmbientRadialCorrectionLedger k N i j) := by
  filter_upwards
    [canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eventually_eq_ledger
      M N i j] with k hk
  exact
    (canonicalCompletedC3NormalizedAmbientRadialDslopeDefect_eq_neg_separation_mul_residual
      k N i j).symm.trans hk

/-- Every entry in the one-point normalized ambient microscope is the
concrete `dslope - normalizedAmbientGram` residual at its admissible radial
point. -/
theorem canonicalCompletedC3NormalizedAmbientRadialDslopeResidual_one_apply_zero
    (k : ℕ) :
    canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
        k 1 0 0 =
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint k 1 0) -
      canonicalCompletedC3NormalizedAmbientResponseKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 1 0)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 1 0) := rfl

/-- Entrywise two-point normalized ambient microscope. -/
theorem canonicalCompletedC3NormalizedAmbientRadialDslopeResidual_two_apply
    (k : ℕ) (i j : Fin 2) :
    canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
        k 2 i j =
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 2 i)
        (canonicalCompletedC3AmbientRadialTiltPoint k 2 j) -
      canonicalCompletedC3NormalizedAmbientResponseKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 2 i)
        (canonicalCompletedC3AmbientRadialTiltPoint k 2 j)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 2 j) := rfl

/-- Entrywise three-point normalized ambient microscope; no determinant is
used, so all ordered correction information remains available. -/
theorem canonicalCompletedC3NormalizedAmbientRadialDslopeResidual_three_apply
    (k : ℕ) (i j : Fin 3) :
    canonicalCompletedC3NormalizedAmbientRadialDslopeResidualSampleMatrix
        k 3 i j =
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 3 i)
        (canonicalCompletedC3AmbientRadialTiltPoint k 3 j) -
      canonicalCompletedC3NormalizedAmbientResponseKernel
        (canonicalCompletedC3AmbientRadialTiltPoint k 3 i)
        (canonicalCompletedC3AmbientRadialTiltPoint k 3 j)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 3 i)
        (canonicalCompletedC3AmbientRadialTiltPoint_half_pos k 3 j) := rfl

end

end CarrySelfAdjointOperator

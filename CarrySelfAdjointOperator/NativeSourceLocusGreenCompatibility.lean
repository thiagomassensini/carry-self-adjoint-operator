import CarrySelfAdjointOperator.PureNativeBoundaryGreenSewing
import Mathlib.Tactic

/-!
# Native source-locus Green compatibility

This module gives the source-locus-specific comparison requested after the
pure native boundary chart was isolated.  It introduces no new state or map:
both charts are read from the canonical structured C3 state.  The Gamma chart
uses the structured green-port projection followed by the existing six-camera
Cauchy trace, while the scalar chart uses the normalized value/log-jet
projection.

The comparison is deliberately kept as one exact projection mismatch.  The
existing Gpre/cancellation theorem is exposed separately: it identifies the
glued Green defect with a vertical Wronskian, but it does not identify that
Wronskian with the Gamma projection on this source locus.  Thus this module
records the first unresolved channel without claiming it vanishes.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Green form obtained by the Gamma projection of the canonical structured
one-point C3 state.  The parameter proof only records that the Cauchy trace is
off the real axis. -/
def canonicalCompletedC3NativeSourceLocusGammaGreenForm
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalCompletedC3StructuredGammaBoundaryState z hz)
    (canonicalCompletedC3StructuredGammaBoundaryState w hw)

/-- Green form obtained by the normalized, undressed value/log-jet projection
of the same structured state. -/
def canonicalCompletedC3NativeSourceLocusScalarGreenForm
    (z w : ℂ) : ℂ :=
  canonicalCompletedC3StructuredNativeGreenForm z w

/-- The Gamma projection is the existing Gamma boundary state, with its
structured green-port ancestry made explicit. -/
theorem canonicalCompletedC3NativeSourceLocusGammaGreenForm_eq_canonical
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NativeSourceLocusGammaGreenForm z w hz hw =
      greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) := by
  unfold canonicalCompletedC3NativeSourceLocusGammaGreenForm
  rw [canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical,
    canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical]

/-- On the genuine strip the scalar projection is the undressed native pair
and hence its Green form is the previously named native scalar Green form. -/
theorem canonicalCompletedC3NativeSourceLocusScalarGreenForm_eq_nativeUndressed
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusScalarGreenForm z w =
      canonicalNativeUndressedGreenForm z w := by
  exact canonicalCompletedC3StructuredNativeGreenForm_eq_nativeUndressed
    hzStrip hwStrip

/-- The exact source-locus projection channel left after both charts are
pulled back to their common structured state.  No completion or Xi factor is
present. -/
def canonicalCompletedC3NativeSourceLocusProjectionMismatch
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3NativeSourceLocusGammaGreenForm z w hz hw -
    canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

/-- On the genuine strip this projection channel is exactly the pure native
boundary mismatch. -/
theorem canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw := by
  unfold canonicalCompletedC3NativeSourceLocusProjectionMismatch
    canonicalCompletedC3NativeSourceLocusGammaGreenForm
    canonicalCompletedC3NativeSourceLocusScalarGreenForm
  exact
    (canonicalCompletedC3PureNativeBoundaryMismatch_eq_sameStructuredGreenForm_sub
      z w hz hw hzStrip hwStrip).symm

/-- The same channel is the difference between the existing Gamma readout and
the undressed native Wronskian, in division-free form. -/
theorem canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_gammaReadout_sub_nativeWronskian
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        completedGreenWronskian
          nativeHeightScalar nativeHeightScalarBoundaryCompanion w z := by
  rw [canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative
    z w hz hw hzStrip hwStrip]
  exact canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
    z w hz hw

/-- Pointwise source-locus compatibility of the two native projections.  This
is a relation on the canonical family only; it is not a global intertwiner for
the six-camera packing. -/
def CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : Prop :=
  canonicalCompletedC3NativeSourceLocusGammaGreenForm z w hz hw =
    canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

/-- The relation above unfolds to equality of the two explicitly named
structured-state Green forms.  The pre-existing
`CanonicalCompletedC3SameStructuredBoundaryCompatibility` compares the Gamma
chart with the *dressed* scalar chart, so it is intentionally not reused here. -/
theorem canonicalCompletedC3NativeSourceLocusGreenCompatibilityAt_iff_structuredForms
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt z w hz hw ↔
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3StructuredGammaBoundaryState z hz)
          (canonicalCompletedC3StructuredGammaBoundaryState w hw) =
        canonicalCompletedC3StructuredNativeGreenForm z w := by
  unfold CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt
    canonicalCompletedC3NativeSourceLocusGammaGreenForm
    canonicalCompletedC3NativeSourceLocusScalarGreenForm
  rfl

/-- Global source-locus sewing is the pointwise relation for the canonical
structured family.  No map on the ambient C3 port space is requested. -/
def CanonicalCompletedC3NativeSourceLocusGreenCompatibility : Prop :=
  ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
    CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt z w hz hw

/-- Global source-locus compatibility is equivalent to vanishing of the one
explicit projection channel. -/
theorem canonicalCompletedC3NativeSourceLocusGreenCompatibility_iff_mismatch_zero :
    CanonicalCompletedC3NativeSourceLocusGreenCompatibility ↔
      ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
        canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw = 0 := by
  constructor
  · intro h z w hz hw
    have hpoint := h z w hz hw
    unfold CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt at hpoint
    unfold canonicalCompletedC3NativeSourceLocusProjectionMismatch
    exact sub_eq_zero.mpr hpoint
  · intro h z w hz hw
    unfold CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt
    have hzero := h z w hz hw
    unfold canonicalCompletedC3NativeSourceLocusProjectionMismatch at hzero
    exact sub_eq_zero.mp hzero

/-- On the genuine strip the source-locus relation is exactly the pure native
sewing relation, pair by pair. -/
theorem canonicalCompletedC3NativeSourceLocusGreenCompatibilityAt_iff_pureNative
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt z w hz hw ↔
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3GammaBoundaryState z hz)
          (canonicalCompletedC3GammaBoundaryState w hw) =
        canonicalNativeUndressedGreenForm z w := by
  unfold CanonicalCompletedC3NativeSourceLocusGreenCompatibilityAt
  rw [canonicalCompletedC3NativeSourceLocusGammaGreenForm_eq_canonical,
    canonicalCompletedC3NativeSourceLocusScalarGreenForm_eq_nativeUndressed
      hzStrip hwStrip]

/-- The cancellation carrier remains the existing finite response/return
carrier.  Its glued boundary defect is a vertical Wronskian, so provenance
coordinates cancel inside that Green defect without being discarded. -/
theorem canonicalCompletedC3NativeSourceLocusCancellation_greenDefect_eq_verticalWronskian
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (S : Finset NativeGpreBoundaryContext)
    (x y : CanonicalCompletedC3PureNativeCancellationBoundaryCarrier) :
    inner ℂ
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace y)
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace x) -
      inner ℂ
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).valueTrace y)
        ((canonicalCompletedC3CancellationNativeBoundaryPencil hbase S).fluxTrace x) =
      carryWeightedVerticalBoundaryWronskian
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalCompletedC3CancellationBoundaryReconstruction x)
        (canonicalCompletedC3CancellationBoundaryReconstruction y) :=
  canonicalCompletedC3PureNativeCancellation_greenDefect_eq_verticalWronskian
    hbase S x y

/-- The source-locus mismatch inherits the skew-Hermitian symmetry of the
existing pure native residual. -/
theorem canonicalCompletedC3NativeSourceLocusProjectionMismatch_skew
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch w z hw hz =
      -conj (canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw) := by
  rw [canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative
      z w hz hw hzStrip hwStrip,
    canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative
      w z hw hz hwStrip hzStrip]
  exact canonicalCompletedC3PureNativeBoundaryMismatch_skew z w hz hw

/-- On the diagonal, only the real part of the source-locus mismatch is
forced to vanish; no zero conclusion is inferred. -/
theorem canonicalCompletedC3NativeSourceLocusProjectionMismatch_diagonal_re_eq_zero
    (z : ℂ) (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    (canonicalCompletedC3NativeSourceLocusProjectionMismatch z z hz hz).re = 0 := by
  rw [canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative
    z z hz hz hzStrip hzStrip]
  exact canonicalCompletedC3PureNativeBoundaryMismatch_diagonal_re_eq_zero z hz

end

end CarrySelfAdjointOperator

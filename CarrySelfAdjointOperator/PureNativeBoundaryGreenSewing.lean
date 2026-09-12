import CarrySelfAdjointOperator.NativeBoundaryArchimedeanDressingSeparation
import CarrySelfAdjointOperator.CompletedC3SameStructuredBoundaryState
import CarrySelfAdjointOperator.CompletedNativeCancellationBoundarySewing
import Mathlib.Tactic

/-!
# Pure native boundary Green sewing

This module isolates the boundary-chart comparison which remains after the
archimedean product dressing has been separated.  The primary residual is
defined directly as the Green form of the canonical Gamma boundary state minus
the Green form of the undressed native scalar pair.  Consequently its
 definition contains no xi/completion factor.

The normalized value and log-jet coordinates of the cutoff-one structured
TFVD state are retained as the undressed scalar projection.  On the genuine
strip they are identified with `(-N', N)` by the existing finite-tail
crosswalks.  The Gamma projection and this scalar projection therefore have a
common structured ancestor, but this file does not assume that the two Green
forms agree.

The cancellation/Gpre carrier is exposed through wrappers around the existing
reconstruction and glued-boundary Green-defect theorem.  This records the
positive geometric carrier used by the cancellation route without turning its
Green defect into a scalar sewing assertion.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The undressed scalar projection of the canonical cutoff-one structured
TFVD state.  The order is `(log-jet,value)`, the order used by `greenForm` and
by `canonicalNativeUndressedScalarBoundaryPair`.  No archimedean factor is
read here. -/
def canonicalCompletedC3StructuredNativeScalarBoundaryPair
    (z : ℂ) : ℂ × ℂ :=
  (canonicalC3BracketTfvdNormalizedLogJetReadout 1 z,
    canonicalC3BracketTfvdNormalizedValueReadout 1 z)

/-- The structured native scalar projection is exactly the previously named
undressed native boundary pair on the genuine strip. -/
theorem canonicalCompletedC3StructuredNativeScalarBoundaryPair_eq_nativeUndressed
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3StructuredNativeScalarBoundaryPair z =
      canonicalNativeUndressedScalarBoundaryPair z := by
  apply Prod.ext
  · dsimp [canonicalCompletedC3StructuredNativeScalarBoundaryPair,
      canonicalNativeUndressedScalarBoundaryPair]
    rw [canonicalC3BracketTfvdNormalizedLogJetReadout_eq_cutoff,
      canonicalCompletedC3FiniteEnrichedTfvdNormalizedLogJetTailReadout_eq_completed
        1 hzStrip,
      canonicalCompletedC3EnrichedTfvdNormalizedLogJetTailReadout_eq_nativeCompanion
        hzStrip]
  · dsimp [canonicalCompletedC3StructuredNativeScalarBoundaryPair,
      canonicalNativeUndressedScalarBoundaryPair]
    rw [canonicalC3BracketTfvdNormalizedValueReadout_eq_cutoff,
      canonicalCompletedC3FiniteEnrichedTfvdNormalizedValueTailReadout_eq_completed
        1 hzStrip,
      canonicalCompletedC3EnrichedTfvdNormalizedValueTailReadout_eq_nativeHeightScalar
        hzStrip]

/-- Green form of the undressed scalar projection of the same structured state.
It is deliberately defined without the archimedean completion factor. -/
def canonicalCompletedC3StructuredNativeGreenForm (z w : ℂ) : ℂ :=
  greenForm (𝕜 := ℂ)
    (canonicalCompletedC3StructuredNativeScalarBoundaryPair z)
    (canonicalCompletedC3StructuredNativeScalarBoundaryPair w)

/-- On the genuine strip the structured native Green form is the previously
identified native undressed Green form. -/
theorem canonicalCompletedC3StructuredNativeGreenForm_eq_nativeUndressed
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3StructuredNativeGreenForm z w =
      canonicalNativeUndressedGreenForm z w := by
  unfold canonicalCompletedC3StructuredNativeGreenForm
  rw [canonicalCompletedC3StructuredNativeScalarBoundaryPair_eq_nativeUndressed
        hzStrip,
    canonicalCompletedC3StructuredNativeScalarBoundaryPair_eq_nativeUndressed
        hwStrip]
  rfl

/-- Pure native boundary mismatch.  This is the difference between the
canonical Gamma Green form and the undressed native scalar Green form.  In
particular, no `nativeXiCompletionFactor` occurs in this definition. -/
def canonicalCompletedC3PureNativeBoundaryMismatch
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  greenForm (𝕜 := ℂ)
      (canonicalCompletedC3GammaBoundaryState z hz)
      (canonicalCompletedC3GammaBoundaryState w hw) -
    canonicalNativeUndressedGreenForm z w

/-- The pure mismatch is definitionally the earlier undressed Gamma/native
residual.  This theorem is an audit alias, not a new identification. -/
theorem canonicalCompletedC3PureNativeBoundaryMismatch_eq_existing
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw =
      canonicalC3GammaNativeUndressedBoundaryGreenMismatch z w hz hw := by
  rfl

/-- On the genuine strip both sides of the pure mismatch are projections of
one cutoff-one structured state. -/
theorem canonicalCompletedC3PureNativeBoundaryMismatch_eq_sameStructuredGreenForm_sub
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw =
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3StructuredGammaBoundaryState z hz)
          (canonicalCompletedC3StructuredGammaBoundaryState w hw) -
        canonicalCompletedC3StructuredNativeGreenForm z w := by
  unfold canonicalCompletedC3PureNativeBoundaryMismatch
  rw [← canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical z hz,
    ← canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical w hw,
    canonicalCompletedC3StructuredNativeGreenForm_eq_nativeUndressed
      hzStrip hwStrip]

/-- Division-free Wronskian spelling of the pure mismatch. -/
theorem canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        completedGreenWronskian
          nativeHeightScalar nativeHeightScalarBoundaryCompanion w z := by
  unfold canonicalCompletedC3PureNativeBoundaryMismatch
  rw [canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_boundaryGreenForm,
    canonicalNativeUndressedGreenForm_eq_nativeWronskian]

/-- The pure mismatch is the only source-locus compatibility condition needed
for the two undressed boundary charts. -/
def CanonicalCompletedC3PureNativeBoundaryGreenSewing : Prop :=
  ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
    greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) =
      canonicalNativeUndressedGreenForm z w

/-- Pure native sewing is equivalent to pointwise vanishing of the explicitly
defined pure mismatch. -/
theorem canonicalCompletedC3PureNativeBoundaryGreenSewing_iff_mismatch_zero :
    CanonicalCompletedC3PureNativeBoundaryGreenSewing ↔
      ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
        canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0 := by
  constructor
  · intro h z w hz hw
    unfold canonicalCompletedC3PureNativeBoundaryMismatch
    rw [h z w hz hw]
    exact sub_self _
  · intro h z w hz hw
    have hzero := h z w hz hw
    unfold canonicalCompletedC3PureNativeBoundaryMismatch at hzero
    exact sub_eq_zero.mp hzero

/-- On the genuine strip the pure sewing gate is exactly compatibility of the
two projections of the common structured state. -/
theorem canonicalCompletedC3PureNativeBoundaryGreenSewing_iff_sameStructuredNativeGreenCompatibility
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (greenForm (𝕜 := ℂ)
        (canonicalCompletedC3GammaBoundaryState z hz)
        (canonicalCompletedC3GammaBoundaryState w hw) =
      canonicalNativeUndressedGreenForm z w) ↔
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3StructuredGammaBoundaryState z hz)
          (canonicalCompletedC3StructuredGammaBoundaryState w hw) =
        canonicalCompletedC3StructuredNativeGreenForm z w := by
  rw [← canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical z hz,
    ← canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical w hw,
    canonicalCompletedC3StructuredNativeGreenForm_eq_nativeUndressed
      hzStrip hwStrip]

/-- The Green form is skew-Hermitian in the two arguments, hence so is the
pure native mismatch.  This is an exact structural property of the residual. -/
theorem canonicalCompletedC3PureNativeBoundaryMismatch_skew
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3PureNativeBoundaryMismatch w z hw hz =
      -conj (canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw) := by
  unfold canonicalCompletedC3PureNativeBoundaryMismatch
  unfold canonicalNativeUndressedGreenForm
  rw [greenForm_skew
      (canonicalCompletedC3GammaBoundaryState z hz)
      (canonicalCompletedC3GammaBoundaryState w hw),
    greenForm_skew
      (canonicalNativeUndressedScalarBoundaryPair z)
      (canonicalNativeUndressedScalarBoundaryPair w)]
  change
    -(starRingEnd ℂ)
          (greenForm (𝕜 := ℂ)
            (canonicalCompletedC3GammaBoundaryState z hz)
            (canonicalCompletedC3GammaBoundaryState w hw)) -
        (-(starRingEnd ℂ)
          (greenForm (𝕜 := ℂ)
            (canonicalNativeUndressedScalarBoundaryPair z)
            (canonicalNativeUndressedScalarBoundaryPair w))) =
      -(starRingEnd ℂ)
        (greenForm (𝕜 := ℂ)
            (canonicalCompletedC3GammaBoundaryState z hz)
            (canonicalCompletedC3GammaBoundaryState w hw) -
          greenForm (𝕜 := ℂ)
            (canonicalNativeUndressedScalarBoundaryPair z)
            (canonicalNativeUndressedScalarBoundaryPair w))
  rw [map_sub]
  ring

/-- On the diagonal the pure mismatch has zero real part. -/
theorem canonicalCompletedC3PureNativeBoundaryMismatch_diagonal_re_eq_zero
    (z : ℂ) (hz : z.im ≠ 0) :
    (canonicalCompletedC3PureNativeBoundaryMismatch z z hz hz).re = 0 := by
  have hskew := canonicalCompletedC3PureNativeBoundaryMismatch_skew z z hz hz
  have hre := congrArg Complex.re hskew
  have hre' :
      (canonicalCompletedC3PureNativeBoundaryMismatch z z hz hz).re =
        -(canonicalCompletedC3PureNativeBoundaryMismatch z z hz hz).re := by
    simpa using hre
  linarith

/-- Post-hoc audit decomposition: once the dressed scalar chart is compared
with the undressed one, the old raw Gamma--Wronskian defect is the pure native
mismatch minus the full archimedean chart-transport correction.  The primary
pure mismatch above does not depend on this correction. -/
theorem canonicalCompletedC3PureNativeBoundaryMismatch_eq_rawDefect_add_archimedeanTransportCorrection
    {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw +
        canonicalArchimedeanBoundaryGreenTransportCorrection z w := by
  have h :=
    canonicalCompletedC3RawGammaWronskianDefect_eq_gammaNativeMismatch_sub_archimedeanTransportCorrection
      hz hw hzStrip hwStrip
  rw [canonicalCompletedC3PureNativeBoundaryMismatch_eq_existing]
  rw [h]
  ring

/-- The finite cancellation state is the already existing response/return
carrier.  This alias keeps the pure-native route visibly tied to its geometric
source without changing that carrier. -/
abbrev CanonicalCompletedC3PureNativeCancellationBoundaryCarrier :=
  CanonicalCompletedC3CancellationBoundaryCarrier

/-- The cancellation carrier reconstructs the finite TFVD prefix exactly. -/
theorem canonicalCompletedC3PureNativeCancellationBoundaryState_reconstructs
    {base : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (s : ℂ) (hs : 0 < s.re) :
    canonicalCompletedC3CancellationBoundaryReconstruction
        (canonicalCompletedC3CancellationBoundaryState hbase s hs) =
      canonicalCompletedC3DirichletGradientState s hs :=
  canonicalCompletedC3CancellationBoundaryState_reconstructs hbase s hs

/-- The Gpre glued-boundary provenance coordinates cancel inside the Green
form, leaving exactly the vertical Wronskian of the reconstructed states. -/
theorem canonicalCompletedC3PureNativeCancellation_greenDefect_eq_verticalWronskian
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
  canonicalCompletedC3CancellationNativeBoundaryPencil_greenDefect_eq_verticalWronskian
    hbase S x y

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedC3GreenInverseSewingProbe
import CarrySelfAdjointOperator.NativeSourceLocusGreenCompatibility
import Mathlib.Tactic

/-!
# Native Green-inverse trace sewing

This module records the native (undressed) trace target for the canonical
completed C3 Green inverse. The defect operator and its source are not
changed: a candidate is still a point of RealifiedLogarithmicDomain solving
the same canonical right-inverse equation. Resolvent uniqueness therefore
forces every such candidate to be the Gamma state.

The only new field is the trace target
  candidate boundary readout =
    completedGreenWronskian nativeHeightScalar
      nativeHeightScalarBoundaryCompanion.
The resulting structure is characterized exactly by the already isolated
pure native projection mismatch. This is deliberately a criterion rather
than an unproved existence assertion: the existing cancellation/Gpre carrier
identifies its Green defect with a vertical Wronskian, but the vertical-to-
native-scalar trace identification is a separate, still explicit gate.

No Xi/archimedean factor, Hankel, Jacobi, HP, camera limit, or new resolvent
state is introduced here.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- A canonical C3 Green right inverse equipped with the undressed native
scalar boundary target. The target is the vertical/native Wronskian of
nativeHeightScalar; it contains no archimedean completion factor. -/
structure CanonicalCompletedC3NativeGreenInverseTraceRealization
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) where
  candidateZ : RealifiedLogarithmicDomain
  candidateW : RealifiedLogarithmicDomain
  rightInverseZ : CanonicalCompletedC3GreenRightInverseAt z candidateZ
  rightInverseW : CanonicalCompletedC3GreenRightInverseAt w candidateW
  boundaryReadout :
    canonicalCompletedC3CandidateResolventBoundaryReadout
        z w candidateZ candidateW =
      completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion w z

namespace CanonicalCompletedC3NativeGreenInverseTraceRealization

/-- Every native trace realization uses the unique Gamma right inverse at the
first source. -/
theorem candidateZ_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw) :
    realization.candidateZ =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
  canonicalCompletedC3GreenRightInverseAt_eq_gamma hz
    realization.rightInverseZ

/-- Every native trace realization uses the unique Gamma right inverse at the
second source. -/
theorem candidateW_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw) :
    realization.candidateW =
      carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w) :=
  canonicalCompletedC3GreenRightInverseAt_eq_gamma hw
    realization.rightInverseW

/-- The native trace target forces the Gamma boundary readout to equal the
native undressed Wronskian. -/
theorem gammaBoundaryReadout_eq_nativeWronskian
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw =
      completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion w z := by
  have hread := realization.boundaryReadout
  rw [realization.candidateZ_eq_gamma, realization.candidateW_eq_gamma,
    canonicalCompletedC3CandidateResolventBoundaryReadout_gamma_eq] at hread
  exact hread

/-- Consequently any native trace realization kills precisely the previously
isolated pure native source-locus mismatch. -/
theorem pureNativeBoundaryMismatch_eq_zero
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw) :
    canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0 := by
  have hread := realization.gammaBoundaryReadout_eq_nativeWronskian
  have hdiff :=
    canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
      z w hz hw
  rw [hdiff, hread]
  exact sub_self _

/-- On the genuine strip the same realization also kills the named
source-locus projection mismatch. -/
theorem nativeSourceLocusProjectionMismatch_eq_zero
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw = 0 := by
  rw [canonicalCompletedC3NativeSourceLocusProjectionMismatch_eq_pureNative
    z w hz hw hzStrip hwStrip]
  exact realization.pureNativeBoundaryMismatch_eq_zero

end CanonicalCompletedC3NativeGreenInverseTraceRealization

/-- The canonical TFVD-resolved domain vectors satisfy the right-inverse part
of the native realization. The trace field is intentionally left as the
native mismatch gate. -/
def canonicalCompletedC3NativeGreenInverseTraceRealizationOf
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hmismatch :
      canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0) :
    CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw where
  candidateZ := canonicalCompletedC3TfvdResolventDomainVector z hz
  candidateW := canonicalCompletedC3TfvdResolventDomainVector w hw
  rightInverseZ :=
    canonicalCompletedC3TfvdResolventDomainVector_greenRightInverse z hz
  rightInverseW :=
    canonicalCompletedC3TfvdResolventDomainVector_greenRightInverse w hw
  boundaryReadout := by
    rw [canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout]
    have hdiff :=
      canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
        z w hz hw
    rw [hdiff] at hmismatch
    exact sub_eq_zero.mp hmismatch

/-- Conversely, the canonical TFVD-resolved pair has the native target exactly
when the pure native mismatch vanishes. -/
theorem canonicalCompletedC3TfvdNativeBoundaryReadout_iff_mismatch_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3TfvdResolventDomainVector w hw) =
      completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion w z ↔
      canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0 := by
  constructor
  · intro hread
    have hgamma :=
      canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout
        z w hz hw
    have hdiff :=
      canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
        z w hz hw
    rw [hgamma] at hread
    rw [hdiff]
    exact sub_eq_zero.mpr hread
  · intro hmismatch
    exact
      (canonicalCompletedC3NativeGreenInverseTraceRealizationOf
        z w hz hw hmismatch).boundaryReadout

/-- Existence of the native trace realization is equivalent to the exact pure
native mismatch gate. No alternative Green state can make this proposition
easier, because both candidates are already forced to be Gamma. -/
theorem canonicalCompletedC3NativeGreenInverseTraceRealization_nonempty_iff_mismatch_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Nonempty
        (CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw) ↔
      canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0 := by
  constructor
  · rintro ⟨realization⟩
    have hread := realization.gammaBoundaryReadout_eq_nativeWronskian
    have hdiff :=
      canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
        z w hz hw
    rw [hdiff, hread]
    exact sub_self _
  · intro hmismatch
    exact ⟨canonicalCompletedC3NativeGreenInverseTraceRealizationOf
      z w hz hw hmismatch⟩

/-- The source-locus trace relation can be stated directly on the canonical
Gamma candidates. This is a family-specific relation, not a global map on the
C3 port carrier. -/
def CanonicalCompletedC3NativeGreenTraceRelationAt
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : Prop :=
  canonicalCompletedC3CandidateResolventBoundaryReadout z w
      (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z))
      (carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w)) =
    completedGreenWronskian
      nativeHeightScalar nativeHeightScalarBoundaryCompanion w z

/-- The canonical source-locus trace relation is equivalent to the pure native
mismatch gate. -/
theorem canonicalCompletedC3NativeGreenTraceRelationAt_iff_mismatch_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    CanonicalCompletedC3NativeGreenTraceRelationAt z w hz hw ↔
      canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0 := by
  unfold CanonicalCompletedC3NativeGreenTraceRelationAt
  rw [canonicalCompletedC3CandidateResolventBoundaryReadout_gamma_eq]
  have hdiff :=
    canonicalCompletedC3PureNativeBoundaryMismatch_eq_gammaReadout_sub_nativeWronskian
      z w hz hw
  constructor
  · intro hread
    rw [hdiff]
    exact sub_eq_zero.mpr hread
  · intro hmismatch
    rw [hdiff] at hmismatch
    exact sub_eq_zero.mp hmismatch

/-- The canonical TFVD/Gamma state remains the unique right inverse; this
wrapper records the fact in the native trace vocabulary. -/
theorem canonicalCompletedC3NativeTrace_candidate_eq_gamma
    {z : ℂ} (hz : z.im ≠ 0)
    {candidate : RealifiedLogarithmicDomain}
    (hgreen : CanonicalCompletedC3GreenRightInverseAt z candidate) :
    candidate =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
  canonicalCompletedC3GreenRightInverseAt_eq_gamma hz hgreen

/-- The finite cancellation carrier already preserves the Green response,
boundary return, provenance, and TFVD reconstruction. Its glued Green defect
is the vertical Wronskian; this is the exact geometric input still available
for the unresolved vertical-to-native-scalar trace step. -/
theorem canonicalCompletedC3NativeTrace_cancellation_greenDefect_eq_verticalWronskian
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

/-- Global existence of the native trace realization is the all-pairs
source-locus trace sewing statement. -/
def CanonicalCompletedC3NativeGreenInverseTraceRealizationExists : Prop :=
  ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
    Nonempty
      (CanonicalCompletedC3NativeGreenInverseTraceRealization z w hz hw)

/-- The global native trace-realization gate is exactly the all-pairs pure
native mismatch gate. -/
theorem canonicalCompletedC3NativeGreenInverseTraceRealizationExists_iff_mismatch_zero :
    CanonicalCompletedC3NativeGreenInverseTraceRealizationExists ↔
      ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
        canonicalCompletedC3PureNativeBoundaryMismatch z w hz hw = 0 := by
  constructor
  · intro h z w hz hw
    rcases h z w hz hw with ⟨realization⟩
    exact realization.pureNativeBoundaryMismatch_eq_zero
  · intro h z w hz hw
    exact ⟨canonicalCompletedC3NativeGreenInverseTraceRealizationOf
      z w hz hw (h z w hz hw)⟩


end

end CarrySelfAdjointOperator

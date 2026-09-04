import CarrySelfAdjointOperator.CompletedC3BoundaryRelationSewingBridge
import CarrySelfAdjointOperator.CanonicalC3GlobalCameraBoundaryBridge
import CarrySelfAdjointOperator.CompletedC3CompressedLogarithmicOperator
import Mathlib.Tactic

/-!
# Same structured C3 state behind the Gamma and scalar boundary charts

The completed C3 sewing has two boundary descriptions which were historically
constructed in different parts of the repository:

* the six-camera source entering the source-extended Gamma/Weyl relation;
* the completed scalar trace `(F,-F')` entering the Wronskian.

This file identifies both as projections of the very same cutoff-one
`CanonicalC3BracketTfvdCompletionState`.  The Green-port projection is packed
faithfully into the six native cameras and then used by the Gamma field.  The
value/log-jet projection is completed and oriented as `(-F',F)`.

The point is not to assume their Green forms agree.  Instead, the remaining
sewing defect is rewritten as the difference of the two Green forms attached
to these two projections of one structured state.

We also retain one older no-go theorem, but only in its exact scope: the bare
six-camera coordinate packing is not, by itself, an intrinsic Green
intertwiner on the whole C3 port carrier.  This predates and does not rule out
the later additive--multiplicative/projective-valve structure, nor any
source-locus-specific enriched boundary transform built from it.  In
particular, the present target is a structured boundary-chart identification,
not a claim that raw packing preserves the Green form globally.
-/

open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The canonical one-point structured C3 state from which both boundary
charts are projected. -/
def canonicalCompletedC3StructuredOnePointState
    (z : ℂ) : CanonicalC3BracketTfvdCompletionState 1 :=
  canonicalC3BracketTfvdCompletionState 1 (operatorHeightParameter z)

/-- The scalar boundary chart of the structured state, oriented as
`(Psi,F)=(-F',F)` rather than the internal `(F,Psi)` storage order. -/
def canonicalCompletedC3StructuredScalarBoundaryPair
    (z : ℂ) : ℂ × ℂ :=
  let trace :=
    (canonicalCompletedC3StructuredOnePointState z).completedTraceAt z
  (trace.2, trace.1)

/-- The Green-port chart of the same structured state, faithfully packed into
the six all-bases cameras used by the Gamma field. -/
def canonicalCompletedC3StructuredGammaSource
    (z : ℂ) : RealifiedCameraComplexification :=
  canonicalC3SixCameraSourceMap
    (canonicalCompletedC3StructuredOnePointState z).greenPort

/-- The completed scalar projection of the structured state is exactly the
existing canonical scalar boundary pair `(-F',F)`. -/
theorem canonicalCompletedC3StructuredScalarBoundaryPair_eq_canonical
    {z : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3StructuredScalarBoundaryPair z =
      canonicalCompletedC3ScalarBoundaryPair z := by
  unfold canonicalCompletedC3StructuredScalarBoundaryPair
    canonicalCompletedC3StructuredOnePointState
  rw [CanonicalC3BracketTfvdCompletionState.completedTraceAt_canonical,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime 1 hzStrip]
  simp [canonicalCompletedC3ScalarBoundaryPair,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

/-- The packed Green-port projection of the structured state is exactly the
canonical six-camera source already fed into the Gamma resolvent. -/
theorem canonicalCompletedC3StructuredGammaSource_eq_canonical
    (z : ℂ) :
    canonicalCompletedC3StructuredGammaSource z =
      canonicalCompletedC3SixCameraSource z := by
  unfold canonicalCompletedC3StructuredGammaSource
    canonicalCompletedC3StructuredOnePointState
    canonicalCompletedC3SixCameraSource
  rw [canonicalC3BracketTfvdCompletionState_greenPort_eq_bracket,
    ← canonicalCompletedOperatorC3State_eq_greenBoundaryPair]

/-- Gamma boundary state obtained by first projecting the same structured C3
state to its six-camera Green source and then applying the canonical Cauchy
boundary trace. -/
def canonicalCompletedC3StructuredGammaBoundaryState
    (z : ℂ) (hz : z.im ≠ 0) : CanonicalCompletedC3GammaBoundaryCarrier :=
  (canonicalCompletedC3StructuredGammaSource z,
    carryGammaComplexCauchyReadout z hz
      (canonicalCompletedC3StructuredGammaSource z))

/-- The structured-state Gamma boundary chart is exactly the previously
constructed canonical Gamma boundary state. -/
theorem canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3StructuredGammaBoundaryState z hz =
      canonicalCompletedC3GammaBoundaryState z hz := by
  unfold canonicalCompletedC3StructuredGammaBoundaryState
    canonicalCompletedC3GammaBoundaryState
  rw [canonicalCompletedC3StructuredGammaSource_eq_canonical]

/-- Pointwise compatibility of the two boundary charts of the same structured
C3 state.  This is deliberately source-locus-specific; it does not ask for a
symplectic map on the whole six-camera Hilbert space. -/
def CanonicalCompletedC3SameStructuredBoundaryCompatibility
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : Prop :=
  greenForm (𝕜 := ℂ)
      (canonicalCompletedC3StructuredGammaBoundaryState z hz)
      (canonicalCompletedC3StructuredGammaBoundaryState w hw) =
    greenForm (𝕜 := ℂ)
      (canonicalCompletedC3StructuredScalarBoundaryPair z)
      (canonicalCompletedC3StructuredScalarBoundaryPair w)

/-- On the open strip, the raw Gamma--Wronskian defect is literally the
difference of the two Green forms obtained from the same structured C3
states. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_sameStructuredGreenForm_sub
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3StructuredGammaBoundaryState z hz)
          (canonicalCompletedC3StructuredGammaBoundaryState w hw) -
        greenForm (𝕜 := ℂ)
          (canonicalCompletedC3StructuredScalarBoundaryPair z)
          (canonicalCompletedC3StructuredScalarBoundaryPair w) := by
  rw [canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical,
    canonicalCompletedC3StructuredGammaBoundaryState_eq_canonical,
    canonicalCompletedC3StructuredScalarBoundaryPair_eq_canonical hzStrip,
    canonicalCompletedC3StructuredScalarBoundaryPair_eq_canonical hwStrip]
  exact
    canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub
      z w hz hw

/-- The same-state boundary compatibility is exactly the vanishing of the
existing raw sewing defect.  No global symplectic extension is required. -/
theorem canonicalCompletedC3SameStructuredBoundaryCompatibility_iff_rawDefect_zero
  (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
  (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
  (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
  CanonicalCompletedC3SameStructuredBoundaryCompatibility z w hz hw ↔
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 := by
  unfold CanonicalCompletedC3SameStructuredBoundaryCompatibility
  rw [canonicalCompletedC3RawGammaWronskianDefect_eq_sameStructuredGreenForm_sub
    z w hz hw hzStrip hwStrip]
  constructor
  · intro h
    exact sub_eq_zero.mpr h
  · intro h
    exact sub_eq_zero.mp h

/-- A pointwise same-state boundary compatibility closes the already
formalized normalized Gamma--`dslope` sewing at that pair. -/
theorem CanonicalCompletedC3SameStructuredBoundaryCompatibility.normalizedGammaKernel_eq_dslope
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (h : CanonicalCompletedC3SameStructuredBoundaryCompatibility z w hz hw)
    (M : ℕ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
      canonicalCompletedNativePolarizedDslopeKernel z w := by
  apply
    (canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
      M z w hz hw hzStrip hwStrip hzF hwF hsep).2
  have hzero : canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 :=
    (canonicalCompletedC3SameStructuredBoundaryCompatibility_iff_rawDefect_zero
      z w hz hw hzStrip hwStrip).1 h
  unfold canonicalCompletedC3RawGammaWronskianDefect at hzero
  exact sub_eq_zero.mp hzero

/-- Bare-packing no-go only: the faithful six-camera coordinate packing is not
itself an intrinsic Green intertwiner on the whole C3 port carrier.  This does
not exclude a later valve-enriched or source-relation boundary transform. -/
theorem no_global_intrinsicGreenIntertwiner_from_sixCameraPacking :
    ¬ (∀ x y : FiniteC3GreenPortCarrier 3,
      (greenForm (𝕜 := ℂ) x y).re =
        realifiedGreenSkew
          (canonicalC3SixCameraSourceMap x)
          (canonicalC3SixCameraSourceMap y)) := by
  intro h
  rcases canonicalC3SixCameraSourceMap_not_intrinsicGreenIntertwiner with
    ⟨x, y, hne⟩
  exact hne (h x y)

end

end CarrySelfAdjointOperator

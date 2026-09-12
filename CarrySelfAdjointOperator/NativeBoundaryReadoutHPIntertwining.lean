import CarrySelfAdjointOperator.CompletedC3GreenInverseSewingProbe
import CarrySelfAdjointOperator.CompletedC3BoundaryRelationSewingBridge
import CarrySelfAdjointOperator.CompletedC3AmbientBoundaryReadout
import CarrySelfAdjointOperator.NativeLogEvolution
import Mathlib.Tactic

/-!
# Native boundary readout and the HP seam

The native carry derivation first produces the completed characteristic and
its logarithmic moments.  It does not provide an undamped cyclic vector in
the ordinary `ℓ²` logarithmic Hilbert space: the coordinatewise source has
harmonic squared mass.  The legitimate native response is therefore the
off-axis maximal-domain resolvent state, with its source retained as boundary
data.

This file records that boundary realization without introducing a new
positive operator or a moment-fitted carrier.  The TFVD source is resolved by
the existing logarithmic resolvent, its defect equation is proved by the
existing resolvent identity, and uniqueness identifies it with the canonical
Gamma state.  The resulting two-point boundary readout is then compared with
the completed `(F,-F')` Wronskian.

The comparison is exact and exposes the only remaining scalar seam: the
already existing raw Gamma--Wronskian defect.  Consequently this module does
not claim the boundary Green sewing, the normalized `dslope` Gram, or an
unconditional HP certificate.  Those implications are imported only through
their existing equivalences.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## The native boundary source and its two relation charts -/

/-- The native source response used by the completed TFVD construction.

This is an alias for the existing maximal-domain resolvent state; it does not
introduce a new state and does not mention moments or a Jacobi operator. -/
def canonicalNativeBoundarySourceState
    (z : ℂ) (hz : z.im ≠ 0) : RealifiedLogarithmicDomain :=
  canonicalCompletedC3TfvdResolventDomainVector z hz

/-- The camera/source datum resolved by the native state. -/
def canonicalNativeBoundarySource
    (z : ℂ) : RealifiedCameraComplexification :=
  canonicalCompletedC3TfvdCameraSource z

/-- The two real source-relation quadratures of the same complex boundary
source.  The pair is only a packaging of the existing source-relation
elements. -/
def canonicalNativeBoundarySourceRelationPair
    (z : ℂ) (hz : z.im ≠ 0) : carrySourceRelation × carrySourceRelation :=
  (canonicalCompletedC3GammaSourceRelationFst z hz,
    canonicalCompletedC3GammaSourceRelationSnd z hz)

@[simp] theorem canonicalNativeBoundarySourceState_eq_resolvent
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalNativeBoundarySourceState z hz =
      canonicalCompletedC3TfvdResolventDomainVector z hz :=
  rfl

@[simp] theorem canonicalNativeBoundarySource_eq_tfvd
    (z : ℂ) :
    canonicalNativeBoundarySource z =
      canonicalCompletedC3TfvdCameraSource z :=
  rfl

/-- The native boundary source state satisfies the exact source/defect
equation of the maximal logarithmic relation. -/
theorem canonicalNativeBoundarySourceState_defectEquation
    (z : ℂ) (hz : z.im ≠ 0) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding
          (canonicalNativeBoundarySourceState z hz)) =
      realifiedLogarithmicMultiplication
          (canonicalNativeBoundarySourceState z hz) +
        realifiedNaimarkPort (canonicalNativeBoundarySource z) := by
  unfold canonicalNativeBoundarySourceState canonicalNativeBoundarySource
  rw [canonicalCompletedC3TfvdCameraSource_eq_canonicalSource]
  exact canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation z hz

/-- The same state is a Green right inverse for the canonical completed
source. -/
theorem canonicalNativeBoundarySourceState_greenRightInverse
    (z : ℂ) (hz : z.im ≠ 0) :
    CanonicalCompletedC3GreenRightInverseAt z
      (canonicalNativeBoundarySourceState z hz) := by
  exact canonicalCompletedC3TfvdResolventDomainVector_greenRightInverse z hz

/-- Resolvent uniqueness identifies the native boundary state with the Gamma
state. -/
theorem canonicalNativeBoundarySourceState_eq_gamma
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalNativeBoundarySourceState z hz =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) := by
  exact canonicalCompletedC3TfvdResolventDomainVector_eq_gamma z hz

/-- The first relation chart of the native source has the already proved Weyl
boundary coordinates. -/
theorem canonicalNativeBoundarySourceRelationPair_fst_weylBoundaryMap
    (z : ℂ) (hz : z.im ≠ 0) :
    carryWeylBoundaryMap
        (canonicalNativeBoundarySourceRelationPair z hz).1 =
      ((canonicalCompletedC3GammaBoundaryState z hz).2.fst,
        (canonicalCompletedC3GammaBoundaryState z hz).1.fst) := by
  exact canonicalCompletedC3GammaSourceRelationFst_weylBoundaryMap z hz

/-- The second relation chart of the native source has the already proved Weyl
boundary coordinates. -/
theorem canonicalNativeBoundarySourceRelationPair_snd_weylBoundaryMap
    (z : ℂ) (hz : z.im ≠ 0) :
    carryWeylBoundaryMap
        (canonicalNativeBoundarySourceRelationPair z hz).2 =
      ((canonicalCompletedC3GammaBoundaryState z hz).2.snd,
        (canonicalCompletedC3GammaBoundaryState z hz).1.snd) := by
  exact canonicalCompletedC3GammaSourceRelationSnd_weylBoundaryMap z hz

/-- The two relation charts are exactly the two quadratures of the same
boundary state. -/
theorem canonicalNativeBoundarySourceRelationPair_weylBoundaryMap
    (z : ℂ) (hz : z.im ≠ 0) :
    carryWeylBoundaryMap
        (canonicalNativeBoundarySourceRelationPair z hz).1 =
      ((canonicalCompletedC3GammaBoundaryState z hz).2.fst,
        (canonicalCompletedC3GammaBoundaryState z hz).1.fst) ∧
    carryWeylBoundaryMap
        (canonicalNativeBoundarySourceRelationPair z hz).2 =
      ((canonicalCompletedC3GammaBoundaryState z hz).2.snd,
        (canonicalCompletedC3GammaBoundaryState z hz).1.snd) := by
  exact ⟨canonicalNativeBoundarySourceRelationPair_fst_weylBoundaryMap z hz,
    canonicalNativeBoundarySourceRelationPair_snd_weylBoundaryMap z hz⟩

/-! ## The uncollapsed native two-point boundary readout -/

/-- Boundary readout of the two native maximal-domain response states.  The
first and second spectral slots remain separate, as in the existing candidate
readout. -/
def canonicalNativeBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalCompletedC3CandidateResolventBoundaryReadout z w
    (canonicalNativeBoundarySourceState z hz)
    (canonicalNativeBoundarySourceState w hw)

/-- Resolvent uniqueness transports the native boundary readout to the
canonical positive Gamma boundary readout. -/
theorem canonicalNativeBoundaryReadout_eq_gammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalNativeBoundaryReadout z w hz hw =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw := by
  exact canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout
    z w hz hw

/-- The same readout has the exact spectral-separation times Gamma-Gram
factorization. -/
theorem canonicalNativeBoundaryReadout_eq_separation_mul_gammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalNativeBoundaryReadout z w hz hw =
      (w - conj z) * canonicalCompletedC3PolarizedGammaKernel z w hz hw := by
  exact canonicalCompletedC3TfvdDomainBoundaryReadout_eq_separation_mul_gammaKernel
    z w hz hw

/-- The readout can also be expanded through the literal C3 bracket Cauchy
packing. -/
theorem canonicalNativeBoundaryReadout_eq_bracketCauchy
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalNativeBoundaryReadout z w hz hw =
      canonicalCompletedC3BracketCauchyBoundaryReadout z w hz hw := by
  exact canonicalCompletedC3TfvdDomainBoundaryReadout_eq_bracketCauchy
    z w hz hw

/-! ## The exact scalar seam -/

/-- Difference between the native boundary readout and the completed
`(F,-F')` Wronskian.  This is defined from the native boundary state, before
any moment or HP object is mentioned. -/
def canonicalNativeBoundaryReadoutDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  canonicalNativeBoundaryReadout z w hz hw -
    completedGreenWronskian
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion w z

/-- The native boundary defect is exactly the existing raw Gamma--Wronskian
defect. -/
theorem canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalNativeBoundaryReadoutDefect z w hz hw =
      canonicalCompletedC3RawGammaWronskianDefect z w hz hw := by
  unfold canonicalNativeBoundaryReadoutDefect
  rw [canonicalNativeBoundaryReadout_eq_gammaBoundaryReadout]
  rfl

/-- The same defect is the difference of the two actual boundary Green forms:
the Gamma source relation and the completed scalar trace. -/
theorem canonicalNativeBoundaryReadoutDefect_eq_boundaryGreenForm_sub
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalNativeBoundaryReadoutDefect z w hz hw =
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3GammaBoundaryState z hz)
          (canonicalCompletedC3GammaBoundaryState w hw) -
        greenForm (𝕜 := ℂ)
          (canonicalCompletedC3ScalarBoundaryPair z)
          (canonicalCompletedC3ScalarBoundaryPair w) := by
  rw [canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect,
    canonicalCompletedC3RawGammaWronskianDefect_eq_boundaryGreenForm_sub]

/-- The pointwise native boundary/Wronskian sewing gate, stated with the
actual resolved TFVD states. -/
def CanonicalNativeBoundaryCompletedReadoutSewing : Prop :=
  ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
    canonicalNativeBoundaryReadout z w hz hw =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z

/-- Sewing is equivalent to vanishing of the explicit native boundary
defect. -/
theorem canonicalNativeBoundaryCompletedReadoutSewing_iff_defect_zero :
    CanonicalNativeBoundaryCompletedReadoutSewing ↔
      ∀ (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0),
        canonicalNativeBoundaryReadoutDefect z w hz hw = 0 := by
  constructor
  · intro h z w hz hw
    unfold canonicalNativeBoundaryReadoutDefect
    rw [h z w hz hw]
    exact sub_self _
  · intro h z w hz hw
    have hzero := h z w hz hw
    unfold canonicalNativeBoundaryReadoutDefect at hzero
    exact sub_eq_zero.mp hzero

/-- The native source-state sewing is literally the pre-existing boundary
Green sewing gate. -/
theorem canonicalNativeBoundaryCompletedReadoutSewing_iff_boundaryGreenSewing :
    CanonicalNativeBoundaryCompletedReadoutSewing ↔
      CanonicalCompletedC3BoundaryGreenSewing := by
  rw [canonicalNativeBoundaryCompletedReadoutSewing_iff_defect_zero,
    canonicalCompletedC3BoundaryGreenSewing_iff_rawDefect_zero]
  constructor
  · intro h z w hz hw
    have hd := canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect
      z w hz hw
    rw [← hd]
    exact h z w hz hw
  · intro h z w hz hw
    have hd := canonicalNativeBoundaryReadoutDefect_eq_rawGammaWronskianDefect
      z w hz hw
    rw [hd]
    exact h z w hz hw

/-- If the remaining boundary sewing is supplied, the existing normalized
Gamma Gram closes against the completed native `dslope`.  The theorem keeps
the sewing as an explicit premise and therefore does not turn the residual
into an unproved premise. -/
theorem canonicalNativeBoundaryCompletedReadoutSewing.normalizedGammaKernel_eq_dslope
    (h : CanonicalNativeBoundaryCompletedReadoutSewing)
    (M : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
      canonicalCompletedNativePolarizedDslopeKernel z w := by
  have hboundary : CanonicalCompletedC3BoundaryGreenSewing :=
    (canonicalNativeBoundaryCompletedReadoutSewing_iff_boundaryGreenSewing.mp h)
  exact hboundary.normalizedGammaKernel_eq_dslope
    M z w hz hw hzStrip hwStrip hzF hwF hsep

/-! ## The Hilbert-space Green identity before scalar sewing -/

/-- The uncollapsed ambient boundary defect of the native response is already
spectral separation times a Hilbert-space Gram.  This is the rigorous
positive/Green part that survives independently of the scalar sewing gate. -/
theorem canonicalNativeBoundarySource_ambientGreenDefect_eq_separation_mul_gram
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3AmbientDefectBoundaryReadout z w
        (canonicalNativeBoundarySourceState z hz)
        (canonicalNativeBoundarySourceState w hw) =
      (w - conj z) *
        inner ℂ
          (canonicalCompletedC3GammaNaimarkView
            (realifiedLogarithmicDomainEmbedding
              (canonicalNativeBoundarySourceState z hz)))
          (canonicalCompletedC3GammaNaimarkView
            (realifiedLogarithmicDomainEmbedding
              (canonicalNativeBoundarySourceState w hw))) := by
  exact canonicalCompletedC3AmbientDefectBoundaryReadout_eq_kernel z w
    (canonicalNativeBoundarySourceState z hz)
    (canonicalNativeBoundarySourceState w hw)

/-- The previous Gram identity is a consequence of the source equation, not a
claim that the scalar Gamma and completed Wronskian readouts are equal. -/
theorem canonicalNativeBoundarySource_green_identity_package
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    CanonicalCompletedC3GreenRightInverseAt z
        (canonicalNativeBoundarySourceState z hz) ∧
      CanonicalCompletedC3GreenRightInverseAt w
        (canonicalNativeBoundarySourceState w hw) ∧
      canonicalCompletedC3AmbientDefectBoundaryReadout z w
          (canonicalNativeBoundarySourceState z hz)
          (canonicalNativeBoundarySourceState w hw) =
        (w - conj z) *
          inner ℂ
            (canonicalCompletedC3GammaNaimarkView
              (realifiedLogarithmicDomainEmbedding
                (canonicalNativeBoundarySourceState z hz)))
            (canonicalCompletedC3GammaNaimarkView
              (realifiedLogarithmicDomainEmbedding
                (canonicalNativeBoundarySourceState w hw))) := by
  exact ⟨canonicalNativeBoundarySourceState_greenRightInverse z hz,
    canonicalNativeBoundarySourceState_greenRightInverse w hw,
    canonicalNativeBoundarySource_ambientGreenDefect_eq_separation_mul_gram
      z w hz hw⟩

end

end CarrySelfAdjointOperator

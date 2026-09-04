import CarrySelfAdjointOperator.CompletedC3TfvdResolventTraceBridge
import Mathlib.Tactic

/-!
# Green-inverse criterion for the completed C3 sewing

This module isolates a Sun-inspired reformulation of the remaining completed
C3 sewing gate.  Instead of presenting the maximal-domain source equation in
its expanded form, we ask for the candidate state to be a right inverse of the
canonical defect operator `z - Y` on the completed C3 source.

The point is deliberately modest and exact:

* a Green/right-inverse identity is equivalent to the same-source resolvent
  equation already used by the Gamma field;
* therefore a trace-compatible Green realization canonically produces the
  existing `CanonicalCompletedC3WronskianResolventRealization`;
* resolvent uniqueness then closes the raw Gamma--Wronskian defect and, away
  from the usual regularity exclusions, the normalized Gamma--`dslope` sewing.

No new positivity, zero hypothesis, spectral list, or confinement statement is
assumed.  The remaining analytic task is exposed as the construction of a
trace-compatible Green right inverse on the completed cancellation carrier.

The organizational inspiration is the Green-inverse/Dirichlet-to-Neumann
criterion in Y. Sun, arXiv:2609.03647; no theorem from that paper is imported
or assumed here.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- A maximal-domain state is a Green right inverse at `z` for the canonical
completed C3 source when applying the defect operator `z - Y` returns exactly
that source.

This is the operator/inverse spelling of the already existing same-source
resolvent equation. -/
def CanonicalCompletedC3GreenRightInverseAt
    (z : ℂ) (candidate : RealifiedLogarithmicDomain) : Prop :=
  realifiedLambdaMinusLogarithmicMultiplication z candidate =
    realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)

/-- The Green right-inverse spelling expands to the canonical source equation
used by resolvent uniqueness. -/
theorem canonicalCompletedC3GreenRightInverseAt_defectEquation
    {z : ℂ} {candidate : RealifiedLogarithmicDomain}
    (hgreen : CanonicalCompletedC3GreenRightInverseAt z candidate) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding candidate) =
      realifiedLogarithmicMultiplication candidate +
        realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  unfold CanonicalCompletedC3GreenRightInverseAt at hgreen
  unfold realifiedLambdaMinusLogarithmicMultiplication at hgreen
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe] at hgreen
  exact sub_eq_iff_eq_add.mp hgreen

/-- Conversely, every canonical same-source resolvent state is a right inverse
of `z - Y` on the completed C3 source. -/
theorem canonicalCompletedC3GreenRightInverseAt_of_defectEquation
    {z : ℂ} {candidate : RealifiedLogarithmicDomain}
    (hequation :
      realifiedNaimarkScalar z
          (realifiedLogarithmicDomainEmbedding candidate) =
        realifiedLogarithmicMultiplication candidate +
          realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)) :
    CanonicalCompletedC3GreenRightInverseAt z candidate := by
  unfold CanonicalCompletedC3GreenRightInverseAt
  unfold realifiedLambdaMinusLogarithmicMultiplication
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe]
  exact sub_eq_iff_eq_add.mpr hequation

/-- Off the real axis there is no second canonical Green right inverse inside
the current logarithmic maximal domain: resolvent uniqueness forces every such
candidate to be the Gamma state.  A genuinely new Sun-style construction must
therefore change the cancellation carrier/operator and then intertwine it with
this one, rather than search for another state of the same defect operator. -/
theorem canonicalCompletedC3GreenRightInverseAt_eq_gamma
    {z : ℂ} (hz : z.im ≠ 0) {candidate : RealifiedLogarithmicDomain}
    (hgreen : CanonicalCompletedC3GreenRightInverseAt z candidate) :
    candidate =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
  carryGammaIntoDomain_unique z hz
    (canonicalCompletedC3SixCameraSource z) candidate
    (canonicalCompletedC3GreenRightInverseAt_defectEquation hgreen)

/-- A two-point trace-compatible Green realization.

The two candidate states are required to be Green right inverses on the
canonical completed sources.  The only scalar compatibility retained is that
their uncollapsed boundary readout is the already constructed completed
Wronskian. -/
structure CanonicalCompletedC3GreenInverseTraceRealization
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) where
  candidateZ : RealifiedLogarithmicDomain
  candidateW : RealifiedLogarithmicDomain
  rightInverseZ : CanonicalCompletedC3GreenRightInverseAt z candidateZ
  rightInverseW : CanonicalCompletedC3GreenRightInverseAt w candidateW
  boundaryReadout :
    canonicalCompletedC3CandidateResolventBoundaryReadout
        z w candidateZ candidateW =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z

namespace CanonicalCompletedC3GreenInverseTraceRealization

/-- A trace-compatible Green right inverse is exactly enough to construct the
existing completed Wronskian resolvent realization. -/
def toWronskianResolventRealization
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3GreenInverseTraceRealization z w hz hw) :
    CanonicalCompletedC3WronskianResolventRealization z w hz hw where
  candidateZ := realization.candidateZ
  candidateW := realization.candidateW
  defectEquationZ :=
    canonicalCompletedC3GreenRightInverseAt_defectEquation
      realization.rightInverseZ
  defectEquationW :=
    canonicalCompletedC3GreenRightInverseAt_defectEquation
      realization.rightInverseW
  boundaryReadout := realization.boundaryReadout

/-- Resolvent uniqueness identifies the first Green state with the canonical
Gamma state. -/
theorem candidateZ_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3GreenInverseTraceRealization z w hz hw) :
    realization.candidateZ =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
  realization.toWronskianResolventRealization.candidateZ_eq_gamma

/-- Resolvent uniqueness identifies the second Green state with the canonical
Gamma state. -/
theorem candidateW_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3GreenInverseTraceRealization z w hz hw) :
    realization.candidateW =
      carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w) :=
  realization.toWronskianResolventRealization.candidateW_eq_gamma

/-- The Green-inverse criterion kills the raw Gamma--Wronskian defect. -/
theorem rawGammaWronskianDefect_eq_zero
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3GreenInverseTraceRealization z w hz hw) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 :=
  realization.toWronskianResolventRealization.rawGammaWronskianDefect_eq_zero

/-- Away from characteristic zeros and spectral collision, the same
Green-inverse realization closes the normalized Gamma--`dslope` sewing. -/
theorem normalizedGammaKernel_eq_dslope
    (M : ℕ) {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3GreenInverseTraceRealization z w hz hw)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
      canonicalCompletedNativePolarizedDslopeKernel z w :=
  realization.toWronskianResolventRealization.normalizedGammaKernel_eq_dslope
    M hzStrip hwStrip hzF hwF hsep

end CanonicalCompletedC3GreenInverseTraceRealization

/-- The concrete TFVD/Gamma maximal-domain vector is already a Green right
inverse on the canonical completed source.  Thus the new formulation does not
create a stronger vector gate; it moves the remaining work entirely to the
trace-compatible construction. -/
theorem canonicalCompletedC3TfvdResolventDomainVector_greenRightInverse
    (z : ℂ) (hz : z.im ≠ 0) :
    CanonicalCompletedC3GreenRightInverseAt z
      (canonicalCompletedC3TfvdResolventDomainVector z hz) := by
  apply canonicalCompletedC3GreenRightInverseAt_of_defectEquation
  exact canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation z hz

/-! ## Test the already completed ambient trace candidate -/

/-- The ambient completed response is a Green right inverse for the canonical
C3 source exactly when its induced ambient source agrees with the canonical
TFVD/Gamma source.  Thus the pre-existing source correction is not ancillary:
it is precisely the obstruction to using the exact `(F,-F')` trace carrier as
the required Green realization without further cancellation. -/
theorem canonicalCompletedC3AmbientResolventDomainVector_greenRightInverse_iff_source
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3GreenRightInverseAt z
        (canonicalCompletedC3AmbientResolventDomainVector z hz hs) ↔
      canonicalCompletedC3AmbientInducedSourceLimit z hs =
        realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z) := by
  unfold CanonicalCompletedC3GreenRightInverseAt
  unfold canonicalCompletedC3AmbientResolventDomainVector
  rw [realifiedLambdaMinusLogarithmicMultiplication_apply_resolvent,
    canonicalCompletedC3TfvdCameraSource_eq_canonicalSource]

/-- Equivalently, the ambient exact-trace candidate works precisely when the
ambient-to-TFVD source correction vanishes. -/
theorem canonicalCompletedC3AmbientResolventDomainVector_greenRightInverse_iff_correction_zero
    (z : ℂ) (hz : z.im ≠ 0)
    (hs : 0 < (operatorHeightParameter z).re) :
    CanonicalCompletedC3GreenRightInverseAt z
        (canonicalCompletedC3AmbientResolventDomainVector z hz hs) ↔
      canonicalCompletedC3AmbientTfvdSourceCorrection z hs = 0 := by
  rw [canonicalCompletedC3AmbientResolventDomainVector_greenRightInverse_iff_source
    z hz hs]
  unfold canonicalCompletedC3AmbientTfvdSourceCorrection
  exact sub_eq_zero.symm

/-- The established leak witness rules out the naive choice of the already
completed ambient exact-trace response as the Green right inverse.  Therefore
any successful Sun-style route must genuinely modify/quotient/intertwine the
source correction rather than merely relabel the existing ambient state. -/
theorem canonicalCompletedC3AmbientResolventDomainVector_not_greenRightInverse_at_witness
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    ¬ CanonicalCompletedC3GreenRightInverseAt noLeakWitnessHeight
        (canonicalCompletedC3AmbientResolventDomainVector
          noLeakWitnessHeight
          (by rw [noLeakWitnessHeight_im]; norm_num)
          (by rw [operatorHeightParameter_noLeakWitnessHeight_re]; norm_num)) := by
  rw [canonicalCompletedC3AmbientResolventDomainVector_greenRightInverse_iff_source]
  rcases
      exists_canonicalCompletedC3AmbientInducedSourceLimit_ne_tfvdSource_at_witness
        hbase with ⟨_, _, hne⟩
  exact hne

end

end CarrySelfAdjointOperator

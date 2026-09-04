import CarrySelfAdjointOperator.CanonicalCompletedC3UniversalResolventDefect
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

end

end CarrySelfAdjointOperator

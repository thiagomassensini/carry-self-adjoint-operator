import CarrySelfAdjointOperator.CompletedC3TfvdResolventTraceBridge
import CarrySelfAdjointOperator.CompletedC3DirichletGradientBracketSource
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

The second half records a more faithful finite cancellation analogue.  The
carry-weighted Green operator is already an exact right inverse of the weighted
centered bracket on the zero-head source channel.  The actual finite TFVD
bracket source belongs to that channel, and its Green response plus the
canonical boundary return reconstructs the whole finite prefix.  This is the
concrete cancellation mechanism to be transported through completion; it is
not an extra positivity or spectral assumption.

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
  rw [← hgreen]
  abel

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
  rw [hequation]
  abel

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

/-! ## A genuine finite cancellation Green inverse -/

/-- On the zero-head cancellation channel, the weighted causal Green operator
is an exact right inverse of the weighted centered bracket.  The general
Green identity returns the zero-head projection; the cancellation condition
removes precisely that boundary defect. -/
theorem carryWeightedVerticalCenteredBracket_weightedGreen_eq_self_of_zeroHead
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (hx : x 0 = 0) :
    carryWeightedVerticalCenteredBracket q
        (carryVerticalL2WeightedGreen q x) = x := by
  rw [carryWeightedVerticalCenteredBracket_weightedGreen q hqpos hq1]
  ext n
  by_cases hn : n = 0
  · subst n
    simp [carryVerticalL2ZeroHeadProjection_apply, hx]
  · simp [carryVerticalL2ZeroHeadProjection_apply, hn]

/-- The actual finite completed-C3 bracket source belongs to the zero-head
cancellation channel, so its causal Green response satisfies the exact inverse
identity with no auxiliary hypothesis beyond camera support. -/
theorem canonicalCompletedC3DirichletGradientBracketSource_cancellationGreenInverse
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio base)
        (carryVerticalL2WeightedGreen
          (canonicalBR2CarryAmplitudeRatio base)
          (canonicalCompletedC3DirichletGradientBracketSource base cutoff s)) =
      canonicalCompletedC3DirichletGradientBracketSource base cutoff s := by
  apply carryWeightedVerticalCenteredBracket_weightedGreen_eq_self_of_zeroHead
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
  exact canonicalCompletedC3DirichletGradientBracketSource_zero base cutoff s

/-- The same finite cancellation Green response carries the honest boundary
return: Green response plus the trace return reconstructs the complete TFVD
prefix.  This is the finite source/Green/boundary square that a completed
Sun-style intertwiner would have to preserve. -/
theorem canonicalCompletedC3DirichletGradient_cancellationGreen_add_boundary_eq_prefix
    {base cutoff : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) (s : ℂ) :
    let q : ℝ := canonicalBR2CarryAmplitudeRatio base
    let prefixState := canonicalCompletedC3DirichletGradientPrefixState s
      (NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1)
    canonicalCompletedC3DirichletGradientBracketGreenResponse base cutoff s +
        carryWeightedVerticalReturn q
          (canonicalBR2CarryAmplitudeRatio_pos hbase).le
          (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
          (carryWeightedVerticalTrace q prefixState) =
      prefixState := by
  exact canonicalCompletedC3DirichletGradient_greenResponse_add_boundary_eq_prefix
    hbase s

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

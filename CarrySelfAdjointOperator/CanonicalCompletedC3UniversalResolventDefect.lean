import CarrySelfAdjointOperator.CanonicalCompletedC3NormalizedGammaSewing
import Mathlib.Tactic

/-!
# Universal resolvent defect for the completed C3 sewing

The raw Gamma--Wronskian mismatch is factored through a pair of vectors in
the exact maximal logarithmic domain.  A candidate completed realization at
each spectral point is compared with the canonical Gamma resolvent solution.
The scalar boundary mismatch is then one linear readout of this two-point
vector defect.

The existing resolvent uniqueness theorem annihilates the vector defect as
soon as the candidate satisfies the same source equation.  Thus the remaining
construction is typed precisely: realize the completed TFVD Wronskian as the
boundary readout of maximal-domain candidates with the already constructed
canonical C3 sources.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- Two-point maximal-domain carrier for a universal resolvent defect. -/
abbrev CanonicalCompletedC3UniversalResolventDefectCarrier :=
  RealifiedLogarithmicDomain × RealifiedLogarithmicDomain

/-- Type-only view of the existing realified camera carrier in the canonical
complex Hilbert structure.  No coordinate is changed. -/
def canonicalCompletedC3GammaCameraView
    (u : RealifiedCameraComplexification) : CarryGammaComplexCamera :=
  u

@[simp] theorem canonicalCompletedC3GammaCameraView_sub
    (u v : RealifiedCameraComplexification) :
    canonicalCompletedC3GammaCameraView (u - v) =
      canonicalCompletedC3GammaCameraView u -
        canonicalCompletedC3GammaCameraView v :=
  rfl

@[simp] theorem canonicalCompletedC3GammaCameraView_zero :
    canonicalCompletedC3GammaCameraView
        (0 : RealifiedCameraComplexification) = 0 :=
  rfl

/-- Boundary readout of arbitrary maximal-domain candidates at `z` and `w`.
The canonical C3 sources remain fixed and no Wronskian identity is assumed. -/
def canonicalCompletedC3CandidateResolventBoundaryReadout
    (z w : ℂ)
    (candidateZ candidateW : RealifiedLogarithmicDomain) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaCameraView
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicDomainEmbedding candidateZ)))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3SixCameraSource w)) -
    inner ℂ
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3SixCameraSource z))
      (canonicalCompletedC3GammaCameraView
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicDomainEmbedding candidateW)))

/-- Difference between the canonical Gamma resolvent solutions and two
arbitrary maximal-domain candidates. -/
def canonicalCompletedC3UniversalResolventDefect
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (candidateZ candidateW : RealifiedLogarithmicDomain) :
    CanonicalCompletedC3UniversalResolventDefectCarrier :=
  (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) - candidateZ,
    carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w) - candidateW)

/-- Linear boundary readout of a two-point maximal-domain vector defect. -/
def canonicalCompletedC3UniversalResolventDefectReadout
    (z w : ℂ)
    (defect : CanonicalCompletedC3UniversalResolventDefectCarrier) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaCameraView
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicDomainEmbedding defect.1)))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3SixCameraSource w)) -
    inner ℂ
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3SixCameraSource z))
      (canonicalCompletedC3GammaCameraView
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicDomainEmbedding defect.2)))

@[simp] theorem canonicalCompletedC3UniversalResolventDefectReadout_zero
    (z w : ℂ) :
    canonicalCompletedC3UniversalResolventDefectReadout z w 0 = 0 := by
  unfold canonicalCompletedC3UniversalResolventDefectReadout
  rw [show
      (0 : CanonicalCompletedC3UniversalResolventDefectCarrier).1 = 0 by rfl,
    show (0 : CanonicalCompletedC3UniversalResolventDefectCarrier).2 = 0 by rfl]
  simp only [map_zero]
  change
    inner ℂ
        (0 : CarryGammaComplexCamera)
        (canonicalCompletedC3GammaCameraView
          (canonicalCompletedC3SixCameraSource w)) -
      inner ℂ
        (canonicalCompletedC3GammaCameraView
          (canonicalCompletedC3SixCameraSource z))
        (0 : CarryGammaComplexCamera) = 0
  rw [inner_zero_left, inner_zero_right, sub_self]

/-- The canonical Cauchy trace is the adjoint boundary trace of the same
domain-valued Gamma resolvent solution. -/
theorem canonicalCompletedC3GammaCauchyReadout_eq_domainBoundary
    (z : ℂ) (hz : z.im ≠ 0) :
    carryGammaComplexCauchyReadout z hz
        (canonicalCompletedC3SixCameraSource z) =
      canonicalCompletedC3GammaCameraView
        (realifiedNaimarkAdjoint
          (realifiedLogarithmicDomainEmbedding
            (carryGammaIntoDomain z hz
              (canonicalCompletedC3SixCameraSource z)))) := by
  change allBasesCauchyBlock z hz
      (canonicalCompletedC3SixCameraSource z) =
    realifiedNaimarkAdjoint
      (carryGammaSource z hz (canonicalCompletedC3SixCameraSource z))
  exact (carryDefectGammaZero_apply z hz
    (canonicalCompletedC3SixCameraSource z)).symm

/-- Universal factorization: Gamma boundary minus any candidate boundary is
exactly the readout of their maximal-domain vector defect. -/
theorem canonicalCompletedC3GammaBoundary_sub_candidate_eq_universalDefectReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (candidateZ candidateW : RealifiedLogarithmicDomain) :
    canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
        canonicalCompletedC3CandidateResolventBoundaryReadout
          z w candidateZ candidateW =
      canonicalCompletedC3UniversalResolventDefectReadout z w
        (canonicalCompletedC3UniversalResolventDefect
          z w hz hw candidateZ candidateW) := by
  unfold canonicalCompletedC3PolarizedGammaBoundaryReadout
    carryGammaPolarizedBoundaryReadout
    canonicalCompletedC3CandidateResolventBoundaryReadout
    canonicalCompletedC3UniversalResolventDefectReadout
    canonicalCompletedC3UniversalResolventDefect
  rw [canonicalCompletedC3GammaCauchyReadout_eq_domainBoundary z hz,
    canonicalCompletedC3GammaCauchyReadout_eq_domainBoundary w hw]
  simp only [map_sub,
    canonicalCompletedC3GammaCameraView_sub,
    inner_sub_left, inner_sub_right]
  simp only [canonicalCompletedC3GammaCameraView]
  ring

/-- A same-source candidate contains only the two maximal-domain resolvent
equations.  It carries no scalar boundary or Wronskian hypothesis. -/
structure CanonicalCompletedC3SameSourceResolventCandidate
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) where
  candidateZ : RealifiedLogarithmicDomain
  candidateW : RealifiedLogarithmicDomain
  defectEquationZ :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding candidateZ) =
      realifiedLogarithmicMultiplication candidateZ +
        realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)
  defectEquationW :
    realifiedNaimarkScalar w
        (realifiedLogarithmicDomainEmbedding candidateW) =
      realifiedLogarithmicMultiplication candidateW +
        realifiedNaimarkPort (canonicalCompletedC3SixCameraSource w)

namespace CanonicalCompletedC3SameSourceResolventCandidate

/-- Resolvent uniqueness determines the candidate at `z`. -/
theorem candidateZ_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (candidate :
      CanonicalCompletedC3SameSourceResolventCandidate z w hz hw) :
    candidate.candidateZ =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
  carryGammaIntoDomain_unique z hz
    (canonicalCompletedC3SixCameraSource z)
    candidate.candidateZ candidate.defectEquationZ

/-- Resolvent uniqueness determines the candidate at `w`. -/
theorem candidateW_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (candidate :
      CanonicalCompletedC3SameSourceResolventCandidate z w hz hw) :
    candidate.candidateW =
      carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w) :=
  carryGammaIntoDomain_unique w hw
    (canonicalCompletedC3SixCameraSource w)
    candidate.candidateW candidate.defectEquationW

/-- The universal vector defect vanishes using only the two same-source
resolvent equations. -/
theorem universalDefect_eq_zero
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (candidate :
      CanonicalCompletedC3SameSourceResolventCandidate z w hz hw) :
    canonicalCompletedC3UniversalResolventDefect z w hz hw
        candidate.candidateZ candidate.candidateW = 0 := by
  unfold canonicalCompletedC3UniversalResolventDefect
  rw [candidate.candidateZ_eq_gamma, candidate.candidateW_eq_gamma]
  simp

/-- After uniqueness has killed the vector defect, the raw scalar defect is
exactly the candidate boundary readout minus the completed Wronskian.  This
is the precise boundary-realization gate and contains no unresolved vector
equation. -/
theorem rawGammaWronskianDefect_eq_candidateBoundary_sub_wronskian
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (candidate :
      CanonicalCompletedC3SameSourceResolventCandidate z w hz hw) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      canonicalCompletedC3CandidateResolventBoundaryReadout z w
          candidate.candidateZ candidate.candidateW -
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion w z := by
  have hzero :
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw -
          canonicalCompletedC3CandidateResolventBoundaryReadout z w
            candidate.candidateZ candidate.candidateW = 0 := by
    rw [canonicalCompletedC3GammaBoundary_sub_candidate_eq_universalDefectReadout,
      candidate.universalDefect_eq_zero,
      canonicalCompletedC3UniversalResolventDefectReadout_zero]
  have hboundary := sub_eq_zero.mp hzero
  unfold canonicalCompletedC3RawGammaWronskianDefect
  rw [hboundary]

end CanonicalCompletedC3SameSourceResolventCandidate

/-- A completed Wronskian resolvent realization consists of two
maximal-domain candidates satisfying the canonical C3 source equations and
whose uncollapsed boundary readout is the completed Wronskian. -/
structure CanonicalCompletedC3WronskianResolventRealization
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) where
  candidateZ : RealifiedLogarithmicDomain
  candidateW : RealifiedLogarithmicDomain
  defectEquationZ :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding candidateZ) =
      realifiedLogarithmicMultiplication candidateZ +
        realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)
  defectEquationW :
    realifiedNaimarkScalar w
        (realifiedLogarithmicDomainEmbedding candidateW) =
      realifiedLogarithmicMultiplication candidateW +
        realifiedNaimarkPort (canonicalCompletedC3SixCameraSource w)
  boundaryReadout :
    canonicalCompletedC3CandidateResolventBoundaryReadout
        z w candidateZ candidateW =
      completedGreenWronskian
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w z

namespace CanonicalCompletedC3WronskianResolventRealization

/-- Resolvent uniqueness identifies the first candidate with the canonical
Gamma domain state. -/
theorem candidateZ_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3WronskianResolventRealization z w hz hw) :
    realization.candidateZ =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
  carryGammaIntoDomain_unique z hz
    (canonicalCompletedC3SixCameraSource z)
    realization.candidateZ realization.defectEquationZ

/-- Resolvent uniqueness identifies the second candidate with the canonical
Gamma domain state. -/
theorem candidateW_eq_gamma
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3WronskianResolventRealization z w hz hw) :
    realization.candidateW =
      carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w) :=
  carryGammaIntoDomain_unique w hw
    (canonicalCompletedC3SixCameraSource w)
    realization.candidateW realization.defectEquationW

/-- Both coordinates of the universal vector defect vanish by resolvent
uniqueness. -/
theorem universalDefect_eq_zero
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3WronskianResolventRealization z w hz hw) :
    canonicalCompletedC3UniversalResolventDefect z w hz hw
        realization.candidateZ realization.candidateW = 0 := by
  unfold canonicalCompletedC3UniversalResolventDefect
  rw [realization.candidateZ_eq_gamma, realization.candidateW_eq_gamma]
  simp

/-- The raw Gamma--Wronskian defect is the readout of the universal vector
defect attached to a completed Wronskian resolvent realization. -/
theorem rawGammaWronskianDefect_eq_universalDefectReadout
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3WronskianResolventRealization z w hz hw) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      canonicalCompletedC3UniversalResolventDefectReadout z w
        (canonicalCompletedC3UniversalResolventDefect z w hz hw
          realization.candidateZ realization.candidateW) := by
  rw [canonicalCompletedC3RawGammaWronskianDefect,
    ← realization.boundaryReadout]
  exact
    canonicalCompletedC3GammaBoundary_sub_candidate_eq_universalDefectReadout
      z w hz hw realization.candidateZ realization.candidateW

/-- Resolvent uniqueness therefore kills the raw scalar defect after it has
been factored through the universal vector defect. -/
theorem rawGammaWronskianDefect_eq_zero
    {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3WronskianResolventRealization z w hz hw) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw = 0 := by
  rw [realization.rawGammaWronskianDefect_eq_universalDefectReadout,
    realization.universalDefect_eq_zero]
  exact canonicalCompletedC3UniversalResolventDefectReadout_zero z w

/-- The same realization closes the correctly normalized Gamma--`dslope`
sewing away from characteristic zeros and spectral collision. -/
theorem normalizedGammaKernel_eq_dslope
    (M : ℕ) {z w : ℂ} {hz : z.im ≠ 0} {hw : w.im ≠ 0}
    (realization :
      CanonicalCompletedC3WronskianResolventRealization z w hz hw)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z) :
    canonicalCompletedC3NormalizedPolarizedGammaKernel z w hz hw =
      canonicalCompletedNativePolarizedDslopeKernel z w := by
  rw [canonicalCompletedC3NormalizedPolarizedGammaKernel_eq_dslope_iff_rawWronskian
    M z w hz hw hzStrip hwStrip hzF hwF hsep]
  exact sub_eq_zero.mp realization.rawGammaWronskianDefect_eq_zero

end CanonicalCompletedC3WronskianResolventRealization

end

end CarrySelfAdjointOperator

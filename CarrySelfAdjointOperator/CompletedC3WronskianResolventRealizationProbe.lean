import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CarrySelfAdjointOperator.CanonicalCompletedC3TfvdResolventDomain
import Mathlib.Tactic

/-!
# Independent TFVD domain realization probe

The completed TFVD ledger has an ambient Naimark realization independently
of the logarithmic resolvent.  Because its six camera coordinates have finite
support, that realization belongs coordinatewise to the maximal logarithmic
domain.  This file constructs that domain point and checks, before invoking
resolvent uniqueness, whether it is the required response state.

The calculation distinguishes the TFVD source realization from a TFVD
Wronskian response realization.  No Wronskian equality, zero hypothesis, or
new defect equation is assumed.
-/

open scoped ComplexConjugate InnerProductSpace lp

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The real finite-support Naimark coordinate of the canonical TFVD port. -/
def canonicalCompletedC3TfvdNaimarkSourceRealCoordinate (z : ℂ) :
    NaimarkSpace :=
  naimarkCoreMap
    (c3RealCameraFinsupp
      (canonicalCompletedTfvdGreenPortState (operatorHeightParameter z)))

/-- The imaginary finite-support Naimark coordinate of the canonical TFVD
port. -/
def canonicalCompletedC3TfvdNaimarkSourceImagCoordinate (z : ℂ) :
    NaimarkSpace :=
  naimarkCoreMap
    (c3ImagCameraFinsupp
      (canonicalCompletedTfvdGreenPortState (operatorHeightParameter z)))

theorem canonicalCompletedC3TfvdNaimarkSourceRealCoordinate_mem_domain
    (z : ℂ) :
    canonicalCompletedC3TfvdNaimarkSourceRealCoordinate z ∈
      logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain]
  exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _

theorem canonicalCompletedC3TfvdNaimarkSourceImagCoordinate_mem_domain
    (z : ℂ) :
    canonicalCompletedC3TfvdNaimarkSourceImagCoordinate z ∈
      logarithmicMultiplication.domain := by
  rw [logarithmicMultiplication_domain]
  exact naimarkCoreMap_mem_logarithmicMultiplicationDomain _

/-- Independent maximal-domain lift of the existing TFVD Naimark source.
Unlike `canonicalCompletedC3TfvdResolventDomainVector`, this definition does
not apply a resolvent. -/
def canonicalCompletedC3TfvdNaimarkSourceDomainVector
    (z : ℂ) : RealifiedLogarithmicDomain :=
  (⟨canonicalCompletedC3TfvdNaimarkSourceRealCoordinate z,
      canonicalCompletedC3TfvdNaimarkSourceRealCoordinate_mem_domain z⟩,
    ⟨canonicalCompletedC3TfvdNaimarkSourceImagCoordinate z,
      canonicalCompletedC3TfvdNaimarkSourceImagCoordinate_mem_domain z⟩)

/-- Forgetting the domain witnesses gives exactly the existing TFVD Naimark
state. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding
    (z : ℂ) :
    realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) =
      canonicalCompletedTfvdGreenNaimarkState
        (operatorHeightParameter z) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change
      canonicalCompletedC3TfvdNaimarkSourceRealCoordinate z =
        (canonicalCompletedTfvdGreenNaimarkState
          (operatorHeightParameter z)).fst
    simp only [canonicalCompletedC3TfvdNaimarkSourceRealCoordinate,
      canonicalCompletedTfvdGreenNaimarkState,
      c3SixCameraNaimarkRealization, ContinuousLinearMap.comp_apply,
      realifiedNaimarkPort_fst, c3SixCameraPacking_apply,
      WithLp.toLp_fst]
    rw [naimarkIsometry_cameraEmbedding]
    rfl
  · change
      canonicalCompletedC3TfvdNaimarkSourceImagCoordinate z =
        (canonicalCompletedTfvdGreenNaimarkState
          (operatorHeightParameter z)).snd
    simp only [canonicalCompletedC3TfvdNaimarkSourceImagCoordinate,
      canonicalCompletedTfvdGreenNaimarkState,
      c3SixCameraNaimarkRealization, ContinuousLinearMap.comp_apply,
      realifiedNaimarkPort_snd, c3SixCameraPacking_apply,
      WithLp.toLp_snd]
    rw [naimarkIsometry_cameraEmbedding]
    rfl

/-- The independent lift is the Naimark port of the canonical C3 source. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding_eq_port
    (z : ℂ) :
    realifiedLogarithmicDomainEmbedding
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) =
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  rw [canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding]
  change
    realifiedNaimarkPort
        (canonicalCompletedTfvdGreenCameraState
          (operatorHeightParameter z)) =
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)
  congr 1
  rw [canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState]
  rfl

/-- Compressing the source-domain lift returns the same canonical camera
source.  This is source reconstruction, not a resolvent boundary response. -/
theorem realifiedNaimarkAdjoint_canonicalCompletedC3TfvdNaimarkSourceDomainVector
    (z : ℂ) :
    realifiedNaimarkAdjoint
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)) =
      canonicalCompletedC3SixCameraSource z := by
  rw [canonicalCompletedC3TfvdNaimarkSourceDomainVector_embedding_eq_port]
  change
    (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort)
        (canonicalCompletedC3SixCameraSource z) =
      canonicalCompletedC3SixCameraSource z
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

/-- Consequently the candidate boundary readout of the raw TFVD Naimark
source is identically zero.  Both terms are the same source pairing. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_boundaryReadout_eq_zero
    (z w : ℂ) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)
        (canonicalCompletedC3TfvdNaimarkSourceDomainVector w) = 0 := by
  unfold canonicalCompletedC3CandidateResolventBoundaryReadout
  rw [realifiedNaimarkAdjoint_canonicalCompletedC3TfvdNaimarkSourceDomainVector,
    realifiedNaimarkAdjoint_canonicalCompletedC3TfvdNaimarkSourceDomainVector]
  exact sub_self _

/-- The boundary readout of the actual Gamma domain vector is the positive
Gamma boundary.  This specialization uses only the universal vector-defect
factorization. -/
theorem canonicalCompletedC3CandidateResolventBoundaryReadout_gamma_eq
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z))
        (carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w)) =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw := by
  symm
  apply sub_eq_zero.mp
  rw [canonicalCompletedC3GammaBoundary_sub_candidate_eq_universalDefectReadout]
  have hdefect :
      canonicalCompletedC3UniversalResolventDefect z w hz hw
          (carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z))
          (carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w)) =
        0 := by
    simp [canonicalCompletedC3UniversalResolventDefect]
  rw [hdefect, canonicalCompletedC3UniversalResolventDefectReadout_zero]

/-- The direct TFVD Naimark source lift cannot satisfy the canonical
resolvent equation.  If it did, resolvent uniqueness would identify it with
Gamma, contradicting its zero diagonal boundary and strict Gamma
nondegeneracy. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_not_defectEquation
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    ¬(realifiedNaimarkScalar z
          (realifiedLogarithmicDomainEmbedding
            (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)) =
        realifiedLogarithmicMultiplication
            (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) +
          realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z)) := by
  intro hequation
  have hstate :
      canonicalCompletedC3TfvdNaimarkSourceDomainVector z =
        carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) :=
    carryGammaIntoDomain_unique z hz
      (canonicalCompletedC3SixCameraSource z)
      (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) hequation
  have hsourceZero :=
    canonicalCompletedC3TfvdNaimarkSourceDomainVector_boundaryReadout_eq_zero
      z z
  rw [hstate] at hsourceZero
  have hgammaBoundary :=
    canonicalCompletedC3CandidateResolventBoundaryReadout_gamma_eq z z hz hz
  apply canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
    hzStrip hz
  exact hgammaBoundary.symm.trans hsourceZero

/-- The source actually generated by applying `z-Y` to the direct TFVD
Naimark lift. -/
def canonicalCompletedC3TfvdNaimarkInducedDefectSource
    (z : ℂ) : RealifiedNaimarkComplexification :=
  realifiedLambdaMinusLogarithmicMultiplication z
    (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)

/-- The independent TFVD source lift satisfies a defect equation exactly for
its induced source. -/
theorem canonicalCompletedC3TfvdNaimarkSourceDomainVector_inducedDefectEquation
    (z : ℂ) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdNaimarkSourceDomainVector z)) =
      realifiedLogarithmicMultiplication
          (canonicalCompletedC3TfvdNaimarkSourceDomainVector z) +
        canonicalCompletedC3TfvdNaimarkInducedDefectSource z := by
  unfold canonicalCompletedC3TfvdNaimarkInducedDefectSource
    realifiedLambdaMinusLogarithmicMultiplication
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_coe]
  abel

/-- Exact first noncommuting square: throughout the off-axis open strip, the
source induced by the direct TFVD Naimark lift is not the canonical C3 source
appearing in the logarithmic resolvent equation. -/
theorem canonicalCompletedC3TfvdNaimarkInducedDefectSource_ne_canonical
    {z : ℂ} (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hz : z.im ≠ 0) :
    canonicalCompletedC3TfvdNaimarkInducedDefectSource z ≠
      realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  intro hsource
  apply canonicalCompletedC3TfvdNaimarkSourceDomainVector_not_defectEquation
    hzStrip hz
  rw [canonicalCompletedC3TfvdNaimarkSourceDomainVector_inducedDefectEquation,
    hsource]

end

end CarrySelfAdjointOperator

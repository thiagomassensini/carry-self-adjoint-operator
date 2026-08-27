import CarrySelfAdjointOperator.CanonicalCompletedC3UniversalResolventDefect
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import Mathlib.Tactic

/-!
# Completed TFVD source in the maximal logarithmic domain

The completed TFVD ledger already reconstructs the concrete six-camera source.
This file applies the existing logarithmic resolvent to that source and keeps
the resulting vector in `RealifiedLogarithmicDomain`.  The resolvent equation
then proves that this TFVD-derived vector and the canonical Gamma vector have
exactly the same source.  Resolvent uniqueness identifies them before any
scalar boundary readout is taken.

At two points the construction inhabits the previously isolated same-source
candidate and therefore annihilates the universal vector defect.  The final
theorem rewrites the remaining scalar defect using the independently completed
TFVD Wronskian, without asserting that the two scalar boundary readouts agree.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-- The concrete six-camera source reconstructed from the completed TFVD
ledger, expressed in centered-height coordinates. -/
def canonicalCompletedC3TfvdCameraSource (z : ℂ) :
    RealifiedCameraComplexification :=
  NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState
    (operatorHeightParameter z)

/-- The TFVD-reconstructed source is literally the canonical completed C3
source used by the Gamma field. -/
theorem canonicalCompletedC3TfvdCameraSource_eq_canonicalSource
    (z : ℂ) :
    canonicalCompletedC3TfvdCameraSource z =
      canonicalCompletedC3SixCameraSource z := by
  exact
    (canonicalCompletedC3SixCameraSource_eq_completedTfvdGreenCameraState z).symm

/-- The completed TFVD source resolved into the exact maximal domain of the
global logarithmic multiplication operator. -/
def canonicalCompletedC3TfvdResolventDomainVector
    (z : ℂ) (hz : z.im ≠ 0) : RealifiedLogarithmicDomain :=
  logarithmicResolventIntoDomain z hz
    (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z))

/-- The TFVD domain vector satisfies the resolvent equation with the source
reconstructed from the completed ledger. -/
theorem canonicalCompletedC3TfvdResolventDomainVector_defectEquation
    (z : ℂ) (hz : z.im ≠ 0) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdResolventDomainVector z hz)) =
      realifiedLogarithmicMultiplication
          (canonicalCompletedC3TfvdResolventDomainVector z hz) +
        realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z) := by
  change
    realifiedNaimarkScalar z
        (logarithmicResolventBlock z hz
          (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z))) =
      realifiedLogarithmicMultiplication
          (logarithmicResolventDomainElement z hz
            (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z))) +
        realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z)
  exact realified_logarithmic_resolvent_equation z hz
    (realifiedNaimarkPort (canonicalCompletedC3TfvdCameraSource z))

/-- The same equation after replacing the ledger presentation of the source
by the canonical completed C3 presentation. -/
theorem canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation
    (z : ℂ) (hz : z.im ≠ 0) :
    realifiedNaimarkScalar z
        (realifiedLogarithmicDomainEmbedding
          (canonicalCompletedC3TfvdResolventDomainVector z hz)) =
      realifiedLogarithmicMultiplication
          (canonicalCompletedC3TfvdResolventDomainVector z hz) +
        realifiedNaimarkPort (canonicalCompletedC3SixCameraSource z) := by
  rw [← canonicalCompletedC3TfvdCameraSource_eq_canonicalSource z]
  exact canonicalCompletedC3TfvdResolventDomainVector_defectEquation z hz

/-- Resolvent uniqueness identifies the TFVD-resolved domain vector with the
canonical Gamma domain vector. -/
theorem canonicalCompletedC3TfvdResolventDomainVector_eq_gamma
    (z : ℂ) (hz : z.im ≠ 0) :
    canonicalCompletedC3TfvdResolventDomainVector z hz =
      carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) := by
  exact carryGammaIntoDomain_unique z hz
    (canonicalCompletedC3SixCameraSource z)
    (canonicalCompletedC3TfvdResolventDomainVector z hz)
    (canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation z hz)

/-- The two-point TFVD construction inhabits the same-source resolvent
candidate without a scalar boundary or Wronskian premise. -/
def canonicalCompletedC3TfvdSameSourceResolventCandidate
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    CanonicalCompletedC3SameSourceResolventCandidate z w hz hw where
  candidateZ := canonicalCompletedC3TfvdResolventDomainVector z hz
  candidateW := canonicalCompletedC3TfvdResolventDomainVector w hw
  defectEquationZ :=
    canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation z hz
  defectEquationW :=
    canonicalCompletedC3TfvdResolventDomainVector_canonicalDefectEquation w hw

/-- Both TFVD-resolved vectors are the corresponding canonical Gamma vectors. -/
theorem canonicalCompletedC3TfvdSameSourceResolventCandidate_vectors_eq_gamma
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (canonicalCompletedC3TfvdSameSourceResolventCandidate z w hz hw).candidateZ =
        carryGammaIntoDomain z hz (canonicalCompletedC3SixCameraSource z) ∧
      (canonicalCompletedC3TfvdSameSourceResolventCandidate z w hz hw).candidateW =
        carryGammaIntoDomain w hw (canonicalCompletedC3SixCameraSource w) := by
  exact
    ⟨canonicalCompletedC3TfvdResolventDomainVector_eq_gamma z hz,
      canonicalCompletedC3TfvdResolventDomainVector_eq_gamma w hw⟩

/-- The universal two-point vector defect vanishes for the concrete
TFVD-resolved domain vectors. -/
theorem canonicalCompletedC3TfvdUniversalResolventDefect_eq_zero
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3UniversalResolventDefect z w hz hw
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3TfvdResolventDomainVector w hw) = 0 := by
  exact
    (canonicalCompletedC3TfvdSameSourceResolventCandidate z w hz hw).universalDefect_eq_zero

/-! ## Scalar expansion through the bracket Cauchy readout -/

/-- After vector uniqueness, the TFVD domain boundary is exactly the existing
Gamma Cauchy boundary. -/
theorem canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3TfvdResolventDomainVector w hw) =
      canonicalCompletedC3PolarizedGammaBoundaryReadout z w hz hw := by
  symm
  apply sub_eq_zero.mp
  rw [canonicalCompletedC3GammaBoundary_sub_candidate_eq_universalDefectReadout,
    canonicalCompletedC3TfvdUniversalResolventDefect_eq_zero,
    canonicalCompletedC3UniversalResolventDefectReadout_zero]

/-- The literal six-camera packing of the complete C3 bracket port. -/
def canonicalCompletedC3BracketCauchyCamera (z : ℂ) :
    RealifiedCameraComplexification :=
  NativeCarryC3Crosswalk.c3SixCameraPacking
    (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair 3
      (operatorHeightParameter z))

/-- Fully expanded two-point Cauchy readout of the bracket cameras. -/
def canonicalCompletedC3BracketCauchyBoundaryReadout
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GammaCameraView
        (allBasesCauchyBlock z hz
          (canonicalCompletedC3BracketCauchyCamera z)))
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3BracketCauchyCamera w)) -
    inner ℂ
      (canonicalCompletedC3GammaCameraView
        (canonicalCompletedC3BracketCauchyCamera z))
      (canonicalCompletedC3GammaCameraView
        (allBasesCauchyBlock w hw
          (canonicalCompletedC3BracketCauchyCamera w)))

/-- Expanding the maximal-domain boundary readout yields exactly the Cauchy
readout of the complete bracket packing. -/
theorem canonicalCompletedC3TfvdDomainBoundaryReadout_eq_bracketCauchy
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3TfvdResolventDomainVector w hw) =
      canonicalCompletedC3BracketCauchyBoundaryReadout z w hz hw := by
  rw [canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout]
  unfold canonicalCompletedC3PolarizedGammaBoundaryReadout
    carryGammaPolarizedBoundaryReadout carryGammaComplexCauchyReadout
    canonicalCompletedC3BracketCauchyBoundaryReadout
  rw [← canonicalCompletedC3TfvdCameraSource_eq_canonicalSource z,
    ← canonicalCompletedC3TfvdCameraSource_eq_canonicalSource w]
  have hzCamera :
      canonicalCompletedC3TfvdCameraSource z =
        canonicalCompletedC3BracketCauchyCamera z := by
    exact NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState_eq_canonical
      (operatorHeightParameter z)
  have hwCamera :
      canonicalCompletedC3TfvdCameraSource w =
        canonicalCompletedC3BracketCauchyCamera w := by
    exact NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState_eq_canonical
      (operatorHeightParameter w)
  rw [hzCamera, hwCamera]
  rfl

/-- The same scalar expansion through the positive Gamma Gram. -/
theorem canonicalCompletedC3TfvdDomainBoundaryReadout_eq_separation_mul_gammaKernel
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
        (canonicalCompletedC3TfvdResolventDomainVector z hz)
        (canonicalCompletedC3TfvdResolventDomainVector w hw) =
      (w - conj z) * canonicalCompletedC3PolarizedGammaKernel z w hz hw := by
  rw [canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout,
    canonicalCompletedC3PolarizedGammaBoundaryReadout_eq_kernel]

/-- After bracket expansion and the completed log-jet identity, the requested
scalar sewing is exactly the equality between the positive Gamma Gram boundary
and the Wronskian of `(F,-F')`. -/
theorem canonicalCompletedC3TfvdDomainBoundary_eq_tfvdWronskian_iff
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z w
          (canonicalCompletedC3TfvdResolventDomainVector z hz)
          (canonicalCompletedC3TfvdResolventDomainVector w hw) =
        canonicalC3BracketTfvdCompletedWronskianReadout M w z ↔
      (w - conj z) * canonicalCompletedC3PolarizedGammaKernel z w hz hw =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u) w z := by
  rw [canonicalCompletedC3TfvdDomainBoundaryReadout_eq_separation_mul_gammaKernel,
    canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
      M hwStrip hzStrip]

/-- At a nonreal characteristic zero, the positive Cauchy boundary cannot
already equal the completed TFVD Wronskian: the latter vanishes while the
former is nonzero.  Thus a global proof of the scalar sewing at zeros is
itself a proof that no such off-axis zero exists. -/
theorem canonicalCompletedC3TfvdDomainBoundary_ne_tfvdWronskian_of_characteristicZero
    (M : ℕ) {z : ℂ} (hz : z.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    canonicalCompletedC3CandidateResolventBoundaryReadout z z
          (canonicalCompletedC3TfvdResolventDomainVector z hz)
          (canonicalCompletedC3TfvdResolventDomainVector z hz) ≠
        canonicalC3BracketTfvdCompletedWronskianReadout M z z := by
  have hwronskian :
      canonicalC3BracketTfvdCompletedWronskianReadout M z z = 0 := by
    rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
      M hzStrip hzStrip]
    simp [completedGreenWronskian, hzero]
  have hboundary :=
    canonicalCompletedC3PolarizedGammaBoundaryReadout_diagonal_ne_zero
      hzStrip hz
  rw [canonicalCompletedC3TfvdDomainBoundaryReadout_eq_gammaBoundaryReadout,
    hwronskian]
  exact hboundary

/-- The remaining raw scalar defect after the concrete TFVD vectors have been
identified by uniqueness.  Its right side compares their domain boundary
readout with the independently completed TFVD Wronskian. -/
theorem canonicalCompletedC3RawGammaWronskianDefect_eq_tfvdDomainBoundary_sub_tfvdWronskian
    (M : ℕ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hwStrip : operatorHeightParameter w ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaWronskianDefect z w hz hw =
      canonicalCompletedC3CandidateResolventBoundaryReadout z w
          (canonicalCompletedC3TfvdResolventDomainVector z hz)
          (canonicalCompletedC3TfvdResolventDomainVector w hw) -
        canonicalC3BracketTfvdCompletedWronskianReadout M w z := by
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
    M hwStrip hzStrip]
  have hcompanion :
      (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u) =
        completedNativeOperatorBoundaryCompanion := by
    funext u
    exact (completedNativeOperatorBoundaryCompanion_eq_neg_deriv u).symm
  rw [hcompanion]
  exact
    (canonicalCompletedC3TfvdSameSourceResolventCandidate z w hz hw).rawGammaWronskianDefect_eq_candidateBoundary_sub_wronskian

end

end CarrySelfAdjointOperator

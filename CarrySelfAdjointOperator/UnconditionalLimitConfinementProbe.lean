import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import NativeCarryC3Crosswalk.FinalGenuineZeroConfinement

/-!
# Unconditional confinement composition and exact remaining seam

The failed predecessor of this file asked the pinned theorem graph to prove
`FinalGenuineZeroConfinement` with no extra premise.  GitHub Actions was left
to expose the first residual goal.  The green surface below retains the exact
composition, while naming rather than assuming away the scalarization still
needed from the completed TFVD/C3 source.

No zero list, fitted operator, activation predicate, simplicity assumption,
or confinement certificate enters this interface.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Exact remaining scalarization statement on the canonical completed C3
source. -/
def CanonicalCompletedC3GammaCauchyScalarizationSeam : Prop :=
  HasCanonicalCompletedNativeGammaCauchyScalarization
    canonicalCompletedC3SixCameraSource

/-- The canonical completed C3 source closes the public Genuine-zero target
once the exact Wronskian/Cauchy scalarization is supplied.  Source
nondegeneracy is discharged internally by the public completed TFVD ledger. -/
theorem finalGenuineZeroConfinement_of_canonicalCompletedC3Scalarization
    (hscalar : CanonicalCompletedC3GammaCauchyScalarizationSeam) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  intro s hs hzero
  have hzeta : riemannZeta s = 0 := by
    rw [← nativeScalar_eq_riemannZeta hs,
      nativeScalar_eq_genuineContinuation hs, hzero]
  exact riemannZeta_zero_re_eq_half_of_gammaCauchyScalarization
    canonicalCompletedC3SixCameraSource hscalar hs hzeta (by
      intro _hz
      rw [canonicalCompletedC3SixCameraSource_centeredHeightParameter]
      exact NativeCarryC3Crosswalk.seededCompletedTfvdGreenCameraState_ne_zero hs)

end

end CarrySelfAdjointOperator

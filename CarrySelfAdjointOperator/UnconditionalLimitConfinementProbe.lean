import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import NativeCarryC3Crosswalk.FinalGenuineZeroConfinement

/-!
# Unconditional confinement compositions and exact remaining seams

The public C3 repository already isolates the minimal diagonal seam needed for
Genuine-zero confinement: the uncompleted Genuine Green Wronskian must equal
the linear intrinsic carry-time coefficient times the raw C3 gamma Gram.

The operator repository carries a second, stronger normalization.  It asks the
xi-completed operator Wronskian to equal `-2 i` times the concrete all-bases
Cauchy skew of the canonical completed C3 source.  This stronger statement is
better aligned with the completed Weyl/Jacobi construction, but it must not be
confused with the logically minimal public confinement interface.

The failed red probe in PR #8 asked for the stronger completed scalarization.
The green surface below records both exact implications without asserting
either seam unconditionally.

No zero list, fitted operator, activation predicate, simplicity assumption,
or confinement certificate enters these interfaces.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Minimal public C3 seam at the first nonempty complete block. -/
def MinimalPublicC3ConfinementSeam : Prop :=
  NativeCarryC3Crosswalk.FiniteC3CompletedGreenWronskianSeam 1

/-- The public C3 kernel already proves that its minimal seam is sufficient
for unconditional confinement. -/
theorem finalGenuineZeroConfinement_of_minimalPublicC3Seam
    (hseam : MinimalPublicC3ConfinementSeam) :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement :=
  NativeCarryC3Crosswalk.
    finalGenuineZeroConfinement_of_finiteC3CompletedGreenWronskianSeam
      1 (by norm_num) hseam

/-- Stronger xi-completed scalarization statement on the canonical completed
C3 source used by the height-operator repository. -/
def CanonicalCompletedC3GammaCauchyScalarizationSeam : Prop :=
  HasCanonicalCompletedNativeGammaCauchyScalarization
    canonicalCompletedC3SixCameraSource

/-- The stronger completed scalarization also closes the public Genuine-zero
target. Source nondegeneracy is discharged internally by the public completed
TFVD ledger. -/
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

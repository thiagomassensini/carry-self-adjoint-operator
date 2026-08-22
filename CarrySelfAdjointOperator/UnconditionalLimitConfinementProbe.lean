import CarrySelfAdjointOperator.CompletedTfvdCanonicalSourceIntertwining
import CarrySelfAdjointOperator.CompletedGammaCauchyScalarization
import NativeCarryC3Crosswalk.FinalGenuineZeroConfinement

/-!
# Unconditional limit and confinement probe

This file asks the current pinned theorem graph for the zero-confinement
capstone using the canonical completed TFVD/C3 source.  No new realization,
positivity premise, zero list, or confinement certificate is introduced.

The first theorem records the exact composition already supported by the
kernel.  The second declaration deliberately asks Lean to discharge the last
remaining scalarization from the current graph, so GitHub Actions reports the
literal residual goal.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The canonical completed C3 source closes the public Genuine-zero target
once its completed Wronskian/Cauchy scalarization is supplied.  Source
nondegeneracy is discharged by the public completed TFVD ledger theorem. -/
theorem finalGenuineZeroConfinement_of_canonicalCompletedC3Scalarization
    (hscalar : HasCanonicalCompletedNativeGammaCauchyScalarization
      canonicalCompletedC3SixCameraSource) :
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

/-- Kernel probe: can the current graph construct the canonical completed
Wronskian/Cauchy scalarization with no additional premise? -/
theorem finalGenuineZeroConfinement_unconditional_probe :
    NativeCarryC3Crosswalk.FinalGenuineZeroConfinement := by
  apply finalGenuineZeroConfinement_of_canonicalCompletedC3Scalarization
  intro z hz

end

end CarrySelfAdjointOperator

import scratch_local.SourceFifthJetExtraction20261120
import scratch_local.NativeFifthPositiveSourceGate20261120
import CarrySelfAdjointOperator.NativeThetaCofactorMargin
import Mathlib.Tactic

/-!
## Fifth native C3 source Schur gate: completed analytic identity

Imports an unconditional height-side native analytic identification.
The geometry-derived third even Schur pivot is a SEPARATE sign certificate,
provided by GoN PR #324. No all-order positivity is assumed.
-/

namespace CarrySelfAdjointOperator.SourcePositiveReduction
noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

theorem nativeSourcePrefixDet_even_two_eq_nativeD2Real :
    nativeSourcePrefixDet 0 2 = nativeD2Real := by
  simp [nativeSourcePrefixDet, sourceMomentMatrix,
    Matrix.det_fin_two, nativeD2Real, pow_two]

theorem nativeEvenPrefix_two_isUnit :
    IsUnit (sourceMomentMatrix m 0 2) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  change nativeSourcePrefixDet 0 2 ≠ 0
  rw [nativeSourcePrefixDet_even_two_eq_nativeD2Real]
  exact (ne_of_gt nativeMoment_first_discriminant_pos)

theorem nativeSourceBorderedScalar_even_two_eq_nativeD3Real :
    nativeSourceBorderedScalar 0 2 = nativeD3Real := by
  simp [nativeSourceBorderedScalar, nativeSourcePrefixDet,
    sourceMomentCoupling, sourceMomentMatrix,
    Matrix.det_fin_two, Matrix.adjugate_fin_two,
    Matrix.mulVec, dotProduct, nativeD3Real, pow_two]
  ring

theorem nativeD3Real_eq_prefixDet_mul_evenThirdSchur :
    nativeD3Real =
      nativeD2Real * sourceMomentSchur m 0 2 := by
  calc
    nativeD3Real = nativeSourceBorderedScalar 0 2 :=
      nativeSourceBorderedScalar_even_two_eq_nativeD3Real.symm
    _ = nativeSourcePrefixDet 0 2 * sourceMomentSchur m 0 2 :=
      nativeSourceBorderedScalar_eq 0 2 nativeEvenPrefix_two_isUnit
    _ = nativeD2Real * sourceMomentSchur m 0 2 := by
      rw [nativeSourcePrefixDet_even_two_eq_nativeD2Real]

theorem chainScale_four_eq_nativeFifthScaleCandidate :
    chainScale 4 = nativeFifthScaleCandidate := by
  rw [chainScale_four_eq_native_det_ratio,
    nativeD3Real_eq_prefixDet_mul_evenThirdSchur]
  unfold nativeFifthScaleCandidate nativeFifthEvenD2 nativeFifthOddD2
    nativeD2Real nativeOddD2Real
  ring

theorem chainScale_four_pos_of_C3EvenThirdPivot
    (hC3EvenThird : 0 < sourceMomentSchur m 0 2) :
    0 < chainScale 4 := by
  rw [chainScale_four_eq_nativeFifthScaleCandidate]
  exact nativeFifthScaleCandidate_pos_of_evenThirdSchur hC3EvenThird

end
end CarrySelfAdjointOperator.SourcePositiveReduction

#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.chainScale_four_eq_nativeFifthScaleCandidate
#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.chainScale_four_pos_of_C3EvenThirdPivot

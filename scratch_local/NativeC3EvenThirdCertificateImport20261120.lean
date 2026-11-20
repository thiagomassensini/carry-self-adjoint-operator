import scratch_local.FifthNativePositiveKernel20261120
import NativeEvenCertificate

/-!
# Exact imported PR #324 witness

This module may only compile against the actual upstream proof, not an
axiom or an assumed pivot sign. The PR #324 theorem is imported from its
Lean source's compiled module NativeEvenCertificate.
-/

namespace CarrySelfAdjointOperator.SourcePositiveReduction
open Filter Topology
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

local notation "m" => canonicalCompletedNativeLogDerivativeMoment

/-- GoN source-derived even third pivot transported into the CSA namespace. -/
theorem nativeC3_evenThirdSchur_pos :
    0 < sourceMomentSchur m 0 2 := by
  exact C3CofactorChiral.c3_even_third_native_pivot_positive

/-- The fifth coefficient of the actual completed C3 source is POSITIVE,
with no parameter or sign assumptions remaining. -/
theorem nativeC3_fifthChainScale_pos :
    0 < chainScale 4 := by
  exact chainScale_four_pos_of_C3EvenThirdPivot nativeC3_evenThirdSchur_pos

/-- The completed two-variable native Green kernel admits five exact
positive source channels plus the untouched fifth residual. -/
theorem nativeC3_fivePositiveChannels_unconditional :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ z ∈ U, ∀ w ∈ U, w ≠ conj z →
        (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion w -
          conj (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z)) / (w - conj z) =
          chainPrefixKernel 5 z w +
          conj (chainWeight 5 z) * chainWeight 5 w *
            chainKernel 5 z w := by
  exact nativeKernel_five_positive_channels_local nativeC3_evenThirdSchur_pos

end
end CarrySelfAdjointOperator.SourcePositiveReduction

#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.nativeC3_evenThirdSchur_pos
#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.nativeC3_fifthChainScale_pos
#print axioms CarrySelfAdjointOperator.SourcePositiveReduction.nativeC3_fivePositiveChannels_unconditional

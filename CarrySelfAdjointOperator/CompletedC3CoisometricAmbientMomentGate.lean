import CarrySelfAdjointOperator.CompletedC3CoisometricAmbientStrictPositivity
import CarrySelfAdjointOperator.CompletedNativeCausalLegChiralBridge
import Mathlib.Tactic

/-!
# Central moment gate for the coisometric ambient carrier

The canonical Naimark port gives a strictly positive ambient Gram, but this
alone does not identify that Gram with the completed-native moment kernel.
At the center, the proposed identification is equivalent to one exact
geometric statement: the second transverse variation of the full completed
characteristic energy must be four times the completed C3 gradient energy.

This file records that equivalence without asserting the remaining energy
identity.  It also shows that the identity would force strict positivity of
the zeroth canonical moment.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- The central normalized ambient Gram equals the zeroth completed-native
moment exactly when the full transverse curvature equals four times the
ordinary completed C3 gradient energy.  The characteristic normalization and
the product-rule completion channels are retained on both sides. -/
theorem
    norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_eq_moment_zero_iff_transverseCurvature :
    ‖canonicalCompletedC3NormalizedAmbientResponseState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment 0 ↔
      iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 =
        4 * ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  rw [
    norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_eq_moment_zero_iff,
    completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_moment_zero]
  constructor <;> intro h <;> nlinarith

/-- The transverse-curvature identity isolated above would already make the
zeroth completed-native moment strictly positive, because the completed C3
ordinary gradient is nonzero at the center. -/
theorem canonicalCompletedNativeLogDerivativeMoment_zero_pos_of_transverseCurvature
    (hcurvature :
      iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 =
        4 * ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2) :
    0 < canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [← completedNativeVerticalModulusEnergy_secondDerivative_zero_pos_iff_moment_zero]
  rw [hcurvature]
  have hstrip : operatorHeightParameter 0 ∈
      CPFormal.Analytic.Cp.genuineCriticalStrip := by
    norm_num [operatorHeightParameter,
      CPFormal.Analytic.Cp.genuineCriticalStrip]
  have hgradient :
      canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0) hstrip.1 ≠ 0 :=
    canonicalCompletedC3DirichletGradientState_ne_zero hstrip
  positivity

end

end CarrySelfAdjointOperator

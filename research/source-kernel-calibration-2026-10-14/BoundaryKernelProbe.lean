import GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryHilbert
import GeometryOfNumbers.Analysis.BaseTwoCompletedVectorLiftGate
import Mathlib.Tactic

/-! Executable probe against geometry-of-numbers e1084b4, not against the
older pin consumed by the self-adjoint repository. No upstream file is edited. -/
noncomputable section
open scoped InnerProductSpace ComplexConjugate
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion.SourceKernelProbe

theorem raw_state_norm_ge_one (t : ℝ) :
    1 ≤ ‖baseTwoCompletedBoundaryHilbertState t‖ := by
  have h := WithLp.norm_fst_le ℂ (baseTwoCompletedBoundaryHilbertState t)
  simpa only [baseTwoCompletedBoundaryHilbertState_seed, criticalMaterialSample_one,
    norm_one] using h

theorem raw_state_norm_sq_ge_one (t : ℝ) :
    1 ≤ ‖baseTwoCompletedBoundaryHilbertState t‖^2 := by
  have h := raw_state_norm_ge_one t
  nlinarith

/-- Exact two-variable kernel of the actual completed boundary state. -/
theorem raw_state_polarized_kernel (t u : ℝ) :
    inner ℂ (baseTwoCompletedBoundaryHilbertState t)
      (baseTwoCompletedBoundaryHilbertState u) =
      1 + inner ℂ (baseTwoCompletedMaterialGradientL2 t)
          (baseTwoCompletedMaterialGradientL2 u) +
        conj (baseTwoCompletedBoundaryValue t)*baseTwoCompletedBoundaryValue u := by
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  simp [baseTwoCompletedBoundaryHilbertState, criticalMaterialSample_one,
    RCLike.inner_apply]
  ring

theorem dressed_state_polarized_kernel (t u : ℝ) :
    inner ℂ
      (baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t))
      (baseTwoVectorDressing u (baseTwoCompletedBoundaryHilbertState u)) =
      conj (baseTwoCanonicalDressingScalar t)*baseTwoCanonicalDressingScalar u *
        inner ℂ (baseTwoCompletedBoundaryHilbertState t)
          (baseTwoCompletedBoundaryHilbertState u) := by
  simp only [baseTwoVectorDressing_apply, inner_smul_left, inner_smul_right]
  ring

/-- Normalizing a vector by its OWN synthesized value cancels scalar dressing.
This is a source identity; no canonical moment occurs in it. -/
theorem value_normalized_dressed_state (t : ℝ) :
    (baseTwoCanonicalResponse t)⁻¹ •
        baseTwoVectorDressing t (baseTwoCompletedBoundaryHilbertState t) =
      (baseTwoCriticalCompleteSignal t)⁻¹ • baseTwoCompletedBoundaryHilbertState t := by
  rw [baseTwoCanonicalResponse_eq_dressing_mul_signal, baseTwoVectorDressing_apply,
    smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (baseTwoCanonicalDressingScalar_ne_zero t), mul_one]

#print axioms raw_state_norm_sq_ge_one
#print axioms raw_state_polarized_kernel
#print axioms dressed_state_polarized_kernel
#print axioms value_normalized_dressed_state
end GeometryOfNumbers.Analysis.BaseTwoCompletion.SourceKernelProbe

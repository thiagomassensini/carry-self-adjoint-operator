import CarrySelfAdjointOperator.NativeGammaSixCameraProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace Matrix
noncomputable section
set_option autoImplicit false

def nativeSixCameraEuclideanSynthesis : EuclideanSpace ℂ (Fin 6) →L[ℂ] CarryGammaComplexCamera :=
  (nativeSixCameraSynthesis.comp (WithLp.linearEquiv 2 ℂ (Fin 6 → ℂ)).toLinearMap).toContinuousLinearMap

theorem nativeSixCameraEuclideanSynthesis_apply (c : EuclideanSpace ℂ (Fin 6)) :
    nativeSixCameraEuclideanSynthesis c = nativeSixCameraSynthesis c.ofLp := rfl

theorem nativeSixCameraEuclideanSynthesis_single (i : Fin 6) :
    nativeSixCameraEuclideanSynthesis (EuclideanSpace.single i 1) =
      nativeComplexCameraVector (atlasSixCameraIndex i) := by
  rw [nativeSixCameraEuclideanSynthesis_apply, PiLp.ofLp_single]
  simp [nativeSixCameraSynthesis, Pi.single_apply]

theorem nativeSixCameraEuclideanAdjoint (u : CarryGammaComplexCamera) :
    (nativeSixCameraEuclideanSynthesis.adjoint u).ofLp = nativeSixCameraAnalysis u := by
  funext i
  have he := nativeSixCameraEuclideanSynthesis.adjoint_inner_right
    (EuclideanSpace.single i 1) u
  rw [nativeSixCameraEuclideanSynthesis_single] at he
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, nativeSixCameraAnalysis,
    LinearMap.coe_mk, AddHom.coe_mk] using he

/-- The Hilbert adjoint of the literal complex packing has the original Gram. -/
theorem nativeSixCamera_adjoint_synthesis (c : EuclideanSpace ℂ (Fin 6)) :
    (nativeSixCameraEuclideanSynthesis.adjoint (nativeSixCameraEuclideanSynthesis c)).ofLp =
      nativeSixCameraGram *ᵥ c.ofLp := by
  rw [nativeSixCameraEuclideanAdjoint, nativeSixCameraEuclideanSynthesis_apply,
    nativeSixCameraAnalysis_synthesis]

theorem nativeSixCameraProjection_selfadjoint (u v : CarryGammaComplexCamera) :
    inner ℂ (nativeSixCameraProjection u) v = inner ℂ u (nativeSixCameraProjection v) := by
  have hl : inner ℂ (nativeSixCameraProjection u) v =
      inner ℂ (nativeSixCameraProjection u) (nativeSixCameraProjection v) := by
    conv_lhs => rhs; rw [nativeSixCameraProjection_roundtrip v]
    simp only [nativeSixCameraProjection, LinearMap.comp_apply]
    rw [inner_add_right, nativeSixCameraExterior_orthogonal, add_zero]
  have hr : inner ℂ u (nativeSixCameraProjection v) =
      inner ℂ (nativeSixCameraProjection u) (nativeSixCameraProjection v) := by
    conv_lhs => lhs; rw [nativeSixCameraProjection_roundtrip u]
    rw [inner_add_left]
    have he : inner ℂ (nativeSixCameraExterior u) (nativeSixCameraProjection v) = 0 := by
      simp only [nativeSixCameraProjection, LinearMap.comp_apply]
      rw [← inner_conj_symm, nativeSixCameraExterior_orthogonal, map_zero]
    rw [he, add_zero]
    rfl
  exact hl.trans hr.symm

theorem nativeSixCameraProjection_orthogonalProjection :
    LinearMap.range nativeSixCameraProjection = LinearMap.range nativeSixCameraSynthesis ∧
    (∀ u, nativeSixCameraProjection (nativeSixCameraProjection u) = nativeSixCameraProjection u) ∧
    (∀ u v, inner ℂ (nativeSixCameraProjection u) v = inner ℂ u (nativeSixCameraProjection v)) ∧
    (∀ c u, inner ℂ (nativeSixCameraSynthesis c) (nativeSixCameraExterior u) = 0) :=
  ⟨nativeSixCameraProjection_range, nativeSixCameraProjection_idempotent,
    nativeSixCameraProjection_selfadjoint, nativeSixCameraExterior_orthogonal⟩

end
end CarrySelfAdjointOperator.GammaMaterialSewing

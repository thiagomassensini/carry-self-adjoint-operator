import CarrySelfAdjointOperator.NativeGammaCameraComplexLinear
import CarrySelfAdjointOperator.NativePhysicalLaguerreObservability

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false

theorem nativeSixCameraGram_det : nativeSixCameraGram.det = 4981760 := by
  change (Complex.ofRealHom.mapMatrix sixCameraGram).det = _
  rw [← RingHom.map_det, sixCameraGram_det]
  norm_num

theorem nativeSixCameraGram_isUnit : IsUnit nativeSixCameraGram.det := by
  rw [nativeSixCameraGram_det]
  norm_num

def nativeSixCameraCoordinates : CarryGammaComplexCamera →ₗ[ℂ] (Fin 6 → ℂ) :=
  (nativeSixCameraGram⁻¹).mulVecLin.comp nativeSixCameraAnalysis

theorem nativeSixCameraCoordinates_synthesis (c : Fin 6 → ℂ) :
    nativeSixCameraCoordinates (nativeSixCameraSynthesis c) = c := by
  change nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis (nativeSixCameraSynthesis c) = _
  rw [nativeSixCameraAnalysis_synthesis, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ nativeSixCameraGram_isUnit, Matrix.one_mulVec]

def nativeSixCameraProjection : CarryGammaComplexCamera →ₗ[ℂ] CarryGammaComplexCamera :=
  nativeSixCameraSynthesis.comp nativeSixCameraCoordinates

def nativeSixCameraExterior : CarryGammaComplexCamera →ₗ[ℂ] CarryGammaComplexCamera :=
  LinearMap.id - nativeSixCameraProjection

theorem nativeSixCameraProjection_roundtrip (u : CarryGammaComplexCamera) :
    u = nativeSixCameraSynthesis (nativeSixCameraCoordinates u) + nativeSixCameraExterior u := by
  change u = nativeSixCameraSynthesis (nativeSixCameraCoordinates u) +
    (u - nativeSixCameraSynthesis (nativeSixCameraCoordinates u))
  abel

theorem nativeSixCameraExterior_synthesis (c : Fin 6 → ℂ) :
    nativeSixCameraExterior (nativeSixCameraSynthesis c) = 0 := by
  change _ - nativeSixCameraSynthesis (nativeSixCameraCoordinates (nativeSixCameraSynthesis c)) = _
  rw [nativeSixCameraCoordinates_synthesis]
  simp only [LinearMap.id_apply, sub_self]

theorem nativeSixCameraProjection_idempotent (u : CarryGammaComplexCamera) :
    nativeSixCameraProjection (nativeSixCameraProjection u) = nativeSixCameraProjection u := by
  change nativeSixCameraSynthesis
    (nativeSixCameraCoordinates (nativeSixCameraSynthesis (nativeSixCameraCoordinates u))) = _
  rw [nativeSixCameraCoordinates_synthesis]
  rfl

theorem nativeSixCameraAnalysis_exterior (u : CarryGammaComplexCamera) :
    nativeSixCameraAnalysis (nativeSixCameraExterior u) = 0 := by
  change nativeSixCameraAnalysis (u - nativeSixCameraSynthesis (nativeSixCameraCoordinates u)) = 0
  rw [map_sub, nativeSixCameraAnalysis_synthesis]
  change _ - nativeSixCameraGram *ᵥ (nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis u) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ nativeSixCameraGram_isUnit,
    Matrix.one_mulVec, sub_self]

theorem nativeSixCameraSynthesis_inner_any (c : Fin 6 → ℂ) (u : CarryGammaComplexCamera) :
    inner ℂ (nativeSixCameraSynthesis c) u = star c ⬝ᵥ nativeSixCameraAnalysis u := by
  change inner ℂ (∑ i, c i • nativeComplexCameraVector (atlasSixCameraIndex i)) u = _
  simp only [sum_inner, inner_smul_left, dotProduct, Pi.star_apply]
  rfl

theorem nativeSixCameraExterior_orthogonal (c : Fin 6 → ℂ) (u : CarryGammaComplexCamera) :
    inner ℂ (nativeSixCameraSynthesis c) (nativeSixCameraExterior u) = 0 := by
  rw [nativeSixCameraSynthesis_inner_any, nativeSixCameraAnalysis_exterior, dotProduct_zero]

theorem nativeSixCameraProjection_metricLedger (u v : CarryGammaComplexCamera) :
    inner ℂ u v = star (nativeSixCameraCoordinates u) ⬝ᵥ
        (nativeSixCameraGram *ᵥ nativeSixCameraCoordinates v) +
      inner ℂ (nativeSixCameraExterior u) (nativeSixCameraExterior v) := by
  conv_lhs => rw [nativeSixCameraProjection_roundtrip u, nativeSixCameraProjection_roundtrip v]
  rw [inner_add_left, inner_add_right, inner_add_right, nativeSixCameraSynthesis_inner,
    nativeSixCameraExterior_orthogonal]
  have he : inner ℂ (nativeSixCameraExterior u)
      (nativeSixCameraSynthesis (nativeSixCameraCoordinates v)) = 0 := by
    rw [← inner_conj_symm, nativeSixCameraExterior_orthogonal, map_zero]
  rw [he]
  ring

theorem nativeSixCameraProjection_range :
    LinearMap.range nativeSixCameraProjection = LinearMap.range nativeSixCameraSynthesis := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨nativeSixCameraCoordinates v,rfl⟩
  · rintro ⟨c,rfl⟩
    refine ⟨nativeSixCameraSynthesis c, ?_⟩
    change nativeSixCameraSynthesis (nativeSixCameraCoordinates (nativeSixCameraSynthesis c)) = _
    rw [nativeSixCameraCoordinates_synthesis]

end
end CarrySelfAdjointOperator.GammaMaterialSewing

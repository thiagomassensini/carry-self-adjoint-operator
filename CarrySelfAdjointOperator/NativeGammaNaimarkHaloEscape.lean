import CarrySelfAdjointOperator.NativeGammaThreeSectorResolvent
import CarrySelfAdjointOperator.NativeGammaCameraAdjoint

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace ComplexConjugate
open NativeCarrySpectralWeyl.Infinite
noncomputable section
set_option autoImplicit false

def nativeComplexGlobalNaimarkProjection : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexNaimark :=
  nativeComplexNaimarkPort.comp nativeComplexNaimarkAdjoint

def nativeComplexGlobalNaimarkEscape : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexNaimark :=
  LinearMap.id - nativeComplexGlobalNaimarkProjection

theorem nativeComplexGlobalNaimarkProjection_eq_realComplexification (f : CarryGammaComplexNaimark) :
    nativeComplexGlobalNaimarkProjection f = nativeComplexificationMap globalNaimarkCameraProjection f := by
  apply RealHilbertComplexification.ext <;> rfl

theorem nativeComplexGlobalNaimarkEscape_eq_realComplexification (f : CarryGammaComplexNaimark) :
    nativeComplexGlobalNaimarkEscape f = nativeComplexificationMap globalNaimarkCameraEscape f := by
  apply RealHilbertComplexification.ext <;> rfl

theorem nativeGammaGlobalEscape_eq_globalProjectionEscape (z : ℂ) (hz : z.im ≠ 0)
    (u : CarryGammaComplexCamera) :
    nativeGammaGlobalEscape z hz u = nativeComplexGlobalNaimarkEscape (carryGammaComplexState z hz u) := by
  change _ - _ = _ - nativeComplexNaimarkPort (nativeComplexNaimarkAdjoint _)
  rw [nativeComplexNaimarkAdjoint_gamma]
  rfl

def nativeComplexSixCameraNaimarkProjection : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexNaimark :=
  nativeComplexNaimarkPort.comp (nativeSixCameraProjection.comp nativeComplexNaimarkAdjoint)

def nativeComplexSixCameraNaimarkEscape : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexNaimark :=
  LinearMap.id - nativeComplexSixCameraNaimarkProjection

theorem nativeComplexSixCameraNaimarkProjection_range :
    LinearMap.range nativeComplexSixCameraNaimarkProjection =
      LinearMap.range (nativeComplexNaimarkPort.comp nativeSixCameraSynthesis) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨nativeSixCameraCoordinates (nativeComplexNaimarkAdjoint g), rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨nativeComplexNaimarkPort (nativeSixCameraSynthesis c), ?_⟩
    change nativeComplexNaimarkPort (nativeSixCameraProjection
      (nativeComplexNaimarkAdjoint (nativeComplexNaimarkPort (nativeSixCameraSynthesis c)))) = _
    rw [nativeComplexNaimarkAdjoint_port]
    change nativeComplexNaimarkPort (nativeSixCameraSynthesis
      (nativeSixCameraCoordinates (nativeSixCameraSynthesis c))) = _
    rw [nativeSixCameraCoordinates_synthesis]
    rfl

theorem nativeComplexSixCameraNaimarkProjection_idempotent (f : CarryGammaComplexNaimark) :
    nativeComplexSixCameraNaimarkProjection (nativeComplexSixCameraNaimarkProjection f) =
      nativeComplexSixCameraNaimarkProjection f := by
  change nativeComplexNaimarkPort (nativeSixCameraProjection (nativeComplexNaimarkAdjoint
    (nativeComplexNaimarkPort (nativeSixCameraProjection (nativeComplexNaimarkAdjoint f))))) = _
  rw [nativeComplexNaimarkAdjoint_port, nativeSixCameraProjection_idempotent]
  rfl

theorem nativeComplexSixCameraNaimarkEscape_orthogonal (c : Fin 6 → ℂ)
    (f : CarryGammaComplexNaimark) :
    inner ℂ (nativeComplexNaimarkPort (nativeSixCameraSynthesis c))
      (nativeComplexSixCameraNaimarkEscape f) = 0 := by
  change inner ℂ (nativeComplexNaimarkPort (nativeSixCameraSynthesis c))
    (f - nativeComplexNaimarkPort (nativeSixCameraProjection (nativeComplexNaimarkAdjoint f))) = 0
  rw [inner_sub_right, nativeComplexNaimark_adjoint_inner, nativeComplexNaimarkPort_inner]
  have h := nativeSixCameraProjection_roundtrip (nativeComplexNaimarkAdjoint f)
  have he := nativeSixCameraExterior_orthogonal c (nativeComplexNaimarkAdjoint f)
  conv_lhs => arg 1; rhs; rw [h]
  rw [inner_add_right, he, add_zero]
  exact sub_self _

theorem nativeGammaSixCameraEscape_eq_halo_add_globalEscape (z : ℂ) (hz : z.im ≠ 0)
    (c : Fin 6 → ℂ) :
    nativeComplexSixCameraNaimarkEscape (carryGammaComplexState z hz (nativeSixCameraSynthesis c)) =
      nativeComplexNaimarkPort (nativeGammaResponseHalo z hz c) +
      nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c) := by
  change _ - nativeComplexNaimarkPort (nativeSixCameraProjection (nativeComplexNaimarkAdjoint _)) = _
  rw [nativeComplexNaimarkAdjoint_gamma, nativeGammaResolvent_threeSector_roundtrip]
  change (nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates z hz c)) +
    nativeComplexNaimarkPort (nativeGammaResponseHalo z hz c) +
    nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c)) -
    nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates z hz c)) = _
  abel

theorem nativeGammaSixCameraEscape_pairing (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (c d : Fin 6 → ℂ) :
    inner ℂ (nativeComplexSixCameraNaimarkEscape (carryGammaComplexState z hz (nativeSixCameraSynthesis c)))
      (nativeComplexSixCameraNaimarkEscape (carryGammaComplexState w hw (nativeSixCameraSynthesis d))) =
      inner ℂ (nativeGammaResponseHalo z hz c) (nativeGammaResponseHalo w hw d) +
      inner ℂ (nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c))
        (nativeGammaGlobalEscape w hw (nativeSixCameraSynthesis d)) := by
  rw [nativeGammaSixCameraEscape_eq_halo_add_globalEscape, nativeGammaSixCameraEscape_eq_halo_add_globalEscape]
  simp only [inner_add_left, inner_add_right, nativeComplexNaimarkPort_inner,
    nativeGammaGlobalEscape_orthogonal, nativeGammaGlobalEscape_orthogonal_reverse,
    add_zero, zero_add]

end
end CarrySelfAdjointOperator.GammaMaterialSewing

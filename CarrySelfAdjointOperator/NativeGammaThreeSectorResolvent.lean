import CarrySelfAdjointOperator.NativeGammaNaimarkComplexProjection
import CarrySelfAdjointOperator.NativeGammaSixCameraProjection

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false

def nativeGammaResponseCoordinates (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) : Fin 6 → ℂ :=
  nativeSixCameraCoordinates (nativeComplexCauchy z hz (nativeSixCameraSynthesis c))

def nativeGammaResponseHalo (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    CarryGammaComplexCamera :=
  nativeSixCameraExterior (nativeComplexCauchy z hz (nativeSixCameraSynthesis c))

theorem nativeGammaResolvent_threeSector_roundtrip (z : ℂ) (hz : z.im ≠ 0)
    (c : Fin 6 → ℂ) :
    carryGammaComplexState z hz (nativeSixCameraSynthesis c) =
      nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates z hz c)) +
      nativeComplexNaimarkPort (nativeGammaResponseHalo z hz c) +
      nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c) := by
  rw [nativeGammaGlobalEscape_roundtrip]
  have h := congrArg nativeComplexNaimarkPort
    (nativeSixCameraProjection_roundtrip (nativeComplexCauchy z hz (nativeSixCameraSynthesis c)))
  rw [map_add] at h
  exact congrArg (fun f => f + nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c)) h

theorem nativeGammaResolvent_camera_halo_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    inner ℂ
      (nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates z hz c)))
      (nativeComplexNaimarkPort (nativeGammaResponseHalo w hw d)) = 0 := by
  rw [nativeComplexNaimarkPort_inner]
  exact nativeSixCameraExterior_orthogonal _ _

theorem nativeGammaResolvent_halo_camera_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    inner ℂ (nativeComplexNaimarkPort (nativeGammaResponseHalo z hz c))
      (nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates w hw d))) = 0 := by
  rw [← inner_conj_symm, nativeGammaResolvent_camera_halo_orthogonal, map_zero]

theorem nativeGammaResolvent_threeSector_orthogonal (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    inner ℂ (nativeComplexNaimarkPort (nativeGammaResponseHalo z hz c))
        (nativeGammaGlobalEscape w hw (nativeSixCameraSynthesis d)) = 0 ∧
    inner ℂ (nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates z hz c)))
        (nativeGammaGlobalEscape w hw (nativeSixCameraSynthesis d)) = 0 ∧
    inner ℂ (nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c))
        (nativeComplexNaimarkPort (nativeGammaResponseHalo w hw d)) = 0 ∧
    inner ℂ (nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c))
        (nativeComplexNaimarkPort (nativeSixCameraSynthesis (nativeGammaResponseCoordinates w hw d))) = 0 := by
  exact ⟨nativeGammaGlobalEscape_orthogonal _ _ _ _,
    nativeGammaGlobalEscape_orthogonal _ _ _ _,
    nativeGammaGlobalEscape_orthogonal_reverse _ _ _ _,
    nativeGammaGlobalEscape_orthogonal_reverse _ _ _ _⟩

theorem nativeGammaResolvent_fullGram (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (u v : CarryGammaComplexCamera) :
    inner ℂ (carryGammaComplexState z hz u) (carryGammaComplexState w hw v) =
      inner ℂ (nativeComplexCauchy z hz u) (nativeComplexCauchy w hw v) +
      inner ℂ (nativeGammaGlobalEscape z hz u) (nativeGammaGlobalEscape w hw v) := by
  conv_lhs => rw [nativeGammaGlobalEscape_roundtrip z hz u,
    nativeGammaGlobalEscape_roundtrip w hw v]
  rw [inner_add_left, inner_add_right, inner_add_right,
    nativeComplexNaimarkPort_inner, nativeGammaGlobalEscape_orthogonal,
    nativeGammaGlobalEscape_orthogonal_reverse]
  ring

theorem nativeGammaResolvent_threeSector_Gram (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (c d : Fin 6 → ℂ) :
    inner ℂ (carryGammaComplexState z hz (nativeSixCameraSynthesis c))
        (carryGammaComplexState w hw (nativeSixCameraSynthesis d)) =
      star (nativeGammaResponseCoordinates z hz c) ⬝ᵥ
        (nativeSixCameraGram *ᵥ nativeGammaResponseCoordinates w hw d) +
      inner ℂ (nativeGammaResponseHalo z hz c) (nativeGammaResponseHalo w hw d) +
      inner ℂ (nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c))
        (nativeGammaGlobalEscape w hw (nativeSixCameraSynthesis d)) := by
  rw [nativeGammaResolvent_fullGram, nativeSixCameraProjection_metricLedger]
  rfl

end
end CarrySelfAdjointOperator.GammaMaterialSewing

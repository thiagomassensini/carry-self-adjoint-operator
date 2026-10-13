import CarrySelfAdjointOperator.NativeGammaCameraComplexLinear
import CarrySelfAdjointOperator.SixCameraGlobalNaimarkHaloDecomposition

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace ComplexConjugate
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

def nativeComplexificationMap {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →L[ℝ] F) :
    RealHilbertComplexification E →ₗ[ℂ] RealHilbertComplexification F where
  toFun u := RealHilbertComplexification.mk
    (T (RealHilbertComplexification.re u)) (T (RealHilbertComplexification.im u))
  map_add' := by intro u v; apply RealHilbertComplexification.ext <;> simp
  map_smul' := by
    intro a u
    apply RealHilbertComplexification.ext <;> simp [map_sub, map_smul]

def nativeComplexNaimarkPort : CarryGammaComplexCamera →ₗ[ℂ] CarryGammaComplexNaimark :=
  nativeComplexificationMap naimarkIsometry.toContinuousLinearMap

def nativeComplexNaimarkAdjoint : CarryGammaComplexNaimark →ₗ[ℂ] CarryGammaComplexCamera :=
  nativeComplexificationMap naimarkAdjoint

theorem nativeComplexNaimarkPort_eq_original (u : CarryGammaComplexCamera) :
    nativeComplexNaimarkPort u = realifiedNaimarkPort u := by
  apply RealHilbertComplexification.ext <;>
    simp [nativeComplexNaimarkPort, nativeComplexificationMap,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      RealHilbertComplexification.mk]

theorem nativeComplexNaimarkAdjoint_eq_original (f : CarryGammaComplexNaimark) :
    nativeComplexNaimarkAdjoint f = realifiedNaimarkAdjoint f := by
  apply RealHilbertComplexification.ext <;>
    simp [nativeComplexNaimarkAdjoint, nativeComplexificationMap,
      RealHilbertComplexification.re, RealHilbertComplexification.im,
      RealHilbertComplexification.mk]

theorem nativeComplexNaimarkPort_inner (u v : CarryGammaComplexCamera) :
    inner ℂ (nativeComplexNaimarkPort u) (nativeComplexNaimarkPort v) = inner ℂ u v := by
  simp [nativeComplexNaimarkPort, nativeComplexificationMap,
    RealHilbertComplexification.complexInner, naimarkIsometry.inner_map_map]

theorem nativeComplexNaimarkPort_norm (u : CarryGammaComplexCamera) :
    ‖nativeComplexNaimarkPort u‖ = ‖u‖ := by
  have h : ‖nativeComplexNaimarkPort u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), nativeComplexNaimarkPort_inner,
      norm_sq_eq_re_inner (𝕜 := ℂ)]
  nlinarith [norm_nonneg (nativeComplexNaimarkPort u), norm_nonneg u]

def nativeComplexNaimarkIsometry : CarryGammaComplexCamera →ₗᵢ[ℂ] CarryGammaComplexNaimark where
  toLinearMap := nativeComplexNaimarkPort
  norm_map' := nativeComplexNaimarkPort_norm

theorem nativeComplexNaimark_adjoint_inner (u : CarryGammaComplexCamera)
    (f : CarryGammaComplexNaimark) :
    inner ℂ (nativeComplexNaimarkPort u) f = inner ℂ u (nativeComplexNaimarkAdjoint f) := by
  have hr (a : CameraHilbert) (b : NaimarkSpace) :
      inner ℝ (naimarkIsometry a) b = inner ℝ a (naimarkAdjoint b) := by
    simpa [naimarkAdjoint] using
      (naimarkIsometry.toContinuousLinearMap.adjoint_inner_right a b).symm
  simp [nativeComplexNaimarkPort, nativeComplexNaimarkAdjoint, nativeComplexificationMap,
    RealHilbertComplexification.complexInner, hr]

theorem nativeComplexNaimark_hilbertAdjoint (f : CarryGammaComplexNaimark) :
    nativeComplexNaimarkIsometry.toContinuousLinearMap.adjoint f = nativeComplexNaimarkAdjoint f := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact nativeComplexNaimark_adjoint_inner u f

theorem nativeComplexNaimarkAdjoint_port (u : CarryGammaComplexCamera) :
    nativeComplexNaimarkAdjoint (nativeComplexNaimarkPort u) = u := by
  rw [nativeComplexNaimarkPort_eq_original, nativeComplexNaimarkAdjoint_eq_original]
  change (realifiedNaimarkAdjoint ∘L realifiedNaimarkPort) u = u
  rw [NativeCarryC3Crosswalk.realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  rfl

theorem nativeComplexNaimarkAdjoint_gamma (z : ℂ) (hz : z.im ≠ 0)
    (u : CarryGammaComplexCamera) :
    nativeComplexNaimarkAdjoint (carryGammaComplexState z hz u) = nativeComplexCauchy z hz u := by
  rw [nativeComplexNaimarkAdjoint_eq_original]
  exact carryDefectGammaZero_apply z hz u

def nativeGammaGlobalEscape (z : ℂ) (hz : z.im ≠ 0) (u : CarryGammaComplexCamera) :
    CarryGammaComplexNaimark :=
  carryGammaComplexState z hz u - nativeComplexNaimarkPort (nativeComplexCauchy z hz u)

theorem nativeGammaGlobalEscape_eq_original (z : ℂ) (hz : z.im ≠ 0)
    (u : CarryGammaComplexCamera) :
    nativeGammaGlobalEscape z hz u =
      canonicalCompletedC3AmbientPortEscape (carryGammaComplexState z hz u) := by
  change _ - _ = _ - realifiedNaimarkPort (realifiedNaimarkAdjoint _)
  rw [← nativeComplexNaimarkPort_eq_original, ← nativeComplexNaimarkAdjoint_eq_original,
    nativeComplexNaimarkAdjoint_gamma]
  rfl

theorem nativeGammaGlobalEscape_roundtrip (z : ℂ) (hz : z.im ≠ 0)
    (u : CarryGammaComplexCamera) :
    carryGammaComplexState z hz u =
      nativeComplexNaimarkPort (nativeComplexCauchy z hz u) + nativeGammaGlobalEscape z hz u := by
  unfold nativeGammaGlobalEscape
  abel

theorem nativeGammaGlobalEscape_orthogonal (z : ℂ) (hz : z.im ≠ 0)
    (u v : CarryGammaComplexCamera) :
    inner ℂ (nativeComplexNaimarkPort v) (nativeGammaGlobalEscape z hz u) = 0 := by
  rw [nativeGammaGlobalEscape, inner_sub_right, nativeComplexNaimark_adjoint_inner,
    nativeComplexNaimarkAdjoint_gamma, nativeComplexNaimarkPort_inner, sub_self]

theorem nativeGammaGlobalEscape_orthogonal_reverse (z : ℂ) (hz : z.im ≠ 0)
    (u v : CarryGammaComplexCamera) :
    inner ℂ (nativeGammaGlobalEscape z hz u) (nativeComplexNaimarkPort v) = 0 := by
  rw [← inner_conj_symm, nativeGammaGlobalEscape_orthogonal, map_zero]

end
end CarrySelfAdjointOperator.GammaMaterialSewing

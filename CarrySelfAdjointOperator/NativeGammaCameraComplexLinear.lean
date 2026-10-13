import CarrySelfAdjointOperator.CompletedGammaTwoParameterGreenIdentity
import CarrySelfAdjointOperator.AtlasEnergySixCameraHilbertAsymptoticCrosswalk
import CarrySelfAdjointOperator.CanonicalC3SixCameraSource

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false

def nativeComplexCameraBlock (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (u : CarryGammaComplexCamera) : CarryGammaComplexCamera := realifiedCameraBlock A B u

theorem nativeComplexCameraBlock_re (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (u : CarryGammaComplexCamera) :
    RealHilbertComplexification.re (nativeComplexCameraBlock A B u) =
      A (RealHilbertComplexification.re u) - B (RealHilbertComplexification.im u) :=
  realifiedCameraBlock_fst A B u

theorem nativeComplexCameraBlock_im (A B : CameraHilbert →L[ℝ] CameraHilbert)
    (u : CarryGammaComplexCamera) :
    RealHilbertComplexification.im (nativeComplexCameraBlock A B u) =
      B (RealHilbertComplexification.re u) + A (RealHilbertComplexification.im u) :=
  realifiedCameraBlock_snd A B u

theorem realifiedCameraBlock_complex_smul
    (A B : CameraHilbert →L[ℝ] CameraHilbert) (c : ℂ)
    (u : CarryGammaComplexCamera) :
    nativeComplexCameraBlock A B (c • u) = c • nativeComplexCameraBlock A B u := by
  apply RealHilbertComplexification.ext <;>
    simp only [nativeComplexCameraBlock_re, nativeComplexCameraBlock_im,
      RealHilbertComplexification.re_smul, RealHilbertComplexification.im_smul,
      map_sub, map_add, map_smul] <;> module

/-- The original real block is complex-linear on the existing canonical
complexification. Its inner product and norm are unchanged. -/
def nativeComplexCauchy (z : ℂ) (hz : z.im ≠ 0) :
    CarryGammaComplexCamera →ₗ[ℂ] CarryGammaComplexCamera where
  toFun := carryGammaComplexCauchyReadout z hz
  map_add' := by intro u v; exact (allBasesCauchyBlock z hz).map_add u v
  map_smul' := by
    intro c u
    exact realifiedCameraBlock_complex_smul _ _ c u

theorem nativeComplexCauchy_apply (z : ℂ) (hz : z.im ≠ 0) (u : CarryGammaComplexCamera) :
    nativeComplexCauchy z hz u = carryGammaComplexCauchyReadout z hz u := rfl

theorem nativeComplexCauchy_I (z : ℂ) (hz : z.im ≠ 0) (u : CarryGammaComplexCamera) :
    nativeComplexCauchy z hz (Complex.I • u) = Complex.I • nativeComplexCauchy z hz u :=
  (nativeComplexCauchy z hz).map_smul Complex.I u

def nativeComplexCameraVector (b : CameraIndex) : CarryGammaComplexCamera :=
  RealHilbertComplexification.mk (cameraVector b) 0

theorem nativeComplexCameraVector_inner (b c : CameraIndex) :
    inner ℂ (nativeComplexCameraVector b) (nativeComplexCameraVector c) =
      (gramKernel b c : ℂ) := by
  simp [nativeComplexCameraVector, RealHilbertComplexification.inner_apply,
    RealHilbertComplexification.complexInner]

def nativeSixCameraGram : Matrix (Fin 6) (Fin 6) ℂ :=
  sixCameraGram.map Complex.ofReal

theorem nativeSixCameraGram_entry (i j : Fin 6) :
    inner ℂ (nativeComplexCameraVector (atlasSixCameraIndex i))
      (nativeComplexCameraVector (atlasSixCameraIndex j)) = nativeSixCameraGram i j := by
  rw [nativeComplexCameraVector_inner, ← atlasSixCameraGram_entry_eq_gramKernel]
  rfl

def nativeSixCameraSynthesis : (Fin 6 → ℂ) →ₗ[ℂ] CarryGammaComplexCamera where
  toFun c := ∑ i, c i • nativeComplexCameraVector (atlasSixCameraIndex i)
  map_add' := by intro c d; simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

def nativeSixCameraAnalysis : CarryGammaComplexCamera →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun u i := inner ℂ (nativeComplexCameraVector (atlasSixCameraIndex i)) u
  map_add' := by intro u v; ext i; simp only [inner_add_right, Pi.add_apply]
  map_smul' := by intro a u; ext i; simp only [inner_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem nativeSixCameraAnalysis_synthesis (c : Fin 6 → ℂ) :
    nativeSixCameraAnalysis (nativeSixCameraSynthesis c) = nativeSixCameraGram *ᵥ c := by
  ext i
  simp only [nativeSixCameraAnalysis, LinearMap.coe_mk, AddHom.coe_mk,
    nativeSixCameraSynthesis, inner_sum, inner_smul_right, nativeSixCameraGram_entry,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nativeSixCameraSynthesis_inner (c d : Fin 6 → ℂ) :
    inner ℂ (nativeSixCameraSynthesis c) (nativeSixCameraSynthesis d) =
      star c ⬝ᵥ (nativeSixCameraGram *ᵥ d) := by
  change inner ℂ (∑ i, c i • nativeComplexCameraVector (atlasSixCameraIndex i)) _ = _
  simp only [sum_inner, inner_smul_left, ← nativeSixCameraAnalysis_synthesis,
    dotProduct, Pi.star_apply]
  rfl

end
end CarrySelfAdjointOperator.GammaMaterialSewing

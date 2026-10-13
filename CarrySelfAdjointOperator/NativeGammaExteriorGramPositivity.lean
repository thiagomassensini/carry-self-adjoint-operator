import CarrySelfAdjointOperator.NativeGammaResolventMatrix
import CarrySelfAdjointOperator.NativeGammaComplexLinearState

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false

theorem nativeFiniteGram_pairing {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (f : Fin 6 → H) (c d : Fin 6 → ℂ) :
    star c ⬝ᵥ ((fun i j => inner ℂ (f i) (f j)) *ᵥ d) =
      inner ℂ (∑ i, c i • f i) (∑ j, d j • f j) := by
  simp only [dotProduct, Matrix.mulVec, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Pi.star_apply, Complex.star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nativeGammaHaloMatrix_quadratic (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    star c ⬝ᵥ (nativeGammaHaloMatrix z z hz hz *ᵥ c) =
      (‖nativeGammaResponseHalo z hz c‖ ^ 2 : ℝ) := by
  unfold nativeGammaHaloMatrix
  rw [nativeFiniteGram_pairing, inner_self_eq_norm_sq_to_K]
  simp [nativeGammaResponseHalo, nativeSixCameraSynthesis, map_sum, map_smul, Complex.ofReal_pow]

theorem nativeGammaGlobalEscape_synthesis (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c) =
      ∑ i, c i • nativeGammaGlobalEscape z hz (nativeComplexCameraVector (atlasSixCameraIndex i)) := by
  simp only [nativeGammaGlobalEscape, ← nativeComplexGamma_eq_original,
    nativeSixCameraSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]

theorem nativeGammaEscapeMatrix_quadratic (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    star c ⬝ᵥ (nativeGammaEscapeMatrix z z hz hz *ᵥ c) =
      (‖nativeGammaGlobalEscape z hz (nativeSixCameraSynthesis c)‖ ^ 2 : ℝ) := by
  unfold nativeGammaEscapeMatrix
  rw [nativeFiniteGram_pairing, inner_self_eq_norm_sq_to_K,
    nativeGammaGlobalEscape_synthesis]
  simp

theorem nativeGammaExteriorGrams_nonnegative (z : ℂ) (hz : z.im ≠ 0) (c : Fin 6 → ℂ) :
    0 ≤ (star c ⬝ᵥ (nativeGammaHaloMatrix z z hz hz *ᵥ c)).re ∧
    (star c ⬝ᵥ (nativeGammaHaloMatrix z z hz hz *ᵥ c)).im = 0 ∧
    0 ≤ (star c ⬝ᵥ (nativeGammaEscapeMatrix z z hz hz *ᵥ c)).re ∧
    (star c ⬝ᵥ (nativeGammaEscapeMatrix z z hz hz *ᵥ c)).im = 0 := by
  rw [nativeGammaHaloMatrix_quadratic, nativeGammaEscapeMatrix_quadratic]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨sq_nonneg _, trivial, sq_nonneg _, trivial⟩

end
end CarrySelfAdjointOperator.GammaMaterialSewing

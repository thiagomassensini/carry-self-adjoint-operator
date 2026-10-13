import CarrySelfAdjointOperator.NativeGammaCanonicalSource
import CarrySelfAdjointOperator.C3MixedReturnTraceObstruction

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
open NativeCarryC3Crosswalk
noncomputable section
set_option autoImplicit false

def nativeMixedRay : Fin 6 → ℂ := ![-6,-3,2,0,3,0]

def nativeMixedVector : CarryGammaComplexCamera := nativeSixCameraSynthesis nativeMixedRay

def nativeMixedUnitVector : CarryGammaComplexCamera :=
  ((Real.sqrt 278 : ℂ)⁻¹) • nativeMixedVector

def nativeMixedCoefficients (c : Fin 6 → ℂ) : Fin 6 → ℂ := (c 4 / 3) • nativeMixedRay

def nativeMixedComplement (c : Fin 6 → ℂ) : Fin 6 → ℂ := c - nativeMixedCoefficients c

theorem nativeMixedCoefficients_cameraSix (c : Fin 6 → ℂ) :
    nativeMixedCoefficients c 4 = c 4 := by
  change c 4 / 3 * 3 = c 4
  ring

theorem nativeMixedComplement_cameraSix (c : Fin 6 → ℂ) :
    nativeMixedComplement c 4 = 0 := by
  simp [nativeMixedComplement, nativeMixedCoefficients_cameraSix]

theorem nativeMixedCoefficients_roundtrip (c : Fin 6 → ℂ) :
    nativeMixedCoefficients c + nativeMixedComplement c = c := by
  unfold nativeMixedComplement
  abel

theorem nativeMixedVector_eq_original : nativeMixedVector =
    RealHilbertComplexification.mk sixCameraReturnVector 0 := by
  have h := sixCameraMixedReturnPortPart_sourceMap
    (WithLp.toLp 2 ![0,0,0], WithLp.toLp 2 ![0,3,0])
  rw [← nativeSixCameraSynthesis_pack] at h
  norm_num [nativeC3PackedCoefficients, sixCameraMixedReturnPortPart] at h
  exact h

theorem nativeMixedVector_inner_synthesis (c : Fin 6 → ℂ) :
    inner ℂ nativeMixedVector (nativeSixCameraSynthesis c) = (278/3 : ℂ) * c 4 := by
  have he (i : Fin 6) : inner ℂ nativeMixedVector
      (nativeComplexCameraVector (atlasSixCameraIndex i)) =
      if i = 4 then (278/3 : ℂ) else 0 := by
    rw [nativeMixedVector_eq_original]
    have h0 := inner_sixCameraReturnVector_first 0
    have h1 := inner_sixCameraReturnVector_first 1
    have h2 := inner_sixCameraReturnVector_first 2
    have h3 := inner_sixCameraReturnVector_second 0
    have h4 := inner_sixCameraReturnVector_second 1
    have h5 := inner_sixCameraReturnVector_second 2
    norm_num [firstC3CameraIndex, secondC3CameraIndex] at h0 h1 h2 h3 h4 h5
    fin_cases i <;>
      simp [nativeComplexCameraVector, atlasSixCameraIndex, sixCamera,
        RealHilbertComplexification.complexInner,
        h0, h1, h2, h3, h4, h5]
  change inner ℂ nativeMixedVector (∑ i, c i • _) = _
  simp only [inner_sum, inner_smul_right, he]
  simp
  ring

theorem nativeMixedVector_norm_sq : ‖nativeMixedVector‖ ^ 2 = 278 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  have h := nativeMixedVector_inner_synthesis nativeMixedRay
  change inner ℂ nativeMixedVector nativeMixedVector = (278/3 : ℂ) * 3 at h
  simpa using congrArg Complex.re h

theorem nativeMixedUnitVector_norm_sq : ‖nativeMixedUnitVector‖ ^ 2 = 1 := by
  rw [nativeMixedUnitVector, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 278), nativeMixedVector_norm_sq]
  norm_num

theorem nativeMixedCoefficients_pack (x : FiniteC3GreenPortCarrier 3) :
    nativeMixedCoefficients (nativeC3PackedCoefficients x) =
      nativeC3PackedCoefficients (sixCameraMixedReturnPortPart x) := by
  ext i
  fin_cases i
  · change x.2 1 / 3 * (-6) = -2 * x.2 1; ring
  · change x.2 1 / 3 * (-3) = -x.2 1; ring
  · change x.2 1 / 3 * 2 = (2/3 : ℂ) * x.2 1; ring
  · change x.2 1 / 3 * 0 = 0; ring
  · change x.2 1 / 3 * 3 = x.2 1; ring
  · change x.2 1 / 3 * 0 = 0; ring

theorem nativeMixedComplement_pack (x : FiniteC3GreenPortCarrier 3) :
    nativeMixedComplement (nativeC3PackedCoefficients x) =
      nativeC3PackedCoefficients (x - sixCameraMixedReturnPortPart x) := by
  rw [nativeMixedComplement, nativeMixedCoefficients_pack]
  ext i
  fin_cases i <;> rfl

theorem nativeCanonicalMixedSource_eq_original (z : ℂ) :
    nativeSixCameraSynthesis (nativeMixedCoefficients (nativeCanonicalGammaCoefficients z)) =
      canonicalC3ReturnSourcePart z := by
  rw [nativeCanonicalGammaCoefficients, nativeMixedCoefficients_pack,
    nativeSixCameraSynthesis_pack]
  rfl

theorem nativeCanonicalComplementSource_eq_original (z : ℂ) :
    nativeSixCameraSynthesis (nativeMixedComplement (nativeCanonicalGammaCoefficients z)) =
      canonicalC3ReturnSourceRemainder z := by
  rw [nativeCanonicalGammaCoefficients, nativeMixedComplement_pack,
    nativeSixCameraSynthesis_pack]
  rfl

end
end CarrySelfAdjointOperator.GammaMaterialSewing

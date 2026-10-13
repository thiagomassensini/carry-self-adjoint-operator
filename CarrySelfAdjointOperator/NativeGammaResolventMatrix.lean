import CarrySelfAdjointOperator.NativeGammaThreeSectorResolvent
import CarrySelfAdjointOperator.NativeGammaCameraAdjoint
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
open NativeCarrySpectralWeyl.Infinite NativeCarrySpectralWeyl.Finite
noncomputable section
set_option autoImplicit false

theorem nativeSixCameraGram_isHermitian : nativeSixCameraGram.IsHermitian := by
  change nativeSixCameraGramᴴ = nativeSixCameraGram
  ext i j
  simp only [Matrix.conjTranspose_apply, ← nativeSixCameraGram_entry,
    Complex.star_def, inner_conj_symm]

theorem nativeSixCameraProjection_analysisPairing (u v : CarryGammaComplexCamera) :
    star (nativeSixCameraCoordinates u) ⬝ᵥ (nativeSixCameraGram *ᵥ nativeSixCameraCoordinates v) =
      star (nativeSixCameraAnalysis u) ⬝ᵥ (nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis v) := by
  change star (nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis u) ⬝ᵥ
    (nativeSixCameraGram *ᵥ (nativeSixCameraGram⁻¹ *ᵥ nativeSixCameraAnalysis v)) = _
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ nativeSixCameraGram_isUnit,
    Matrix.one_mulVec, Matrix.star_mulVec, nativeSixCameraGram_isHermitian.inv.eq,
    ← Matrix.dotProduct_mulVec]

def nativeGammaCauchyMatrix (z : ℂ) (hz : z.im ≠ 0) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => inner ℂ (nativeComplexCameraVector (atlasSixCameraIndex i))
    (nativeComplexCauchy z hz (nativeComplexCameraVector (atlasSixCameraIndex j)))

def nativeGammaHaloMatrix (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => inner ℂ
    (nativeSixCameraExterior (nativeComplexCauchy z hz (nativeComplexCameraVector (atlasSixCameraIndex i))))
    (nativeSixCameraExterior (nativeComplexCauchy w hw (nativeComplexCameraVector (atlasSixCameraIndex j))))

def nativeGammaEscapeMatrix (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => inner ℂ (nativeGammaGlobalEscape z hz (nativeComplexCameraVector (atlasSixCameraIndex i)))
    (nativeGammaGlobalEscape w hw (nativeComplexCameraVector (atlasSixCameraIndex j)))

theorem nativeGammaCauchyMatrix_analysis (z : ℂ) (hz : z.im ≠ 0) (j : Fin 6) :
    nativeSixCameraAnalysis (nativeComplexCauchy z hz (nativeComplexCameraVector (atlasSixCameraIndex j))) =
      fun i => nativeGammaCauchyMatrix z hz i j := rfl

theorem nativeGammaCauchyMatrix_compressedGram (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (i j : Fin 6) :
    star (nativeSixCameraCoordinates (nativeComplexCauchy z hz (nativeComplexCameraVector (atlasSixCameraIndex i)))) ⬝ᵥ
      (nativeSixCameraGram *ᵥ nativeSixCameraCoordinates
        (nativeComplexCauchy w hw (nativeComplexCameraVector (atlasSixCameraIndex j)))) =
      ((nativeGammaCauchyMatrix z hz)ᴴ * nativeSixCameraGram⁻¹ * nativeGammaCauchyMatrix w hw) i j := by
  rw [nativeSixCameraProjection_analysisPairing]
  simp only [nativeGammaCauchyMatrix_analysis, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem nativeGammaResolvent_matrixIdentity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    (nativeGammaCauchyMatrix z hz)ᴴ - nativeGammaCauchyMatrix w hw =
      (w - conj z) • ((nativeGammaCauchyMatrix z hz)ᴴ * nativeSixCameraGram⁻¹ *
        nativeGammaCauchyMatrix w hw + nativeGammaHaloMatrix z w hz hw + nativeGammaEscapeMatrix z w hz hw) := by
  ext i j
  have h := carryGammaComplex_twoParameter_greenIdentity z w hz hw
    (nativeComplexCameraVector (atlasSixCameraIndex i))
    (nativeComplexCameraVector (atlasSixCameraIndex j))
  rw [nativeGammaResolvent_fullGram, nativeSixCameraProjection_metricLedger,
    nativeGammaCauchyMatrix_compressedGram] at h
  change conj (nativeGammaCauchyMatrix z hz j i) - nativeGammaCauchyMatrix w hw i j =
    (w - conj z) * ((_ + _) + _)
  simp only [nativeGammaCauchyMatrix, nativeGammaHaloMatrix, nativeGammaEscapeMatrix,
    inner_conj_symm, nativeComplexCauchy_apply] at h ⊢
  linear_combination h

theorem nativeGammaResolvent_matrixIdentity_divided (z w : ℂ) (hz : z.im ≠ 0)
    (hw : w.im ≠ 0) (hsep : w - conj z ≠ 0) :
    (w - conj z)⁻¹ • ((nativeGammaCauchyMatrix z hz)ᴴ - nativeGammaCauchyMatrix w hw) =
      (nativeGammaCauchyMatrix z hz)ᴴ * nativeSixCameraGram⁻¹ * nativeGammaCauchyMatrix w hw +
        nativeGammaHaloMatrix z w hz hw + nativeGammaEscapeMatrix z w hz hw := by
  rw [nativeGammaResolvent_matrixIdentity, smul_smul, inv_mul_cancel₀ hsep, one_smul]

def nativeGammaHermitianImaginary (A : Matrix (Fin 6) (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (2 * Complex.I)⁻¹ • (A - Aᴴ)

theorem nativeGammaResolvent_upperHalfPlane (z : ℂ) (hz : 0 < z.im) :
    (-(z.im : ℂ)⁻¹) • nativeGammaHermitianImaginary (nativeGammaCauchyMatrix z hz.ne') =
      (nativeGammaCauchyMatrix z hz.ne')ᴴ * nativeSixCameraGram⁻¹ * nativeGammaCauchyMatrix z hz.ne' +
      nativeGammaHaloMatrix z z hz.ne' hz.ne' + nativeGammaEscapeMatrix z z hz.ne' hz.ne' := by
  have h := nativeGammaResolvent_matrixIdentity z z hz.ne' hz.ne'
  have he : z - conj z = (2 * Complex.I) * (z.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [he] at h
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  ext i j
  have hij := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℂ => A i j) h
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hij
  simp only [nativeGammaHermitianImaginary, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hij

end
end CarrySelfAdjointOperator.GammaMaterialSewing

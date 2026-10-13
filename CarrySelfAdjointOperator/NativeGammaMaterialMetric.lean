import CarrySelfAdjointOperator.NativeGammaMaterialTransport

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace
open PhysicalSewing NativeLaguerre NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

def materialCameraLiftMatrix (C : ℕ) : Matrix (Fin (materialCameraWindow C)) (Fin 6) ℂ :=
  fun j i => (materialCameraPolynomial C i).coeff j.val

def materialCameraGram (C : ℕ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (materialCameraLiftMatrix C)ᴴ * cauchyMatrix (materialCameraWindow C) * materialCameraLiftMatrix C

def materialCameraMetricDefect (C : ℕ) : Matrix (Fin 6) (Fin 6) ℂ :=
  nativeSixCameraGram - materialCameraGram C

theorem materialCameraGram_pairing (C : ℕ) (c d : Fin 6 → ℂ) :
    matrixPairing (materialCameraGram C) c d =
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (materialCameraLift C c) (materialCameraLift C d) := by
  unfold matrixPairing materialCameraGram
  change star c ⬝ᵥ (((materialCameraLiftMatrix C)ᴴ * cauchyMatrix (materialCameraWindow C) *
      materialCameraLiftMatrix C) *ᵥ d) =
    star (materialCameraLiftMatrix C *ᵥ c) ⬝ᵥ
      (cauchyMatrix (materialCameraWindow C) *ᵥ (materialCameraLiftMatrix C *ᵥ d))
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem materialCameraMetricDefect_pairing (C : ℕ) (c d : Fin 6 → ℂ) :
    matrixPairing nativeSixCameraGram c d =
      matrixPairing (materialCameraGram C) c d + matrixPairing (materialCameraMetricDefect C) c d := by
  simp only [materialCameraMetricDefect, matrixPairing, Matrix.sub_mulVec, dotProduct_sub]
  ring

theorem gammaMaterialTransport_metricLedger (C : ℕ) (u v : CarryGammaComplexCamera) :
    inner ℂ u v =
      matrixPairing (cauchyMatrix (materialCameraWindow C))
        (materialCameraLift C (nativeSixCameraCoordinates u))
        (materialCameraLift C (nativeSixCameraCoordinates v)) +
      matrixPairing (materialCameraMetricDefect C) (nativeSixCameraCoordinates u) (nativeSixCameraCoordinates v) +
      inner ℂ (nativeSixCameraExterior u) (nativeSixCameraExterior v) := by
  rw [nativeSixCameraProjection_metricLedger]
  change matrixPairing nativeSixCameraGram _ _ + _ = _
  rw [materialCameraMetricDefect_pairing, materialCameraGram_pairing]

def nativeGammaPairForm (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) : ℂ :=
  inner ℂ p.1 t.2 - inner ℂ p.2 t.1

def gammaMaterialMetricFormDefect (C : ℕ) (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) : ℂ :=
  matrixPairing (materialCameraMetricDefect C) (nativeSixCameraCoordinates p.1) (nativeSixCameraCoordinates t.2) -
    matrixPairing (materialCameraMetricDefect C) (nativeSixCameraCoordinates p.2) (nativeSixCameraCoordinates t.1)

def gammaMaterialExteriorForm (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) : ℂ :=
  inner ℂ (nativeSixCameraExterior p.1) (nativeSixCameraExterior t.2) -
    inner ℂ (nativeSixCameraExterior p.2) (nativeSixCameraExterior t.1)

theorem nativeGammaPairForm_materialLedger (C : ℕ) (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    nativeGammaPairForm p t =
      matrixPairing (cauchyMatrix (materialCameraWindow C))
        (materialCameraLift C (nativeSixCameraCoordinates p.1))
        (materialCameraLift C (nativeSixCameraCoordinates t.2)) -
      matrixPairing (cauchyMatrix (materialCameraWindow C))
        (materialCameraLift C (nativeSixCameraCoordinates p.2))
        (materialCameraLift C (nativeSixCameraCoordinates t.1)) +
      gammaMaterialMetricFormDefect C p t + gammaMaterialExteriorForm p t := by
  unfold nativeGammaPairForm gammaMaterialMetricFormDefect gammaMaterialExteriorForm
  rw [gammaMaterialTransport_metricLedger C p.1 t.2, gammaMaterialTransport_metricLedger C p.2 t.1]
  ring

theorem nativeSixCameraGram_two_three : nativeSixCameraGram 0 1 = 0 := by
  norm_num [nativeSixCameraGram, sixCameraGram, sixCameraGramRat]

theorem materialCameraGram_one_two_three : materialCameraGram 1 0 1 = (139/252 : ℂ) := by
  let J : Matrix (Fin 10) (Fin 6) ℂ := fun j i => (materialCameraPolynomial 1 i).coeff j.val
  change (Jᴴ * cauchyMatrix 10 * J) 0 1 = _
  norm_num [J,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    materialCameraPolynomial, materialStencilPolynomial_coeff_address, finiteStencil_apply,
    finiteCoefficient, seedCoefficient, centerCoefficient, bracketCoefficient, sixCamera,
    FiniteNativeCarryOperator.Camera.radiusSet, FiniteNativeCarryOperator.Camera.halfRange,
    FiniteNativeCarryOperator.Camera.alignedCenter, Finset.sum_range_succ, Finset.sum_Icc_succ_top,
    cauchyMatrix, cauchyEntry, map_add, map_mul, map_sub, map_ofNat]

theorem materialCameraLift_literal_not_isometric : materialCameraGram 1 ≠ nativeSixCameraGram := by
  intro he
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => M 0 1) he
  rw [materialCameraGram_one_two_three, nativeSixCameraGram_two_three] at h
  norm_num at h

theorem materialCameraLift_diagonal_rescaling_not_isometric (d : Fin 6 → ℂ)
    (h0 : d 0 ≠ 0) (h1 : d 1 ≠ 0) :
    Matrix.diagonal (star d) * materialCameraGram 1 * Matrix.diagonal d ≠ nativeSixCameraGram := by
  intro he
  have h := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => M 0 1) he
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply,
    materialCameraGram_one_two_three, nativeSixCameraGram_two_three] at h
  exact (mul_ne_zero (mul_ne_zero (star_ne_zero.mpr h0) (by norm_num)) h1) h

/-- The effective native orientation, for arbitrary independent ambient pairs.
The exterior is retained with the native sign, not discarded by projection. -/
theorem nativeGammaNativeOrientation_materialLedger (C : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    inner ℂ p.2 t.1 - inner ℂ p.1 t.2 =
      matrixPairing (cauchyMatrix (materialCameraWindow C))
        (materialCameraLift C (nativeSixCameraCoordinates p.2))
        (materialCameraLift C (nativeSixCameraCoordinates t.1)) -
      matrixPairing (cauchyMatrix (materialCameraWindow C))
        (materialCameraLift C (nativeSixCameraCoordinates p.1))
        (materialCameraLift C (nativeSixCameraCoordinates t.2)) -
      gammaMaterialMetricFormDefect C p t +
      (inner ℂ (nativeSixCameraExterior p.2) (nativeSixCameraExterior t.1) -
        inner ℂ (nativeSixCameraExterior p.1) (nativeSixCameraExterior t.2)) := by
  have h := nativeGammaPairForm_materialLedger C p t
  unfold nativeGammaPairForm gammaMaterialExteriorForm at h
  linear_combination -h

end
end CarrySelfAdjointOperator.GammaMaterialSewing

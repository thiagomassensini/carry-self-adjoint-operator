import CarrySelfAdjointOperator.NativeGammaMaterialMetric
import CarrySelfAdjointOperator.NativeGammaMaterialGraphDefect
import CarrySelfAdjointOperator.NativeSourceLocusGreenCompatibility

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped InnerProductSpace Matrix ComplexConjugate
open PhysicalSewing NativeLaguerre
noncomputable section
set_option autoImplicit false

def nativeCanonicalGammaPair (z : ℂ) (hz : z.im ≠ 0) :
    CarryGammaComplexCamera × CarryGammaComplexCamera :=
  (nativeCanonicalGammaSource z,nativeCanonicalGammaCauchyTrace z hz)

def gammaPhysicalGreenScale (k : ℕ) : ℂ := 2*Complex.I/((k : ℂ)+1)

theorem gammaPhysicalGreenScale_form (N k : ℕ) (v s w t : Fin N → ℂ) :
    gammaPhysicalGreenScale k * canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis N k v s) (twoPortSynthesis N k w t) =
    matrixPairing (cauchyMatrix N) v t - matrixPairing (cauchyMatrix N) s w := by
  rw [twoPort_signed_form]
  have hK : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hc : gammaPhysicalGreenScale k * (Complex.I*((k : ℂ)+1)/2) = -1 := by
    unfold gammaPhysicalGreenScale
    field_simp
    simp
  rw [← mul_assoc, hc]
  ring

def nativeGammaMetricDefect (C : ℕ) (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) : ℂ :=
  gammaMaterialMetricFormDefect C (nativeCanonicalGammaPair z hz) (nativeCanonicalGammaPair w hw)

/-- The reference dictionary remains a named defect, never assumed zero. -/
def nativeGammaReferenceDefect (C k : ℕ) (z w : ℂ) : ℂ :=
  gammaPhysicalGreenScale k * canonicalCompletedNativeProjectiveChiralForm
    (twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
      (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j))
    (twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C w)
      (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C w j)) -
    canonicalCompletedC3NativeSourceLocusScalarGreenForm z w

theorem nativeGammaCanonicalExterior_sector_zero (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    gammaMaterialExteriorForm (nativeCanonicalGammaPair z hz) (nativeCanonicalGammaPair w hw) = 0 := by
  simp [gammaMaterialExteriorForm, nativeCanonicalGammaPair, nativeCanonicalGammaSource_noExterior]

theorem nativeGammaPairForm_original (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NativeSourceLocusGammaGreenForm z w hz hw =
      -nativeGammaPairForm (nativeCanonicalGammaPair z hz) (nativeCanonicalGammaPair w hw) := by
  rw [canonicalCompletedC3NativeSourceLocusGammaGreenForm_eq_canonical]
  change inner ℂ (nativeCanonicalGammaCauchyTrace z hz) (nativeCanonicalGammaSource w) -
      inner ℂ (nativeCanonicalGammaSource z) (nativeCanonicalGammaCauchyTrace w hw) =
    -(inner ℂ (nativeCanonicalGammaSource z) (nativeCanonicalGammaCauchyTrace w hw) -
      inner ℂ (nativeCanonicalGammaCauchyTrace z hz) (nativeCanonicalGammaSource w))
  ring

theorem physicalSecondDefect_polarizedLedger (N : ℕ) (theta v s w t : Fin N → ℂ) :
    matrixPairing (cauchyMatrix N) v t - matrixPairing (cauchyMatrix N) s w =
    (matrixPairing (cauchyMatrix N) v (fun j => theta j*w j) -
      matrixPairing (cauchyMatrix N) (fun j => theta j*v j) w) +
    matrixPairing (cauchyMatrix N) v (secondPortDefect N theta w t) -
      matrixPairing (cauchyMatrix N) (secondPortDefect N theta v s) w := by
  simp only [secondPortDefect, matrixPairing, Matrix.mulVec_sub, star_sub,
    dotProduct_sub, sub_dotProduct]
  ring

theorem nativeGammaUserOrientation_materialDefectLedger (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    nativeGammaPairForm (nativeCanonicalGammaPair z hz) (nativeCanonicalGammaPair w hw) -
      canonicalCompletedC3NativeSourceLocusScalarGreenForm z w =
      nativeGammaMetricDefect C z w hz hw + nativeGammaReferenceDefect C k z w +
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialGraphDefect C k w hw) -
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialGraphDefect C k z hz)
        (nativeGammaMaterialFirstPort C w) := by
  have hg := nativeGammaPairForm_materialLedger C (nativeCanonicalGammaPair z hz)
    (nativeCanonicalGammaPair w hw)
  rw [nativeGammaCanonicalExterior_sector_zero, add_zero] at hg
  rw [hg]
  simp only [nativeCanonicalGammaPair, nativeCanonicalGammaSource_coordinates]
  change (matrixPairing (cauchyMatrix (materialCameraWindow C))
      (nativeGammaMaterialFirstPort C z) (nativeGammaMaterialSecondPort C w hw) -
    matrixPairing (cauchyMatrix (materialCameraWindow C))
      (nativeGammaMaterialSecondPort C z hz) (nativeGammaMaterialFirstPort C w) +
    nativeGammaMetricDefect C z w hz hw) -
      canonicalCompletedC3NativeSourceLocusScalarGreenForm z w = _
  rw [physicalSecondDefect_polarizedLedger _ (radialResponse (materialCameraWindow C) k)]
  unfold nativeGammaReferenceDefect
  rw [gammaPhysicalGreenScale_form]
  change _ = _ + _ + matrixPairing _ _ (secondPortDefect _ _ _ _) -
    matrixPairing _ (secondPortDefect _ _ _ _) _
  ring

/-- The existing mismatch uses the OPPOSITE boundary orientation in its Gamma term. -/
theorem nativeGammaMismatch_materialDefectLedger (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      -nativeGammaMetricDefect C z w hz hw - nativeGammaReferenceDefect C k z w -
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialGraphDefect C k w hw) +
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialGraphDefect C k z hz)
        (nativeGammaMaterialFirstPort C w) -
      2*canonicalCompletedC3NativeSourceLocusScalarGreenForm z w := by
  have h := nativeGammaUserOrientation_materialDefectLedger C k z w hz hw
  unfold canonicalCompletedC3NativeSourceLocusProjectionMismatch
  rw [nativeGammaPairForm_original]
  linear_combination -h

theorem nativeGammaMismatch_proposedLedgerDifference (C k : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw -
      (nativeGammaMetricDefect C z w hz hw + nativeGammaReferenceDefect C k z w +
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialGraphDefect C k w hw) -
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (nativeGammaMaterialGraphDefect C k z hz)
        (nativeGammaMaterialFirstPort C w)) =
      -2*nativeGammaPairForm (nativeCanonicalGammaPair z hz) (nativeCanonicalGammaPair w hw) := by
  rw [← nativeGammaUserOrientation_materialDefectLedger C k z w hz hw]
  unfold canonicalCompletedC3NativeSourceLocusProjectionMismatch
  rw [nativeGammaPairForm_original]
  ring

end
end CarrySelfAdjointOperator.GammaMaterialSewing

import CarrySelfAdjointOperator.NativeGammaMaterialCrossings
import CarrySelfAdjointOperator.NativeGammaMismatchLedger

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators ComplexConjugate Matrix InnerProductSpace
open PhysicalSewing NativeLaguerre
noncomputable section
set_option autoImplicit false

def gammaPhysicalPairHeadTail (N R : ℕ) (v w : Fin N → ℂ) : ℂ :=
  (∑ r : Fin (R+1), conj (laguerreReadout r.val v) * laguerreReadout r.val w) +
    matrixPairing (tailDiagonal R N * cauchyMatrix N * tailDiagonal R N) v w

theorem gammaPhysicalPair_headTail (N R : ℕ) (v w : Fin N → ℂ) :
    matrixPairing (cauchyMatrix N) v w = gammaPhysicalPairHeadTail N R v w :=
  matrixPairing_head_tail R N v w

theorem materialCameraMetricDefect_pairing_sub (C : ℕ) (c d : Fin 6 → ℂ) :
    matrixPairing (materialCameraMetricDefect C) c d = matrixPairing nativeSixCameraGram c d -
      matrixPairing (cauchyMatrix (materialCameraWindow C)) (materialCameraLift C c) (materialCameraLift C d) := by
  have h := materialCameraMetricDefect_pairing C c d
  rw [materialCameraGram_pairing] at h
  linear_combination -h

theorem gammaMaterialMetricFormDefect_headTail (C R : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    gammaMaterialMetricFormDefect C p t =
      matrixPairing nativeSixCameraGram (nativeSixCameraCoordinates p.1) (nativeSixCameraCoordinates t.2) -
      matrixPairing nativeSixCameraGram (nativeSixCameraCoordinates p.2) (nativeSixCameraCoordinates t.1) -
      gammaPhysicalPairHeadTail (materialCameraWindow C) R
        (materialCameraLift C (nativeSixCameraCoordinates p.1)) (materialCameraLift C (nativeSixCameraCoordinates t.2)) +
      gammaPhysicalPairHeadTail (materialCameraWindow C) R
        (materialCameraLift C (nativeSixCameraCoordinates p.2)) (materialCameraLift C (nativeSixCameraCoordinates t.1)) := by
  unfold gammaMaterialMetricFormDefect
  rw [materialCameraMetricDefect_pairing_sub, materialCameraMetricDefect_pairing_sub,
    gammaPhysicalPair_headTail _ R, gammaPhysicalPair_headTail _ R]
  ring

theorem nativeGammaReferenceDefect_headTail (C k R : ℕ) (z w : ℂ) :
    nativeGammaReferenceDefect C k z w =
      gammaPhysicalGreenScale k * twoPortPolarizedHeadTail (materialCameraWindow C) k R
        (nativeGammaMaterialFirstPort C z)
        (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j)
        (nativeGammaMaterialFirstPort C w)
        (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C w j) -
      canonicalCompletedC3NativeSourceLocusScalarGreenForm z w := by
  unfold nativeGammaReferenceDefect twoPortPolarizedHeadTail
  rw [twoPort_signed_headTail _ k R]

theorem nativeGammaMismatch_materialHeadTailLedger (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedC3NativeSourceLocusProjectionMismatch z w hz hw =
      -nativeGammaMetricDefect C z w hz hw -
      (gammaPhysicalGreenScale k * twoPortPolarizedHeadTail (materialCameraWindow C) k R
        (nativeGammaMaterialFirstPort C z)
        (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j)
        (nativeGammaMaterialFirstPort C w)
        (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C w j) -
        canonicalCompletedC3NativeSourceLocusScalarGreenForm z w) -
      gammaPhysicalPairHeadTail (materialCameraWindow C) R (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialGraphDefect C k w hw) +
      gammaPhysicalPairHeadTail (materialCameraWindow C) R (nativeGammaMaterialGraphDefect C k z hz)
        (nativeGammaMaterialFirstPort C w) - 2*canonicalCompletedC3NativeSourceLocusScalarGreenForm z w := by
  rw [nativeGammaMismatch_materialDefectLedger, nativeGammaReferenceDefect_headTail _ _ R,
    gammaPhysicalPair_headTail _ R, gammaPhysicalPair_headTail _ R]

theorem nativeGammaCamera_graph_plus_defect (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) (i : Fin 6) :
    nativeGammaCameraGraphPort C k z i + nativeGammaCameraDefect C k z hz i =
      nativeGammaCameraSecondPort C z hz i := by
  unfold nativeGammaCameraDefect
  abel

theorem nativeGammaWholePair_camera_fourHeadTails (C k R : ℕ) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z) (nativeGammaMaterialSecondPort C z hz))
      (twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C w) (nativeGammaMaterialSecondPort C w hw)) =
    ∑ i, ∑ j,
      (twoPortPolarizedHeadTail (materialCameraWindow C) k R (nativeGammaCameraFirstPort C z i)
        (nativeGammaCameraGraphPort C k z i) (nativeGammaCameraFirstPort C w j) (nativeGammaCameraGraphPort C k w j) +
      twoPortPolarizedHeadTail (materialCameraWindow C) k R (nativeGammaCameraFirstPort C z i)
        (nativeGammaCameraGraphPort C k z i) 0 (nativeGammaCameraDefect C k w hw j) +
      twoPortPolarizedHeadTail (materialCameraWindow C) k R 0 (nativeGammaCameraDefect C k z hz i)
        (nativeGammaCameraFirstPort C w j) (nativeGammaCameraGraphPort C k w j) +
      twoPortPolarizedHeadTail (materialCameraWindow C) k R 0 (nativeGammaCameraDefect C k z hz i)
        0 (nativeGammaCameraDefect C k w hw j)) := by
  have h := nativeGammaCamera_fourHeadTails C k R z w hz hw
  simpa only [nativeGammaCamera_graph_plus_defect, nativeGammaCameraWholePair_sum] using h

/-- The native exterior and the Laguerre tails remain separate in the
effective native orientation, with two arbitrary ambient inputs. -/
theorem nativeGammaNativeOrientation_materialHeadTailLedger (C R : ℕ)
    (p t : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    inner ℂ p.2 t.1 - inner ℂ p.1 t.2 =
      gammaPhysicalPairHeadTail (materialCameraWindow C) R
        (materialCameraLift C (nativeSixCameraCoordinates p.2))
        (materialCameraLift C (nativeSixCameraCoordinates t.1)) -
      gammaPhysicalPairHeadTail (materialCameraWindow C) R
        (materialCameraLift C (nativeSixCameraCoordinates p.1))
        (materialCameraLift C (nativeSixCameraCoordinates t.2)) -
      gammaMaterialMetricFormDefect C p t +
      (inner ℂ (nativeSixCameraExterior p.2) (nativeSixCameraExterior t.1) -
        inner ℂ (nativeSixCameraExterior p.1) (nativeSixCameraExterior t.2)) := by
  rw [nativeGammaNativeOrientation_materialLedger,
    gammaPhysicalPair_headTail _ R, gammaPhysicalPair_headTail _ R]

end
end CarrySelfAdjointOperator.GammaMaterialSewing

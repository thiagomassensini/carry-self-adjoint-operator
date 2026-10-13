import CarrySelfAdjointOperator.NativeGammaCanonicalSource
import CarrySelfAdjointOperator.NativeGammaMaterialTransport
import CarrySelfAdjointOperator.NativePhysicalObservableCapstone

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped Matrix
open PhysicalSewing NativeLaguerre
noncomputable section
set_option autoImplicit false

def nativeGammaMaterialFirstPort (C : ℕ) (z : ℂ) : Fin (materialCameraWindow C) → ℂ :=
  materialCameraLift C (nativeCanonicalGammaCoefficients z)

/-- The candidate is produced by the original Cauchy, without consulting theta. -/
def nativeGammaMaterialSecondPort (C : ℕ) (z : ℂ) (hz : z.im ≠ 0) : Fin (materialCameraWindow C) → ℂ :=
  materialCameraLift C (nativeSixCameraCoordinates (nativeCanonicalGammaCauchyTrace z hz))

def nativeGammaMaterialGraphDefect (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    Fin (materialCameraWindow C) → ℂ :=
  secondPortDefect (materialCameraWindow C) (radialResponse (materialCameraWindow C) k)
    (nativeGammaMaterialFirstPort C z) (nativeGammaMaterialSecondPort C z hz)

def nativeGammaMaterialProbes (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) : Fin (materialCameraWindow C) → ℂ :=
  mixedPhysicalProbes (materialCameraWindow C) k (radialResponse (materialCameraWindow C) k)
    (nativeGammaMaterialGraphDefect C k z hz)

theorem gammaMaterialGraphDefect_entirePair (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz) -
      twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j) =
      twoPortSynthesis (materialCameraWindow C) k 0 (nativeGammaMaterialGraphDefect C k z hz) := by
  have ha := twoPortSynthesis_add_secondDefect (materialCameraWindow C) k
    (nativeGammaMaterialFirstPort C z)
    (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j)
    (nativeGammaMaterialGraphDefect C k z hz)
  have hs : (fun j => radialResponse (materialCameraWindow C) k j * nativeGammaMaterialFirstPort C z j) +
      nativeGammaMaterialGraphDefect C k z hz = nativeGammaMaterialSecondPort C z hz := by
    unfold nativeGammaMaterialGraphDefect secondPortDefect
    abel
  rw [hs] at ha
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using ha

theorem gammaMaterialGraphDefect_probeFormula (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaMaterialProbes C k z hz = mixedProbeScale k •
      ((cauchyMatrix (materialCameraWindow C)) *ᵥ nativeGammaMaterialGraphDefect C k z hz) :=
  mixedPhysicalProbes_formula _ _ _ _

theorem gammaMaterialGraphDefect_faithful (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    (∀ a, nativeGammaMaterialProbes C k z hz a = 0) ↔ nativeGammaMaterialGraphDefect C k z hz = 0 :=
  mixedPhysicalProbes_faithful _ _ _ _

theorem gammaMaterialGraphDefect_decode (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    nativeGammaMaterialGraphDefect C k z hz = (2*Complex.I/((k : ℂ)+1)) •
      ((cauchyMatrix (materialCameraWindow C))⁻¹ *ᵥ nativeGammaMaterialProbes C k z hz) :=
  mixedPhysicalProbes_decode _ _ _ _

theorem gammaMaterialGraphDefect_vs_completedSource (C k : ℕ) (z : ℂ) (hz : z.im ≠ 0)
    (hreg : ∀ j : Fin (materialCameraWindow C),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    (∀ a, nativeGammaMaterialProbes C k z hz a = 0) ↔
      twoPortSynthesis (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z)
        (nativeGammaMaterialSecondPort C z hz) =
      finiteProjectiveSource (materialCameraWindow C) k (nativeGammaMaterialFirstPort C z) :=
  physicalCandidate_wholePair_iff_probes _ _ _ _ hreg

end
end CarrySelfAdjointOperator.GammaMaterialSewing

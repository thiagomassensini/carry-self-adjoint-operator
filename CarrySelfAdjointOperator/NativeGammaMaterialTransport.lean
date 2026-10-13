import CarrySelfAdjointOperator.NativeGammaMaterialDecoder
import CarrySelfAdjointOperator.NativeGammaCameraAdjoint
import CarrySelfAdjointOperator.NativePhysicalMixedProbes

namespace CarrySelfAdjointOperator.GammaMaterialSewing
open scoped BigOperators InnerProductSpace Matrix ComplexConjugate ComplexOrder
open PhysicalSewing NativeLaguerre ChiralReturn
noncomputable section
set_option autoImplicit false

def physicalRadialFiniteReadout (N k : ℕ) (f : CanonicalCompletedNativeChiralCauchyCarrier) : Fin N → ℂ :=
  fun a => inner ℂ (radialIncidentSynthesis k N (Pi.single a 1)) f

theorem physicalRadialFiniteReadout_synthesis (N k : ℕ) (v : Fin N → ℂ) :
    physicalRadialFiniteReadout N k (radialIncidentSynthesis k N v) =
      ((k : ℂ)+1) • ((cauchyMatrix N) *ᵥ v) := by
  funext a
  rw [physicalRadialFiniteReadout, incident_inner_eq_matrixPairing]
  simp [matrixPairing, dotProduct, Pi.single_apply]

/-- Coordinate decoding in the fixed physical basis, after whole synthesis. -/
def physicalRadialFiniteDecode (N k : ℕ) (f : CanonicalCompletedNativeChiralCauchyCarrier) : Fin N → ℂ :=
  ((k : ℂ)+1)⁻¹ • ((cauchyMatrix N)⁻¹ *ᵥ physicalRadialFiniteReadout N k f)

theorem physicalRadialFiniteDecode_synthesis (N k : ℕ) (v : Fin N → ℂ) :
    physicalRadialFiniteDecode N k (radialIncidentSynthesis k N v) = v := by
  have hu : IsUnit (cauchyMatrix N).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (cauchyMatrix_posDef N).isUnit
  have hK : (k : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [physicalRadialFiniteDecode, physicalRadialFiniteReadout_synthesis, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec,
    smul_smul, inv_mul_cancel₀ hK, one_smul]

def physicalFinitePairDecode (N k : ℕ) (f : CanonicalCompletedNativeProjectiveChiralCarrier) :
    (Fin N → ℂ) × (Fin N → ℂ) :=
  (physicalRadialFiniteDecode N k (twoPortChart f).1,
    physicalRadialFiniteDecode N k (twoPortChart f).2)

theorem physicalFinitePairDecode_synthesis (N k : ℕ) (v s : Fin N → ℂ) :
    physicalFinitePairDecode N k (twoPortSynthesis N k v s) = (v,s) := by
  simp only [physicalFinitePairDecode, twoPortSynthesis_chart, physicalRadialFiniteDecode_synthesis]

abbrev GammaMaterialTransportCarrier := CanonicalCompletedNativeProjectiveChiralCarrier ×
  (CarryGammaComplexCamera × CarryGammaComplexCamera)

/-- Both exterior vectors are retained in their original native carrier. -/
def gammaMaterialTransport (C k : ℕ) (p : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    GammaMaterialTransportCarrier :=
  (twoPortSynthesis (materialCameraWindow C) k
      (materialCameraLift C (nativeSixCameraCoordinates p.1))
      (materialCameraLift C (nativeSixCameraCoordinates p.2)),
    (nativeSixCameraExterior p.1,nativeSixCameraExterior p.2))

def gammaMaterialReconstruct (C k : ℕ) (p : GammaMaterialTransportCarrier) :
    CarryGammaComplexCamera × CarryGammaComplexCamera :=
  (nativeSixCameraSynthesis (materialCameraDecode C (physicalFinitePairDecode
      (materialCameraWindow C) k p.1).1) + p.2.1,
    nativeSixCameraSynthesis (materialCameraDecode C (physicalFinitePairDecode
      (materialCameraWindow C) k p.1).2) + p.2.2)

theorem gammaMaterialTransport_roundtrip (C k : ℕ) (hC : 1 ≤ C)
    (p : CarryGammaComplexCamera × CarryGammaComplexCamera) :
    gammaMaterialReconstruct C k (gammaMaterialTransport C k p) = p := by
  simp only [gammaMaterialReconstruct, gammaMaterialTransport, physicalFinitePairDecode_synthesis,
    materialCameraDecode_lift C hC]
  exact Prod.ext (nativeSixCameraProjection_roundtrip p.1).symm
    (nativeSixCameraProjection_roundtrip p.2).symm

theorem gammaMaterialTransport_injective (C k : ℕ) (hC : 1 ≤ C) :
    Function.Injective (gammaMaterialTransport C k) := by
  intro p t h
  have he := congrArg (gammaMaterialReconstruct C k) h
  simpa only [gammaMaterialTransport_roundtrip C k hC] using he

end
end CarrySelfAdjointOperator.GammaMaterialSewing

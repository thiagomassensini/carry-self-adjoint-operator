import CarrySelfAdjointOperator.NativePhysicalCameraCrossings
import CarrySelfAdjointOperator.NativePhysicalTfvdSecondPort
import CarrySelfAdjointOperator.NativePhysicalValveExtension

namespace CarrySelfAdjointOperator.PhysicalSewing
open scoped BigOperators
open NativeLaguerre NativeCauchyPorts CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false

theorem mixedPhysicalProbe_originalColumn (N k : ℕ) (d : Fin N → ℂ) (a : Fin N)
    (hreg : ∀ j : Fin N,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    mixedPhysicalProbes N k (radialResponse N k) d a =
      canonicalCompletedNativeProjectiveChiralForm
        (canonicalCompletedNativeRadialProjectiveChiralState k a.val) (twoPortSynthesis N k 0 d) := by
  unfold mixedPhysicalProbes
  rw [← finiteProjectiveSource_eq_twoPorts N k (Pi.single a 1) hreg]
  simp [finiteProjectiveSource, Pi.single_apply]

/-- A candidate second port is independently supplied. Equality of whole
pairs is certified exactly by the faithful mixed probes. -/
theorem physicalCandidate_wholePair_iff_probes (N k : ℕ) (v wG : Fin N → ℂ)
    (hreg : ∀ j : Fin N,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    (∀ a, mixedPhysicalProbes N k (radialResponse N k)
      (secondPortDefect N (radialResponse N k) v wG) a = 0) ↔
    twoPortSynthesis N k v wG = finiteProjectiveSource N k v := by
  rw [mixedPhysicalProbes_faithful, finiteProjectiveSource_eq_twoPorts N k v hreg]
  change (wG - (fun j : Fin N => radialResponse N k j*v j) = 0) ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    rw [h]
  · intro h
    have he : (v,wG) = (v,fun j : Fin N => radialResponse N k j*v j) :=
      twoPortSynthesis_injective N k h
    exact congrArg Prod.snd he

/-- Finite observable capstone. Every route identifies the original whole
pair; the independently supplied candidate is tested before scalar energy. -/
theorem physicalFiniteObservable_capstone (n k M : ℕ) (v wG : Fin (2*n) → ℂ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hstrip : ∀ j : Fin (2*n), operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈
      genuineCriticalStrip)
    (hreg : ∀ j : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    nativeSourceProjectiveBoundaryJetSynthesis n k (physicalEndpointJetInput (2*n) k v) =
        finiteProjectiveSource (2*n) k v ∧
    finiteProjectiveSource (2*n) k v =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (finRadialCoefficients (2*n) v) +
          physicalGreenResidualNumerator q k (finRadialCoefficients (2*n) v)) ∧
    tfvdMaterialWholeSource (2*n) M k v
      (fun j => canonicalC3BracketTfvdCompletionState M
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j))) =
        finiteProjectiveSource (2*n) k v ∧
    ((∀ a, mixedPhysicalProbes (2*n) k (radialResponse (2*n) k)
        (secondPortDefect (2*n) (radialResponse (2*n) k) v wG) a = 0) ↔
      twoPortSynthesis (2*n) k v wG = finiteProjectiveSource (2*n) k v) := by
  exact ⟨(physicalFiniteSewing_capstone n k v q hq0 hq1).1,
    (physicalFiniteSewing_capstone n k v q hq0 hq1).2,
    tfvdMaterialWholeSource_canonical (2*n) M k v hstrip hreg,
    physicalCandidate_wholePair_iff_probes (2*n) k v wG hreg⟩

/-- Concrete application to the independently defined original material
producer. Its seed/centers/radii remain in FormalStencil. -/
theorem originalMaterial_observable_capstone (k M : ℕ) (s : FormalStencil)
    (wG : Fin (2*materialStencilHalfWindow s) → ℂ)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hstrip : ∀ j : Fin (2*materialStencilHalfWindow s),
      operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j) ∈ genuineCriticalStrip)
    (hreg : ∀ j : Fin (2*materialStencilHalfWindow s),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    nativeSourceProjectiveBoundaryJetSynthesis (materialStencilHalfWindow s) k
      (physicalEndpointJetInput (2*materialStencilHalfWindow s) k (materialStencilCoefficients s)) =
        originalMaterialCompletedSource k s ∧
    originalMaterialCompletedSource k s =
      (q : ℂ) • ((physicalPairGreenResolvent q hq0.le hq1)^2)
        (physicalGreenBulkBoundary q k (materialStencilRadialCoefficients s) +
          physicalGreenResidualNumerator q k (materialStencilRadialCoefficients s)) ∧
    tfvdMaterialWholeSource (2*materialStencilHalfWindow s) M k (materialStencilCoefficients s)
      (fun j => canonicalC3BracketTfvdCompletionState M
        (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k j))) =
        originalMaterialCompletedSource k s ∧
    ((∀ a, mixedPhysicalProbes (2*materialStencilHalfWindow s) k
      (radialResponse (2*materialStencilHalfWindow s) k)
      (secondPortDefect (2*materialStencilHalfWindow s)
        (radialResponse (2*materialStencilHalfWindow s) k) (materialStencilCoefficients s) wG) a = 0) ↔
      twoPortSynthesis (2*materialStencilHalfWindow s) k (materialStencilCoefficients s) wG =
        originalMaterialCompletedSource k s) := by
  have he : originalMaterialCompletedSource k s =
      finiteProjectiveSource (2*materialStencilHalfWindow s) k (materialStencilCoefficients s) := by
    rw [originalMaterialCompletedSource_eq_physical, materialStencilRadialCoefficients_eq_fin,
      physicalCompletedFiniteSource_fin]
  rw [he, materialStencilRadialCoefficients_eq_fin]
  exact physicalFiniteObservable_capstone (materialStencilHalfWindow s) k M
    (materialStencilCoefficients s) wG q hq0 hq1 hstrip hreg

end
end CarrySelfAdjointOperator.PhysicalSewing

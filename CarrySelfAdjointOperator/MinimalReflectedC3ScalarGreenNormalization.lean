import CarrySelfAdjointOperator.MinimalReflectedC3ConfinementSeam
import CarrySelfAdjointOperator.NativeBoundaryArchimedeanDressingSeparation
import CarrySelfAdjointOperator.CompletedC3BracketTfvdGreenFactorization
import Mathlib.Tactic

/-!
# Public-Genuine normalization of the reflected C3 Green frontier

The public scalar boundary in `NativeCarryC3Crosswalk` is not an additional
scalar carrier: in intrinsic carry time it is exactly the undressed native
height scalar.  The passage to the completed characteristic is instead the
explicit triangular dressing by the xi factor.  This file records that
normalization before comparing it with the completed TFVD ledger.

In particular, no reflected-to-diagonal Gram transport occurs here.
-/

open scoped ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- In intrinsic carry time, the public Genuine boundary value is literally
the undressed native scalar in centered-height coordinates. -/
theorem genuineComplexTimeBoundaryValue_eq_nativeHeightScalar :
    genuineComplexTimeBoundaryValue = nativeHeightScalar := by
  funext z
  unfold genuineComplexTimeBoundaryValue nativeHeightScalar
  rw [carryComplexTimeParameter_eq_operatorHeightParameter]
  exact (nativeScalar_eq_genuineContinuation_unconditional _).symm

/-- The public division-free log jet is the native undressed boundary
companion, because the value functions coincide as functions. -/
theorem genuineComplexTimeLogJet_eq_nativeHeightScalarBoundaryCompanion :
    genuineComplexTimeLogJet = nativeHeightScalarBoundaryCompanion := by
  funext z
  unfold genuineComplexTimeLogJet nativeHeightScalarBoundaryCompanion
  rw [genuineComplexTimeBoundaryValue_eq_nativeHeightScalar]

/-- The public scalar Green Wronskian is exactly the Wronskian of the
undressed native height scalar. -/
theorem scalarGreenWronskian_genuine_eq_nativeHeight
    (z w : ℂ) :
    scalarGreenWronskian
        genuineComplexTimeBoundaryValue genuineComplexTimeLogJet z w =
      completedGreenWronskian
        nativeHeightScalar nativeHeightScalarBoundaryCompanion z w := by
  rw [genuineComplexTimeBoundaryValue_eq_nativeHeightScalar,
    genuineComplexTimeLogJet_eq_nativeHeightScalarBoundaryCompanion]
  rfl

/-- The completed `(F,-F')` Wronskian is the public Genuine Wronskian plus
the explicit xi-product transport correction.  The arguments are diagonal,
which is the only orientation used by the public confinement seam. -/
theorem completedFNegFPrimeWronskian_eq_publicGenuine_add_archimedeanTransport
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    completedGreenWronskian
        completedNativeOperatorCharacteristic
        (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u)
        (carryComplexTimeOfParameter s)
        (carryComplexTimeOfParameter s) =
      scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) +
        canonicalArchimedeanBoundaryGreenTransportCorrection
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) := by
  let z : ℂ := carryComplexTimeOfParameter s
  have hz : operatorHeightParameter z ∈ genuineCriticalStrip := by
    dsimp [z]
    simpa only [carryComplexTimeOfParameter_eq_centeredHeightParameter,
      operatorHeightParameter_centeredHeightParameter] using hs
  have hdressed :=
    canonicalCompletedC3ScalarGreenForm_eq_native_add_archimedeanTransportCorrection
      (z := z) (w := z) hz hz
  have hcompleted :
      greenForm (𝕜 := ℂ)
          (canonicalCompletedC3ScalarBoundaryPair z)
          (canonicalCompletedC3ScalarBoundaryPair z) =
        completedGreenWronskian
          completedNativeOperatorCharacteristic
          (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u)
          z z := by
    unfold canonicalCompletedC3ScalarBoundaryPair
    exact (completedGreenWronskian_eq_scalarGreenForm
      completedNativeOperatorCharacteristic
      (fun u : ℂ ↦ -deriv completedNativeOperatorCharacteristic u)
      z z).symm
  have hundressed :
      canonicalNativeUndressedGreenForm z z =
        scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet z z := by
    rw [canonicalNativeUndressedGreenForm_eq_nativeWronskian,
      ← scalarGreenWronskian_genuine_eq_nativeHeight]
  rw [hcompleted, hundressed] at hdressed
  simpa only [z] using hdressed

/-- Exact normalized form of the completed TFVD ledger at the public
carry-time point.  The left side is the public Genuine Wronskian after the
explicit xi-product transport.  The reflected Green term has the literal
TFVD physical cutoff `3 * 1`; all five retained completed channels remain
visible on the right. -/
theorem weightedPublicGenuineWronskian_add_transport_eq_tfvdGreenLedger
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight
        (carryComplexTimeOfParameter s)
        (carryComplexTimeOfParameter s) *
      (scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) +
        canonicalArchimedeanBoundaryGreenTransportCorrection
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)) =
      mixedHermitianWeight nativeXiCompletionFactor
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 3 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            3 (reflectedParameter s)) +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).greenProvenance +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).offDiagonal +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).readoutResidual +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).tailCompletion +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).archimedeanChart := by
  let z : ℂ := carryComplexTimeOfParameter s
  have hz : operatorHeightParameter z ∈ genuineCriticalStrip := by
    dsimp [z]
    simpa only [carryComplexTimeOfParameter_eq_centeredHeightParameter,
      operatorHeightParameter_centeredHeightParameter] using hs
  have hledger :=
    completedWronskian_factors_through_bracketTfvd_then_green
      1 (z := z) (w := z) hz hz
  rw [canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
    1 hz hz,
    completedFNegFPrimeWronskian_eq_publicGenuine_add_archimedeanTransport hs,
    canonicalC3BracketTfvdMixedGreenReadout_eq_bracketGreen] at hledger
  simpa only [z, carryComplexTimeOfParameter_eq_centeredHeightParameter,
    operatorHeightParameter_centeredHeightParameter, one_mul] using hledger

/-- The single public scalar-minus-one-block-Green residual.  This is the
actual unresolved equality required by `MinimalReflectedC3ConfinementSeam`;
it deliberately contains neither a diagonal Gram nor a reflected-to-diagonal
transport. -/
def minimalReflectedC3ScalarGreenResidual (s : ℂ) : ℂ :=
  scalarGreenWronskian
      genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
      (carryComplexTimeOfParameter s)
      (carryComplexTimeOfParameter s) -
    greenForm (𝕜 := ℂ)
      (finiteC3GenuineBracketGreenBoundaryPair 1 s)
      (finiteC3GenuineBracketGreenBoundaryPair
        1 (reflectedParameter s))

/-- After all existing scalar normalizations, the public one-block residual
has this exact weighted frontier.  The first parenthesis is the literal
cutoff/weight mismatch between the TFVD `3 * 1` Green port and the public
one-block port.  The remaining terms are the five retained completed
channels, with the xi-product transport correction made explicit.  No term
in this equality has been discarded. -/
theorem weighted_minimalReflectedC3ScalarGreenResidual_eq_tfvdFrontier
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    mixedHermitianWeight canonicalC3ChartFactorHeight
        (carryComplexTimeOfParameter s)
        (carryComplexTimeOfParameter s) *
      minimalReflectedC3ScalarGreenResidual s =
      (mixedHermitianWeight nativeXiCompletionFactor
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 3 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            3 (reflectedParameter s)) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s))) +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).greenProvenance +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).offDiagonal +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).readoutResidual +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).tailCompletion +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).archimedeanChart -
        mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        canonicalArchimedeanBoundaryGreenTransportCorrection
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) := by
  have hledger :=
    weightedPublicGenuineWronskian_add_transport_eq_tfvdGreenLedger hs
  unfold minimalReflectedC3ScalarGreenResidual
  calc
    mixedHermitianWeight canonicalC3ChartFactorHeight
        (carryComplexTimeOfParameter s)
        (carryComplexTimeOfParameter s) *
      (scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) -
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s))) =
      mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        (scalarGreenWronskian
            genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
            (carryComplexTimeOfParameter s)
            (carryComplexTimeOfParameter s) +
          canonicalArchimedeanBoundaryGreenTransportCorrection
            (carryComplexTimeOfParameter s)
            (carryComplexTimeOfParameter s)) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        canonicalArchimedeanBoundaryGreenTransportCorrection
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s)) := by ring
    _ =
      (mixedHermitianWeight nativeXiCompletionFactor
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 3 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            3 (reflectedParameter s)) +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).greenProvenance +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).offDiagonal +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).readoutResidual +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).tailCompletion +
        (canonicalCompletedC3FiniteFNegFPrimeMixedChannels 1
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s)).archimedeanChart) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        canonicalArchimedeanBoundaryGreenTransportCorrection
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) -
        mixedHermitianWeight canonicalC3ChartFactorHeight
          (carryComplexTimeOfParameter s)
          (carryComplexTimeOfParameter s) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair 1 s)
          (finiteC3GenuineBracketGreenBoundaryPair
            1 (reflectedParameter s)) := by rw [hledger]
    _ = _ := by ring

/-- The minimal reflected seam is precisely the vanishing of the one public
residual on off-critical strip parameters. -/
theorem minimalReflectedC3ConfinementSeam_iff_publicResidual_eq_zero :
    MinimalReflectedC3ConfinementSeam ↔
      ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
        s.re ≠ (1 : ℝ) / 2 →
          minimalReflectedC3ScalarGreenResidual s = 0 := by
  constructor
  · intro hseam s hs hoff
    unfold minimalReflectedC3ScalarGreenResidual
    rw [hseam hs hoff]
    ring
  · intro hres s hs hoff
    have h := hres hs hoff
    unfold minimalReflectedC3ScalarGreenResidual at h
    exact sub_eq_zero.mp h

end

end CarrySelfAdjointOperator

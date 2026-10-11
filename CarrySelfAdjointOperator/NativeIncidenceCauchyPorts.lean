import CarrySelfAdjointOperator.FirstEdgeChiralStateComparison
import CarrySelfAdjointOperator.ProjectiveValveNativeIncidence
import NativeCarrySpectralWeyl.Camera.FiniteCoefficientBridge
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace CarrySelfAdjointOperator.NativeCauchyPorts
open scoped BigOperators unitInterval ComplexConjugate InnerProductSpace
open CPFormal.Analytic.Cp MeasureTheory MaterialChiralCanary MaterialCameraJets FiniteClockJets FirstEdgeSewing
open Filter
open NativeCarrySpectralWeyl.Camera.FiniteBridge
noncomputable section
set_option autoImplicit false

/-- The geometric advance is multiplication by the actual interval coordinate. -/
def intervalCoordinate : C(unitInterval, ℂ) :=
  ⟨fun u => ((u : ℝ) : ℂ), by fun_prop⟩

def radialContinuousState (k j : ℕ) : C(unitInterval, ℂ) :=
  ((Real.sqrt ((k : ℝ)+1) : ℝ) : ℂ) • completedNativeChiralCauchyContinuousFeature j

/-- Continuous representatives map to the OLD Cauchy vectors without a new metric. -/
theorem radialContinuousState_toLp (k j : ℕ) :
    ContinuousMap.toLp 2 volume ℂ (radialContinuousState k j) =
      completedNativeRadialChiralCauchyState k j := by
  simp [radialContinuousState, completedNativeRadialChiralCauchyState,
    completedNativeChiralCauchyFeature]

theorem radialContinuousState_advance (k j : ℕ) :
    intervalCoordinate * radialContinuousState k j = radialContinuousState k (j+1) := by
  ext u
  simp [intervalCoordinate, radialContinuousState, completedNativeChiralCauchyContinuousFeature,
    pow_succ]
  ring

/-- Physical positive-position lift. Zero is excluded from this model and is
sent to zero explicitly; no claim of injectivity on the unrestricted ledger. -/
def nativeStencilCauchyProfile (k : ℕ) : FormalStencil →ₗ[ℤ] C(unitInterval, ℂ) :=
  Finsupp.linearCombination ℤ (fun n => if n = 0 then 0 else radialContinuousState k (n-1))

theorem nativeStencilCauchyProfile_atom (k j : ℕ) :
    nativeStencilCauchyProfile k (atom (j+1)) = radialContinuousState k j := by
  simp [nativeStencilCauchyProfile, atom]

/-- Original centered stencil, with lower endpoint p+1>0. -/
theorem nativeBracket_profile_factor (k p r : ℕ) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) =
      radialContinuousState k p * (1-intervalCoordinate^r)^2 := by
  have hl : p+r+1-r = p+1 := by omega
  rw [centeredBracketStencil, map_add, map_sub, map_nsmul, hl,
    nativeStencilCauchyProfile_atom, nativeStencilCauchyProfile_atom]
  have hr : p+r+1+r = (p+2*r)+1 := by omega
  rw [hr, nativeStencilCauchyProfile_atom]
  ext u
  simp [radialContinuousState, completedNativeChiralCauchyContinuousFeature,
    intervalCoordinate, pow_add, pow_mul]
  simp only [show (2 : C(unitInterval, ℂ)) u = (2 : ℂ) from rfl]
  ring

/-- The full finite camera is mapped before any readout; the OLD seed, all
centers and all radii remain in the same synthesis. -/
theorem nativeCamera_profile_seed_centers (k b M : ℕ) :
    nativeStencilCauchyProfile k (finiteStencil b M) =
      nativeStencilCauchyProfile k (seedStencil b) +
        ∑ i ∈ Finset.range M, nativeStencilCauchyProfile k (centerStencil b i) := by
  simp [finiteStencil]

/-- Literal endpoint value, after complete synthesis. -/
theorem nativeBracket_profile_value_one (k p r : ℕ) :
    nativeStencilCauchyProfile k (centeredBracketStencil (p+r+1) r) 1 = 0 := by
  rw [nativeBracket_profile_factor]
  simp [intervalCoordinate]

/-- The actual completed pair at a continuous representative, with exactly
one occurrence of the existing amplitude. -/
def completedContinuousPair (k j : ℕ) : C(unitInterval, ℂ) × C(unitInterval, ℂ) :=
  let A := completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j)
  let q := completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)
  A • (radialContinuousState k j, q • radialContinuousState k j)

/-- Both channels are advanced by the SAME interval multiplier. -/
def pairGeometricAdvance :
    (C(unitInterval, ℂ) × C(unitInterval, ℂ)) →ₗ[ℂ]
      (C(unitInterval, ℂ) × C(unitInterval, ℂ)) where
  toFun f := (intervalCoordinate*f.1, intervalCoordinate*f.2)
  map_add' f g := by ext u <;> simp [mul_add]
  map_smul' c f := by ext u <;> simp only [Prod.smul_fst, Prod.smul_snd, ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

/-- Existing analytic residual, now compared to the independently defined
geometric advance, not to a new radial clock. -/
theorem completedPair_advance_residual (k j : ℕ) :
    (ContinuousMap.toLp 2 volume ℂ
      ((completedContinuousPair k (j+1) - pairGeometricAdvance (completedContinuousPair k j)).1),
     ContinuousMap.toLp 2 volume ℂ
      ((completedContinuousPair k (j+1) - pairGeometricAdvance (completedContinuousPair k j)).2)) =
      radialChiralAnalyticResidual k j := by
  have hs : pairGeometricAdvance (completedContinuousPair k j) =
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k j) •
        (radialContinuousState k (j+1),
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j) •
            radialContinuousState k (j+1)) := by
    apply Prod.ext <;> ext u <;>
      simp [pairGeometricAdvance, completedContinuousPair, radialContinuousState,
        completedNativeChiralCauchyContinuousFeature, intervalCoordinate, pow_succ] <;> ring
  rw [hs]
  apply Prod.ext
  · simp [completedContinuousPair, radialContinuousState_toLp,
      radialAnalyticResidual_incident, sub_smul]
  · simp [completedContinuousPair, radialContinuousState_toLp,
      radialAnalyticResidual_returned, smul_smul]
    module

/-- Full-state radial recurrence. The residual is NOT assumed to be a
TFVD boundary return. -/
def continuousAdvanceResidual (k j : ℕ) : C(unitInterval, ℂ) × C(unitInterval, ℂ) :=
  completedContinuousPair k (j+1) - pairGeometricAdvance (completedContinuousPair k j)

theorem completedPair_geometric_telescope (k j : ℕ) :
    completedContinuousPair k j =
      (pairGeometricAdvance^j) (completedContinuousPair k 0) +
        ∑ m ∈ Finset.range j, (pairGeometricAdvance^(j-1-m)) (continuousAdvanceResidual k m) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Module.End.one_apply]
    rw [show completedContinuousPair k (j+1) =
      pairGeometricAdvance (completedContinuousPair k j) + continuousAdvanceResidual k j by
      simp [continuousAdvanceResidual]]
    rw [ih, map_add, map_sum]
    simp only [pow_succ', Module.End.mul_apply]
    rw [← add_assoc]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    have hmj : m < j := Finset.mem_range.mp hm
    rw [show j-m = (j-1-m)+1 by omega, pow_succ']
    rfl

/-- Independent first-port dictionary: frozen completed seed acting on the
geometric feature difference. It does not use U or the normalized radial jet. -/
def geometricFirstPortLift (k : ℕ) :
    (Fin 1 → ℂ) →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun a := a 0 • radialChiralEdgeChannels k 0 0
  map_add' a b := by simp [add_smul]
  map_smul' c a := by simp [smul_smul]

def geometricSupportedTfvdLift (k : ℕ) :
    (finiteSlopeCoefficientSynthesisLinearMap 1).range →ₗ[ℂ]
      CanonicalCompletedNativeProjectiveChiralCarrier :=
  (geometricFirstPortLift k).comp
    (LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
      (finiteSlopeCoefficientSynthesisLinearMap_injective 1)).symm.toLinearMap

/-- Seed plus actual (UNCLOCKED) physical gradient. -/
def geometricSeededPortPair (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  x 0 • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
    geometricFirstPortLift k (fun q => finiteMaterialGradient 1 x q)

/-- Exact independent-port versus true-source defect. Both original legs are
retained; gradient, inverse step and completion residual remain distinct. -/
theorem geometricSeededPort_source_defect (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k x - geometricSeededPortPair k x =
      ((canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1 - finiteMaterialGradient 1 x 0) •
        radialChiralEdgeChannels k 0 0 +
      ((canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1) • radialChiralAnalyticResidual k 0 := by
  rw [sourcePair_two_eq_seed_and_edge, projectiveFirstJet_eq_threeChannels]
  simp [geometricSeededPortPair, geometricFirstPortLift, radialChiralAnalyticResidual,
    Fin.sum_univ_three, finiteMaterialGradient, smul_smul, smul_add]
  module

/-- The full Green response and physical boundary return feed the independent
geometric port, on the exact finite TFVD range. -/
theorem geometricGreenBoundary_port_pair
    {b : ℕ} (hb : FiniteNativeCarryOperator.Camera.IsSupported b) (k : ℕ)
    (x : FiniteRealSpectralHilbert 2) :
    let a : Fin 1 → ℂ := fun q => finiteMaterialGradient 1 x q
    let state := finiteWeightedSlopeGreenResponseLinearMap (canonicalBR2CarryAmplitudeRatio b) 1 a +
      finiteWeightedSlopeBoundaryReturnLinearMap (canonicalBR2CarryAmplitudeRatio b)
        (canonicalBR2CarryAmplitudeRatio_pos hb).le (canonicalBR2CarryAmplitudeRatio_lt_one hb) 1 a
    ∃ h : state ∈ (finiteSlopeCoefficientSynthesisLinearMap 1).range,
      x 0 • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
        geometricSupportedTfvdLift k ⟨state,h⟩ = geometricSeededPortPair k x := by
  dsimp only
  let a : Fin 1 → ℂ := fun q => finiteMaterialGradient 1 x q
  have he := finiteWeightedSlopeGreenResponse_add_boundaryReturn
    (canonicalBR2CarryAmplitudeRatio b) (canonicalBR2CarryAmplitudeRatio_pos hb)
    (canonicalBR2CarryAmplitudeRatio_lt_one hb) 1 a
  refine ⟨?_, ?_⟩
  · rw [he]; exact ⟨a,rfl⟩
  · congr 1
    change geometricFirstPortLift k _ = geometricFirstPortLift k a
    congr 1
    apply (LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
      (finiteSlopeCoefficientSynthesisLinearMap_injective 1)).injective
    change (LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
      (finiteSlopeCoefficientSynthesisLinearMap_injective 1))
      ((LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
        (finiteSlopeCoefficientSynthesisLinearMap_injective 1)).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact he

/-- Minimal obstruction, even with seed retained: a constant material state
has zero gradient, but its second literal radial INPUT coordinate is nonzero.
Scope: this natural geometric first-port dictionary, not all enriched maps. -/
theorem geometricSeededPort_constant_no_go (k : ℕ)
    (hreg : ∀ i : Fin 2,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    let x : FiniteRealSpectralHilbert 2 := WithLp.toLp 2 (fun _ => (1 : ℂ))
    sourceCoordinatePair 1 k x ≠ geometricSeededPortPair k x := by
  dsimp only
  intro h
  have hg : geometricSeededPortPair k (WithLp.toLp 2 (fun _ => (1 : ℂ))) =
      sourceCoordinatePair 1 k (finiteMaterialBasis (0 : Fin 2)) := by
    rw [sourcePair_two_eq_seed_and_edge]
    simp [geometricSeededPortPair, geometricFirstPortLift, finiteMaterialGradient, finiteMaterialBasis]
  rw [hg] at h
  have he := sourceCoordinatePair_injective 1 k hreg h
  have hi := congrArg (fun v : FiniteRealSpectralHilbert 2 => v 1) he
  norm_num [finiteMaterialBasis] at hi


/-- The completed source seed is exactly the FIRST true-input basis column,
with the existing amplitude included once. -/
theorem sourcePair_first_basis {n : ℕ} (hn : 0<n) (k : ℕ) :
    sourceCoordinatePair n k (finiteMaterialBasis (⟨0,by omega⟩ : Fin (2*n))) =
      canonicalCompletedNativeRadialProjectiveChiralState k 0 := by
  have hchoose (i : Fin (2*n)) : Nat.choose 0 i.val =
      if i = (⟨0,by omega⟩ : Fin (2*n)) then 1 else 0 := by
    by_cases hi : i.val = 0
    · have he : i = (⟨0,by omega⟩ : Fin (2*n)) := Fin.ext hi
      simp [he]
    · have he : i ≠ (⟨0,by omega⟩ : Fin (2*n)) := by
        intro he
        exact hi (congrArg Fin.val he)
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp [he]
  unfold sourceCoordinatePair sourceCoordinateInput nativeSourceChiralJetInput
  simp [ChiralReturn.radialIncidentSynthesis, ChiralReturn.radialReturnedSynthesis,
    finiteMaterialBasis, nativeSourceChiralJetInputMatrix, nativeSourceJetOrderPhase,
    completedGreenForwardWeight, hchoose, canonicalCompletedNativeRadialProjectiveChiralState,
    canonicalCompletedNativeRadialChiralDefectState, completedNativeRadialChiralMultiplierState]

/-- Source-side obstruction valid in every nonempty even section (including
2,4,6): a material constant is NOT the single completed seed. No numerical
values or synthetic quotient are used. -/
theorem sourcePair_constant_ne_seed {n : ℕ} (hn : 0<n) (k : ℕ)
    (hreg : ∀ i : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    sourceCoordinatePair n k (WithLp.toLp 2 (fun _ => (1 : ℂ))) ≠
      canonicalCompletedNativeRadialProjectiveChiralState k 0 := by
  rw [← sourcePair_first_basis hn k]
  intro h
  have he := sourceCoordinatePair_injective n k hreg h
  have hi := congrArg (fun v : FiniteRealSpectralHilbert (2*n) => v ⟨1,by omega⟩) he
  norm_num [finiteMaterialBasis] at hi

theorem sourcePair_constant_eventually_ne_seed {n : ℕ} (hn : 0<n) :
    ∀ᶠ k : ℕ in Filter.atTop,
      sourceCoordinatePair n k (WithLp.toLp 2 (fun _ => (1 : ℂ))) ≠
        canonicalCompletedNativeRadialProjectiveChiralState k 0 := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)] with k hk
  exact sourcePair_constant_ne_seed hn k (fun i => ⟨(hk i).2.1,(hk i).2.2⟩)


/-- Two distinct defects: literal-gradient/radial-step mismatch and analytic
completion jumps. This formula is independent of the target pairing. -/
def geometricPortDefect (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  ((canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1 - finiteMaterialGradient 1 x 0) •
    radialChiralEdgeChannels k 0 0 +
  ((canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1) • radialChiralAnalyticResidual k 0

/-- Pairing only AFTER full-state reconstruction: base, both ordered crosses,
and defect-defect, with the original incident-minus-returned form. -/
theorem geometricPort_signed_defect_pairing (k : ℕ) (x y : FiniteRealSpectralHilbert 2) :
    canonicalCompletedNativeProjectiveChiralForm (sourceCoordinatePair 1 k x)
      (sourceCoordinatePair 1 k y) =
    canonicalCompletedNativeProjectiveChiralForm (geometricSeededPortPair k x)
      (geometricSeededPortPair k y) +
    canonicalCompletedNativeProjectiveChiralForm (geometricSeededPortPair k x)
      (geometricPortDefect k y) +
    canonicalCompletedNativeProjectiveChiralForm (geometricPortDefect k x)
      (geometricSeededPortPair k y) +
    canonicalCompletedNativeProjectiveChiralForm (geometricPortDefect k x)
      (geometricPortDefect k y) := by
  have hx : sourceCoordinatePair 1 k x = geometricSeededPortPair k x + geometricPortDefect k x := by
    have h := geometricSeededPort_source_defect k x
    change sourceCoordinatePair 1 k x - geometricSeededPortPair k x = geometricPortDefect k x at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hy : sourceCoordinatePair 1 k y = geometricSeededPortPair k y + geometricPortDefect k y := by
    have h := geometricSeededPort_source_defect k y
    change sourceCoordinatePair 1 k y - geometricSeededPortPair k y = geometricPortDefect k y at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  rw [hx,hy]
  simp only [canonicalCompletedNativeProjectiveChiralForm, Prod.fst_add, Prod.snd_add,
    inner_add_left, inner_add_right]
  ring

/-- First differing true input coordinate in the constant-state canary.
No amplitude is applied a second time in the incident synthesis. -/
theorem constantSeed_input_first_coordinate_defect (k : ℕ) :
    sourceCoordinateInput 1 k (WithLp.toLp 2 (fun _ => (1 : ℂ))) 0 -
      sourceCoordinateInput 1 k (finiteMaterialBasis (0 : Fin 2)) 0 =
      -completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ := by
  rw [sourceCoordinateInput_two_zero, sourceCoordinateInput_two_zero]
  simp [finiteMaterialBasis]
  ring

theorem constantSeed_input_first_coordinate_defect_ne_zero (k : ℕ)
    (hA : completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0) :
    sourceCoordinateInput 1 k (WithLp.toLp 2 (fun _ => (1 : ℂ))) 0 -
      sourceCoordinateInput 1 k (finiteMaterialBasis (0 : Fin 2)) 0 ≠ 0 := by
  rw [constantSeed_input_first_coordinate_defect]
  exact mul_ne_zero (neg_ne_zero.mpr hA) (inv_ne_zero (canonicalCompletedC3RadialSecondStep_ne_zero k))


/-- Existing continuous representatives map to the original Lp pair,
channel by channel; this adapter changes no metric or completion data. -/
def continuousPairToSource : (C(unitInterval, ℂ) × C(unitInterval, ℂ)) →ₗ[ℂ]
    CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun f := (ContinuousMap.toLp 2 volume ℂ f.1, ContinuousMap.toLp 2 volume ℂ f.2)
  map_add' f g := by simp
  map_smul' c f := by simp

theorem completedContinuousPair_toSource (k j : ℕ) :
    continuousPairToSource (completedContinuousPair k j) =
      canonicalCompletedNativeRadialProjectiveChiralState k j := by
  simp [continuousPairToSource, completedContinuousPair, radialContinuousState_toLp,
    canonicalCompletedNativeRadialProjectiveChiralState,
    canonicalCompletedNativeRadialChiralDefectState, completedNativeRadialChiralMultiplierState]

/-- Geometric telescoping in the ORIGINAL two-leg Lp carrier. Advance is
multiplication on the independently specified continuous representatives;
no global radial log operator is fabricated. -/
theorem completedSource_geometric_telescope (k j : ℕ) :
    canonicalCompletedNativeRadialProjectiveChiralState k j =
      continuousPairToSource ((pairGeometricAdvance^j) (completedContinuousPair k 0)) +
      ∑ m ∈ Finset.range j,
        continuousPairToSource ((pairGeometricAdvance^(j-1-m)) (continuousAdvanceResidual k m)) := by
  rw [← completedContinuousPair_toSource, completedPair_geometric_telescope, map_add, map_sum]


/-- The independent port dictionary is EXACTLY the geometrically advanced
completed seed minus that seed, in the old two-leg carrier. This proves its
provenance without defining it from U or from a normalized difference jet. -/
theorem geometricFirstPort_channel_provenance (k : ℕ) :
    continuousPairToSource
      (pairGeometricAdvance (completedContinuousPair k 0) - completedContinuousPair k 0) =
      radialChiralEdgeChannels k 0 0 := by
  have hr := completedPair_advance_residual k 0
  change continuousPairToSource
    (completedContinuousPair k 1 - pairGeometricAdvance (completedContinuousPair k 0)) =
      radialChiralAnalyticResidual k 0 at hr
  rw [map_sub, completedContinuousPair_toSource] at hr
  have he : canonicalCompletedNativeRadialProjectiveChiralState k 1 -
      canonicalCompletedNativeRadialProjectiveChiralState k 0 =
      radialChiralEdgeChannels k 0 0 + radialChiralAnalyticResidual k 0 := by
    simpa [Fin.sum_univ_three, radialChiralAnalyticResidual, add_assoc] using
      radialProjectiveEdge_eq_threeChannels k 0
  rw [map_sub, completedContinuousPair_toSource]
  calc
    _ = (canonicalCompletedNativeRadialProjectiveChiralState k 1 -
          canonicalCompletedNativeRadialProjectiveChiralState k 0) -
        (canonicalCompletedNativeRadialProjectiveChiralState k 1 -
          continuousPairToSource (pairGeometricAdvance (completedContinuousPair k 0))) := by abel
    _ = (radialChiralEdgeChannels k 0 0 + radialChiralAnalyticResidual k 0) -
        radialChiralAnalyticResidual k 0 := by rw [he,hr]
    _ = _ := by abel

end
end CarrySelfAdjointOperator.NativeCauchyPorts

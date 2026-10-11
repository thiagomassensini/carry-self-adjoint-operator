import CarrySelfAdjointOperator.ChiralLogGapDefectTransport

namespace CarrySelfAdjointOperator.FirstEdgeSewing
open CPFormal.Analytic.Cp FiniteClockJets MaterialCameraJets MaterialChiralCanary
open LogGapConnection ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Three independently sourced terms of the radial product rule:
frozen graph difference, completion amplitude jump, chiral quotient jump.
All terms live in the original TWO-leg carrier. -/
def radialChiralEdgeChannels (k i : ℕ) :
    Fin 3 → CanonicalCompletedNativeProjectiveChiralCarrier :=
  let A0 := completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i)
  let A1 := completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1))
  let q0 := completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i)
  let q1 := completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1))
  let C0 := completedNativeRadialChiralCauchyState k i
  let C1 := completedNativeRadialChiralCauchyState k (i+1)
  ![A0 • (C1-C0, q0 • (C1-C0)),
    (A1-A0) • (C1, q0 • C1),
    (0, (A1*(q1-q0)) • C1)]

/-- Literal analytic correction; neither channel is defined by subtraction
from a desired positive object. -/
def radialChiralAnalyticResidual (k i : ℕ) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  radialChiralEdgeChannels k i 1 + radialChiralEdgeChannels k i 2

/-- Full-state discrete Leibniz identity, for every adjacent radial edge. -/
theorem radialProjectiveEdge_eq_threeChannels (k i : ℕ) :
    canonicalCompletedNativeRadialProjectiveChiralState k (i+1) -
      canonicalCompletedNativeRadialProjectiveChiralState k i =
        ∑ j : Fin 3, radialChiralEdgeChannels k i j := by
  apply Prod.ext <;>
    simp [radialChiralEdgeChannels, canonicalCompletedNativeRadialProjectiveChiralState,
      canonicalCompletedNativeRadialChiralDefectState, completedNativeRadialChiralMultiplierState,
      Fin.sum_univ_three, smul_smul] <;> module

theorem radialAnalyticResidual_incident (k i : ℕ) :
    (radialChiralAnalyticResidual k i).1 =
      (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) -
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i)) •
        completedNativeRadialChiralCauchyState k (i+1) := by
  simp [radialChiralAnalyticResidual, radialChiralEdgeChannels]

theorem radialAnalyticResidual_returned (k i : ℕ) :
    (radialChiralAnalyticResidual k i).2 =
      ((completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) -
          completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i)) *
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i) +
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) *
          (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1)) -
            completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i))) •
        completedNativeRadialChiralCauchyState k (i+1) := by
  simp [radialChiralAnalyticResidual, radialChiralEdgeChannels, smul_smul]
  module

private theorem radialCauchy_ne_zero (k i : ℕ) :
    completedNativeRadialChiralCauchyState k i ≠ 0 := by
  intro h
  have hi := inner_completedNativeRadialChiralCauchyState k i i
  rw [h, inner_zero_left] at hi
  have hp : (0 : ℝ) < ((k : ℝ)+1) * (((i+i+2 : ℕ) : ℝ)⁻¹) := by positivity
  have hn : ((((k : ℝ)+1) * (((i+i+2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne'
  exact hn hi.symm

/-- Vanishing of the complete residual forces the amplitude jump to vanish,
and separately forces the quotient jump weighted by the actual amplitude. -/
theorem radialAnalyticResidual_zero_iff (k i : ℕ) :
    radialChiralAnalyticResidual k i = 0 ↔
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) =
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i) ∧
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) *
        (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1)) -
          completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i)) = 0 := by
  constructor
  · intro h
    have hf := congrArg Prod.fst h
    rw [radialAnalyticResidual_incident] at hf
    have ha := sub_eq_zero.mp ((smul_eq_zero.mp hf).resolve_right (radialCauchy_ne_zero k (i+1)))
    refine ⟨ha, ?_⟩
    have hs := congrArg Prod.snd h
    rw [radialAnalyticResidual_returned, sub_eq_zero.mpr ha, zero_mul, zero_add] at hs
    exact (smul_eq_zero.mp hs).resolve_right (radialCauchy_ne_zero k (i+1))
  · rintro ⟨ha, hq⟩
    apply Prod.ext
    · rw [radialAnalyticResidual_incident, ha, sub_self, zero_smul]
      rfl
    · rw [radialAnalyticResidual_returned, sub_eq_zero.mpr ha, zero_mul, zero_add, hq, zero_smul]
      rfl

theorem radialAnalyticResidual_zero_iff_regular (k i : ℕ)
    (hA : completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k (i+1)) ≠ 0) :
    radialChiralAnalyticResidual k i = 0 ↔
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k (i+1)) =
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k i) ∧
      completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k (i+1)) =
        completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k i) := by
  rw [radialAnalyticResidual_zero_iff]
  simp only [mul_eq_zero, hA, false_or, sub_eq_zero]

/-- The first radial jet includes all three channels with its OLD step. -/
theorem projectiveFirstJet_eq_threeChannels (k : ℕ) :
    projectiveChiralDifferenceJet k 1 =
      (canonicalCompletedC3RadialSecondStep k)⁻¹ •
        ∑ j : Fin 3, radialChiralEdgeChannels k 0 j := by
  rw [projectiveChiralDifferenceJet_one, radialProjectiveEdge_eq_threeChannels]

/-- The complete dimension-two source before applying the clock retains seed. -/
theorem sourcePair_two_eq_seed_and_edge (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k x =
      x 0 • canonicalCompletedNativeRadialProjectiveChiralState k 0 +
        (x 0 + finiteMaterialGradient 1 x 0) • projectiveChiralDifferenceJet k 1 := by
  rw [sourceCoordinatePair_eq_existingSynthesis]
  change (∑ i : Fin 1 ⊕ Fin 1,
    Sum.elim (nativeSourceEvenBoundaryPhase 1 (fun a => x a))
      (nativeSourceOddBoundaryPhase 1 (fun a => x a)) i •
    projectiveChiralDifferenceJet k (Sum.elim (fun j : Fin 1 => 2*j.val)
      (fun j : Fin 1 => 2*j.val+1) i)) = _
  simp [Fintype.sum_sum_type, nativeSourceEvenBoundaryPhase, nativeSourceOddBoundaryPhase,
    nativeSourceEvenBoundaryIndex, nativeSourceOddBoundaryIndex, projectiveChiralDifferenceJet_zero,
    finiteMaterialGradient]

/-- Dictionary fixed independently by the existing FIRST radial jet.
It is only a one-edge coefficient lift, not an all-cutoff physical sewing. -/
def firstEdgeCoefficientLift (k : ℕ) :
    (Fin 1 → ℂ) →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun a := a 0 • projectiveChiralDifferenceJet k 1
  map_add' a b := by simp [add_smul]
  map_smul' c a := by simp [smul_smul]

/-- A whole-state factorization through the actual clocked physical edge.
The clocked gradient includes the original seed contribution. -/
theorem sourcePair_clock_eq_firstPhysicalEdgeLift (k : ℕ)
    (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k (materialJet 1 x) =
      firstEdgeCoefficientLift k (fun q => finiteMaterialGradient 1 (materialJet 1 x) q) := by
  rw [sourcePair_two_eq_seed_and_edge]
  have h0 : materialJet 1 x (0 : Fin 2) = 0 := by
    simp [materialJet_apply, finiteRealSpectralFrequency]
  rw [h0, zero_smul, zero_add, zero_add]
  rfl

/-- The same scalar log gap multiplies a THREE-channel completed vector. -/
theorem sourcePair_clock_eq_threeChannels (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinatePair 1 k (materialJet 1 x) =
      ((positiveLogGap 0 * (x 0 + finiteMaterialGradient 1 x 0)) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹) •
        ∑ j : Fin 3, radialChiralEdgeChannels k 0 j := by
  rw [sourcePair_clock_eq_firstPhysicalEdgeLift]
  change finiteMaterialGradient 1 (materialJet 1 x) 0 • projectiveChiralDifferenceJet k 1 = _
  rw [materialGradient_jet_productRule, projectiveFirstJet_eq_threeChannels]
  simp [logEdgePowerWeight, positiveLogVertexWeight, finiteMaterialGradient, smul_smul]

private theorem form_sum {ι : Type*} [Fintype ι]
    (u v : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
    canonicalCompletedNativeProjectiveChiralForm (∑ i, u i) (∑ j, v j) =
      ∑ i, ∑ j, canonicalCompletedNativeProjectiveChiralForm (u i) (v j) := by
  have hf (f : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
      (∑ i, f i).1 = ∑ i, (f i).1 :=
    map_sum (AddMonoidHom.fst _ _) f Finset.univ
  have hs (f : ι → CanonicalCompletedNativeProjectiveChiralCarrier) :
      (∑ i, f i).2 = ∑ i, (f i).2 :=
    map_sum (AddMonoidHom.snd _ _) f Finset.univ
  simp only [canonicalCompletedNativeProjectiveChiralForm, hf, hs, sum_inner, inner_sum]
  rw [Finset.sum_comm (f := fun j i => inner ℂ (u i).1 (v j).1),
    Finset.sum_comm (f := fun j i => inner ℂ (u i).2 (v j).2)]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

/-- Two independent material inputs, all nine signed sectors retained. -/
theorem sourcePair_firstEdge_signed_nine_sectors (k : ℕ)
    (x y : FiniteRealSpectralHilbert 2) :
    let ax := (positiveLogGap 0 * (x 0 + finiteMaterialGradient 1 x 0)) *
      (canonicalCompletedC3RadialSecondStep k)⁻¹
    let ay := (positiveLogGap 0 * (y 0 + finiteMaterialGradient 1 y 0)) *
      (canonicalCompletedC3RadialSecondStep k)⁻¹
    canonicalCompletedNativeProjectiveChiralForm
      (sourceCoordinatePair 1 k (materialJet 1 x))
      (sourceCoordinatePair 1 k (materialJet 1 y)) =
      ∑ j : Fin 3, ∑ l : Fin 3, conj ax * ay *
        canonicalCompletedNativeProjectiveChiralForm
          (radialChiralEdgeChannels k 0 j) (radialChiralEdgeChannels k 0 l) := by
  dsimp only
  rw [sourcePair_clock_eq_threeChannels, sourcePair_clock_eq_threeChannels,
    projectiveChiralForm_smul]
  rw [form_sum]
  simp only [Finset.mul_sum]

/-- Recover the coefficient ONLY on the actual one-edge finite TFVD image.
This is a linear lift of that supported prefix; no projection of an arbitrary
infinite TFVD state, no new metric, and no cutoff-uniform bound is asserted. -/
def firstEdgeSupportedTfvdLift (k : ℕ) :
    (finiteSlopeCoefficientSynthesisLinearMap 1).range →ₗ[ℂ]
      CanonicalCompletedNativeProjectiveChiralCarrier :=
  (firstEdgeCoefficientLift k).comp
    (LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
      (finiteSlopeCoefficientSynthesisLinearMap_injective 1)).symm.toLinearMap

theorem firstEdgeSupportedTfvdLift_on_synthesis (k : ℕ) (a : Fin 1 → ℂ) :
    firstEdgeSupportedTfvdLift k
      ((LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
        (finiteSlopeCoefficientSynthesisLinearMap_injective 1)) a) =
      firstEdgeCoefficientLift k a := by
  simp [firstEdgeSupportedTfvdLift]

/-- Complete Green response + boundary return is lifted BEFORE any coefficient
readout. Both are independently defined; the original two source legs result.
Scope: one clocked material edge and the existing radial jet dictionary. -/
theorem firstEdgeGreenBoundary_source_state_sewing
    {b : ℕ} (hb : FiniteNativeCarryOperator.Camera.IsSupported b) (k : ℕ)
    (x : FiniteRealSpectralHilbert 2) :
    let a : Fin 1 → ℂ := fun q => finiteMaterialGradient 1 (materialJet 1 x) q
    let state :=
      finiteWeightedSlopeGreenResponseLinearMap (canonicalBR2CarryAmplitudeRatio b) 1 a +
        finiteWeightedSlopeBoundaryReturnLinearMap (canonicalBR2CarryAmplitudeRatio b)
          (canonicalBR2CarryAmplitudeRatio_pos hb).le (canonicalBR2CarryAmplitudeRatio_lt_one hb) 1 a
    ∃ h : state ∈ (finiteSlopeCoefficientSynthesisLinearMap 1).range,
      firstEdgeSupportedTfvdLift k ⟨state, h⟩ =
        sourceCoordinatePair 1 k (materialJet 1 x) := by
  dsimp only
  let a : Fin 1 → ℂ := fun q => finiteMaterialGradient 1 (materialJet 1 x) q
  let state :=
    finiteWeightedSlopeGreenResponseLinearMap (canonicalBR2CarryAmplitudeRatio b) 1 a +
      finiteWeightedSlopeBoundaryReturnLinearMap (canonicalBR2CarryAmplitudeRatio b)
        (canonicalBR2CarryAmplitudeRatio_pos hb).le (canonicalBR2CarryAmplitudeRatio_lt_one hb) 1 a
  have he : state = finiteSlopeCoefficientSynthesisLinearMap 1 a :=
    finiteWeightedSlopeGreenResponse_add_boundaryReturn
      (canonicalBR2CarryAmplitudeRatio b) (canonicalBR2CarryAmplitudeRatio_pos hb)
      (canonicalBR2CarryAmplitudeRatio_lt_one hb) 1 a
  have hm : state ∈ (finiteSlopeCoefficientSynthesisLinearMap 1).range := by
    rw [he]
    exact ⟨a, rfl⟩
  refine ⟨hm, ?_⟩
  have hsub :
      (⟨state, hm⟩ : (finiteSlopeCoefficientSynthesisLinearMap 1).range) =
        (LinearEquiv.ofInjective (finiteSlopeCoefficientSynthesisLinearMap 1)
          (finiteSlopeCoefficientSynthesisLinearMap_injective 1)) a := by
    apply Subtype.ext
    exact he
  rw [hsub, firstEdgeSupportedTfvdLift_on_synthesis]
  exact (sourcePair_clock_eq_firstPhysicalEdgeLift k x).symm

/-- The literal completed endpoint features are not an orthonormal material
pair. This rejects only an isometry sending those individual basis nodes to
those exact incident states; it does not reject a nonunitary enriched sewing. -/
theorem no_isometric_firstNode_identification (k : ℕ)
    (hA0 : completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hA1 : completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 1) ≠ 0) :
    ¬ ∃ T : FiniteRealSpectralHilbert 2 →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ x y, inner ℂ (T x) (T y) = inner ℂ x y) ∧
      T (finiteMaterialBasis (0 : Fin 2)) = (canonicalCompletedNativeRadialProjectiveChiralState k 0).1 ∧
      T (finiteMaterialBasis (1 : Fin 2)) = (canonicalCompletedNativeRadialProjectiveChiralState k 1).1 := by
  rintro ⟨T, hT, h0, h1⟩
  have hi := hT (finiteMaterialBasis (0 : Fin 2)) (finiteMaterialBasis (1 : Fin 2))
  rw [h0, h1] at hi
  have hm : inner ℂ (finiteMaterialBasis (0 : Fin 2)) (finiteMaterialBasis (1 : Fin 2)) = 0 := by
    simp [PiLp.inner_apply, finiteMaterialBasis, RCLike.inner_apply]
  have hs : inner ℂ (canonicalCompletedNativeRadialProjectiveChiralState k 0).1
      (canonicalCompletedNativeRadialProjectiveChiralState k 1).1 =
      conj (completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0)) *
        completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 1) *
        ((((k : ℝ)+1)*(3 : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [canonicalCompletedNativeRadialProjectiveChiralState,
      canonicalCompletedNativeRadialChiralDefectState, Prod.smul_fst]
    rw [inner_smul_left, inner_smul_right, inner_completedNativeRadialChiralCauchyState]
    norm_num only [Nat.reduceAdd]
    ring
  rw [hs, hm] at hi
  have hc : conj (completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k 0)) ≠ 0 := by
    intro hz
    apply hA0
    have hz' := congrArg conj hz
    simpa using hz'
  have hn : ((((k : ℝ)+1)*(3 : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < ((k : ℝ)+1)*(3 : ℝ)⁻¹ by positivity))
  exact (mul_ne_zero (mul_ne_zero hc hA1) hn) hi

end
end CarrySelfAdjointOperator.FirstEdgeSewing

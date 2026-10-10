import CarrySelfAdjointOperator.RelationalMaterialClockAllOrder
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport

/-! A canary for identifying material positions with radial jet orders.
The candidate uses the existing source chart and both original legs.
It is not a proved physical material-to-completed-source sewing. -/
namespace CarrySelfAdjointOperator.MaterialChiralCanary
open CPFormal.Analytic.Cp FiniteClockJets MaterialCameraJets ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Literal coordinate reuse of the existing source input matrix, in the
existing finite material Hilbert. Position and jet-order indices are not identified
by geometry merely because these two finite types have the same cardinality. -/
def sourceCoordinateInput (n k : ℕ) (x : FiniteRealSpectralHilbert (2*n)) :
    FiniteRealSpectralHilbert (2*n) :=
  WithLp.toLp 2 (nativeSourceChiralJetInput n k (fun a => x a))

/-- Both source legs, with the same geometrically fixed U. -/
def sourceCoordinatePair (n k : ℕ) (x : FiniteRealSpectralHilbert (2*n)) :
    CanonicalCompletedNativeProjectiveChiralCarrier :=
  (radialIncidentSynthesis k (2*n) (fun a => sourceCoordinateInput n k x a),
   radialReturnedSynthesis k (2*n) (fun a => sourceCoordinateInput n k x a))

theorem sourceCoordinatePair_eq_existingSynthesis (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinatePair n k x =
      nativeSourceProjectiveBoundaryJetSynthesis n k (fun a => x a) := by
  exact (nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource n k _).symm

/-- Finite whole-source injectivity is independent of any sign assertion. -/
theorem sourceCoordinatePair_injective (n k : ℕ)
    (hreg : ∀ i : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    Function.Injective (sourceCoordinatePair n k) := by
  intro x y h
  have hi := congrArg Prod.fst h
  have hu := radialIncidentSynthesis_injective k (2*n) hi
  have hx := nativeSourceChiralJetInput_injective n k hreg hu
  ext i
  exact congrFun hx i

private theorem source_sum_inner {N : ℕ} (c d : Fin N → ℂ)
    (u v : Fin N → CanonicalCompletedNativeChiralCauchyCarrier) :
    inner ℂ (∑ i, c i • u i) (∑ j, d j • v j) =
      ∑ i, ∑ j, conj (c i) * d j * inner ℂ (u i) (v j) := by
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A slope-only map cannot recover even this complete finite source pair.
The seed loss is an obstruction before any energy or limiting comparison. -/
theorem sourceCoordinatePair_two_not_factor_through_gradient (k : ℕ)
    (hreg : ∀ i : Fin 2,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    ¬ ∃ T : FiniteRealSpectralHilbert 1 → CanonicalCompletedNativeProjectiveChiralCarrier,
      ∀ x : FiniteRealSpectralHilbert 2,
        sourceCoordinatePair 1 k x = T (finiteMaterialGradient 1 x) := by
  rintro ⟨T, hT⟩
  apply finiteMaterialGradient_not_injective 1
  intro x y hxy
  apply sourceCoordinatePair_injective 1 k hreg
  rw [hT x, hT y, hxy]

theorem sourceCoordinatePair_two_eventually_not_factor_through_gradient :
    ∀ᶠ k : ℕ in atTop,
      ¬ ∃ T : FiniteRealSpectralHilbert 1 → CanonicalCompletedNativeProjectiveChiralCarrier,
        ∀ x : FiniteRealSpectralHilbert 2,
          sourceCoordinatePair 1 k x = T (finiteMaterialGradient 1 x) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2] with k hk
  exact sourceCoordinatePair_two_not_factor_through_gradient k
    (fun i => ⟨(hk i).2.1, (hk i).2.2⟩)

/-- All ordered crosses, without deleting either chirality. -/
theorem sourceCoordinatePair_signed_pairing (n k : ℕ)
    (x y : FiniteRealSpectralHilbert (2*n)) :
    canonicalCompletedNativeProjectiveChiralForm
      (sourceCoordinatePair n k x) (sourceCoordinatePair n k y) =
      (2 : ℂ)⁻¹ *
        (∑ i, ∑ j, conj (sourceCoordinateInput n k x i) *
          sourceCoordinateInput n k y j * inner ℂ
            (completedNativeRadialChiralCauchyState k i)
            (completedNativeRadialChiralCauchyState k j) -
         ∑ i, ∑ j, conj (sourceCoordinateInput n k x i) *
          sourceCoordinateInput n k y j * inner ℂ
            (completedNativeRadialChiralMultiplierState k i)
            (completedNativeRadialChiralMultiplierState k j)) := by
  simp only [sourceCoordinatePair, canonicalCompletedNativeProjectiveChiralForm,
    radialIncidentSynthesis, radialReturnedSynthesis, LinearMap.coe_mk, AddHom.coe_mk]
  rw [source_sum_inner, source_sum_inner]

/-- The original signed energy and storage, with their forced factor two. -/
theorem sourceCoordinatePair_energy_eq_storage (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    2 * (‖(sourceCoordinatePair n k x).1‖^2 - ‖(sourceCoordinatePair n k x).2‖^2) =
      2 * (storage k (nativeSourceChiralJetInput n k (fun a => x a)) 1).re := by
  rw [sourceCoordinatePair_eq_existingSynthesis]
  exact nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage n k _

/-- Exact all-order commutator of the direct coordinate-reuse candidate.
Both clocks here are the same existing material clock. This checks that
relabeling U does not by itself make it a material clock intertwiner. -/
theorem sourceCoordinateInput_materialJet_commutator (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) (i : Fin (2*n)) :
    sourceCoordinateInput n k (materialJet r x) i -
      materialJet r (sourceCoordinateInput n k x) i =
      ∑ a, nativeSourceChiralJetInputMatrix n k i a *
        ((finiteRealSpectralFrequency a : ℂ)^r -
          (finiteRealSpectralFrequency i : ℂ)^r) * x a := by
  change (∑ a, nativeSourceChiralJetInputMatrix n k i a * materialJet r x a) -
    materialJet r (sourceCoordinateInput n k x) i = _
  rw [materialJet_apply]
  change (∑ a, nativeSourceChiralJetInputMatrix n k i a * materialJet r x a) -
    (finiteRealSpectralFrequency i : ℂ)^r *
      (∑ a, nativeSourceChiralJetInputMatrix n k i a * x a) = _
  simp only [materialJet_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem sourceCoordinateInput_order_zero (n k : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinateInput n k (materialJet 0 x) =
      materialJet 0 (sourceCoordinateInput n k x) := by
  simp [materialJet]

/-- Order-zero radial state: the first shifted radial node, not the origin. -/
theorem projectiveChiralDifferenceJet_zero (k : ℕ) :
    projectiveChiralDifferenceJet k 0 =
      canonicalCompletedNativeRadialProjectiveChiralState k 0 := by
  simp [projectiveChiralDifferenceJet, completedGreenForwardWeight]

/-- Order one keeps both independently defined radial nodes. -/
theorem projectiveChiralDifferenceJet_one (k : ℕ) :
    projectiveChiralDifferenceJet k 1 =
      (canonicalCompletedC3RadialSecondStep k)⁻¹ •
        (canonicalCompletedNativeRadialProjectiveChiralState k 1 -
          canonicalCompletedNativeRadialProjectiveChiralState k 0) := by
  simp [projectiveChiralDifferenceJet, completedGreenForwardWeight, Finset.sum_range_succ,
    sub_eq_add_neg, add_comm]

/-- The two-coordinate source matrix retains completion amplitudes A0,A1. -/
theorem sourceCoordinateInput_two_zero (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinateInput 1 k x 0 =
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (x 0 - (canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1) := by
  simp [sourceCoordinateInput, nativeSourceChiralJetInput, nativeSourceChiralJetInputMatrix,
    nativeSourceJetOrderPhase, completedGreenForwardWeight, Fin.sum_univ_two]
  ring

theorem sourceCoordinateInput_two_one (k : ℕ) (x : FiniteRealSpectralHilbert 2) :
    sourceCoordinateInput 1 k x 1 =
      completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 1) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ * x 1 := by
  simp [sourceCoordinateInput, nativeSourceChiralJetInput, nativeSourceChiralJetInputMatrix,
    nativeSourceJetOrderPhase, completedGreenForwardWeight, Fin.sum_univ_two]

/-- The literal order-one defect is already nonzero on the second basis vector. -/
theorem sourceCoordinateInput_two_clock_defect (k : ℕ) :
    sourceCoordinateInput 1 k (materialJet 1 (finiteMaterialBasis (1 : Fin 2))) 0 -
      materialJet 1 (sourceCoordinateInput 1 k (finiteMaterialBasis (1 : Fin 2))) 0 =
      -completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k 0) *
        (canonicalCompletedC3RadialSecondStep k)⁻¹ * (Real.log 2 : ℂ) := by
  rw [sourceCoordinateInput_two_zero, materialJet_apply]
  simp [materialJet_apply, finiteMaterialBasis, finiteRealSpectralFrequency]
  ring

/-- No-go for the direct identification of material position and radial jet order,
in the regular two-coordinate chart. This is NOT a universal no-go for sewing. -/
theorem sourceCoordinateInput_two_not_clock_intertwiner (k : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0)
    (hHB : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k 0) ≠ 0) :
    ¬ ∀ x : FiniteRealSpectralHilbert 2,
      sourceCoordinateInput 1 k (materialJet 1 x) =
        materialJet 1 (sourceCoordinateInput 1 k x) := by
  intro h
  have hz := congrArg (fun v : FiniteRealSpectralHilbert 2 => v 0)
    (h (finiteMaterialBasis (1 : Fin 2)))
  have hd := sourceCoordinateInput_two_clock_defect k
  rw [hz, sub_self] at hd
  have ha := completedNativeNormalizedPositiveChiralAmplitude_ne_zero hF hHB
  have hs := canonicalCompletedC3RadialSecondStep_ne_zero k
  have hl : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ha) (inv_ne_zero hs)) hl) hd.symm

theorem sourceCoordinateInput_two_eventually_not_clock_intertwiner :
    ∀ᶠ k : ℕ in atTop, ¬ ∀ x : FiniteRealSpectralHilbert 2,
      sourceCoordinateInput 1 k (materialJet 1 x) =
        materialJet 1 (sourceCoordinateInput 1 k x) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 2] with k hk
  exact sourceCoordinateInput_two_not_clock_intertwiner k (hk 0).2.1 (hk 0).2.2

end
end CarrySelfAdjointOperator.MaterialChiralCanary

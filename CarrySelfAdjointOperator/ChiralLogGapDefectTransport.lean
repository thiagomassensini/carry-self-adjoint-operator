import CarrySelfAdjointOperator.SeededMaterialLogConnection

namespace CarrySelfAdjointOperator.LogGapConnection
open CPFormal.Analytic.Cp FiniteClockJets MaterialCameraJets MaterialChiralCanary ChiralReturn
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- The original incident/returned synthesis on radial coefficients, both legs.
No identification of these coefficients with physical positions is asserted. -/
def sourceRadialPair (n k : ℕ) :
    FiniteRealSpectralHilbert (2*n) →ₗ[ℂ] CanonicalCompletedNativeProjectiveChiralCarrier where
  toFun x := (radialIncidentSynthesis k (2*n) (fun i => x i),
    radialReturnedSynthesis k (2*n) (fun i => x i))
  map_add' x y := by
    apply Prod.ext <;>
      simp [radialIncidentSynthesis, radialReturnedSynthesis, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    apply Prod.ext <;>
      simp [radialIncidentSynthesis, radialReturnedSynthesis, Finset.smul_sum, smul_smul]

/-- The complete vector commutator, before any source synthesis or readout. -/
def sourceCoordinateJetDefect (n k r : ℕ) (x : FiniteRealSpectralHilbert (2*n)) :
    FiniteRealSpectralHilbert (2*n) :=
  sourceCoordinateInput n k (materialJet r x) - materialJet r (sourceCoordinateInput n k x)

/-- One retained vector edge contribution in the same source-coordinate carrier. -/
def sourceEdgeState (n k : ℕ) (x : FiniteRealSpectralHilbert (2*n)) (q : Fin (2*n)) :
    FiniteRealSpectralHilbert (2*n) :=
  WithLp.toLp 2 (fun i => sourceEdgeContribution n k x q i)

theorem sourceCoordinateJetDefect_eq_edgeSynthesis (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinateJetDefect n k r x =
      ∑ q : Fin (2*n), logEdgePowerWeight q.val r • sourceEdgeState n k x q := by
  ext i
  change sourceCoordinateInput n k (materialJet r x) i -
    materialJet r (sourceCoordinateInput n k x) i = _
  rw [sourceCoordinateInput_commutator_edgeFlux]
  simp [sourceEdgeState]

/-- The defect is transported through BOTH original source legs, edge by edge. -/
theorem sourceRadialPair_defect_eq_edgeSynthesis (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceRadialPair n k (sourceCoordinateJetDefect n k r x) =
      ∑ q : Fin (2*n), logEdgePowerWeight q.val r •
        sourceRadialPair n k (sourceEdgeState n k x q) := by
  rw [sourceCoordinateJetDefect_eq_edgeSynthesis, map_sum]
  simp only [map_smul]

/-- Whole-state identity with correction: the commutator is not set to zero. -/
theorem sourceCoordinatePair_jet_eq_base_add_defect (n k r : ℕ)
    (x : FiniteRealSpectralHilbert (2*n)) :
    sourceCoordinatePair n k (materialJet r x) =
      sourceRadialPair n k (materialJet r (sourceCoordinateInput n k x)) +
        sourceRadialPair n k (sourceCoordinateJetDefect n k r x) := by
  change sourceRadialPair n k (sourceCoordinateInput n k (materialJet r x)) = _
  rw [← map_add]
  congr 1
  unfold sourceCoordinateJetDefect
  abel

/-- Two independent inputs and orders, with all signed base/defect crosses.
The form is the original one; this does not compare it to a positive Gram. -/
theorem sourceCoordinatePair_jet_signed_defect_expansion (n k r s : ℕ)
    (x y : FiniteRealSpectralHilbert (2*n)) :
    let Bx := sourceRadialPair n k (materialJet r (sourceCoordinateInput n k x))
    let By := sourceRadialPair n k (materialJet s (sourceCoordinateInput n k y))
    let Dx := sourceRadialPair n k (sourceCoordinateJetDefect n k r x)
    let Dy := sourceRadialPair n k (sourceCoordinateJetDefect n k s y)
    canonicalCompletedNativeProjectiveChiralForm
      (sourceCoordinatePair n k (materialJet r x))
      (sourceCoordinatePair n k (materialJet s y)) =
      canonicalCompletedNativeProjectiveChiralForm Bx By +
        canonicalCompletedNativeProjectiveChiralForm Bx Dy +
        canonicalCompletedNativeProjectiveChiralForm Dx By +
        canonicalCompletedNativeProjectiveChiralForm Dx Dy := by
  dsimp only
  rw [sourceCoordinatePair_jet_eq_base_add_defect, sourceCoordinatePair_jet_eq_base_add_defect]
  simp only [canonicalCompletedNativeProjectiveChiralForm, Prod.fst_add, Prod.snd_add,
    inner_add_left, inner_add_right]
  ring

end
end CarrySelfAdjointOperator.LogGapConnection

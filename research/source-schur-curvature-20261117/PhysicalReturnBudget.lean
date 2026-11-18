import ProjectionLoss
import SchurLimit
import Mathlib.Tactic

/-!
# Exact incident–return budget in the original physical Cauchy carrier

This module imports the existing physical projections, synthesis, return,
radial source quotient, and the established theta/Green provenance.
The projected return head is retained exactly, not discarded.

The source-dependent contraction is an open analytic estimate, not an axiom
or theorem here. The first-order native source tangents prohibit a fixed
strict contraction at every radial scale for a nonzero basis direction.
-/

namespace CarryCauchyResidual
open CarrySelfAdjointOperator ChiralReturn CarryReturnDeflation CarryPositiveSquare
open Filter Topology
open scoped InnerProductSpace ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

/-- All terms are norms on the ORIGINAL physical carrier. -/
def physicalIncidentEnergy (k N : ℕ) (c : Fin N → ℂ) : ℝ :=
  ‖remainingIncident k N c‖^2
def physicalReturnComplementEnergy (k N : ℕ) (c : Fin N → ℂ) : ℝ :=
  ‖nativeOut k N c-returnedHead k N c‖^2
def physicalReturnHeadEnergy (k N : ℕ) (c : Fin N → ℂ) : ℝ :=
  ‖returnedHead k N c‖^2
def physicalSignedBalance (k N : ℕ) (c : Fin N → ℂ) : ℝ :=
  physicalIncidentEnergy k N c -
    (physicalReturnComplementEnergy k N c + physicalReturnHeadEnergy k N c)

/-- The exact literal physical ledger with the omitted return-head restored.
No positivity, eigenvalue input, or Gram approximation. -/
theorem full_physical_balance_eq_original (k N : ℕ) (c : Fin N → ℂ) :
    physicalSignedBalance k N c = (remainingPair k N c c).re := by
  have h := projection_loss_energy k N c
  unfold projectedBothPair at h
  simp only [Complex.sub_re, physical_inner_self_re] at h
  unfold physicalSignedBalance physicalIncidentEnergy
    physicalReturnComplementEnergy physicalReturnHeadEnergy
  linarith

/-- A sufficient *two-channel* relative budget, retaining the projected
return-head as a genuine loss. This is a deduction from actual source terms:
the two hypotheses below have not been proved for arbitrary n and k. -/
theorem physical_relative_two_loss_budget
    (k N : ℕ) (c : Fin N → ℂ)
    (ηhead ηtail : ℝ)
    (hh : physicalReturnHeadEnergy k N c ≤
      ηhead * physicalIncidentEnergy k N c)
    (ht : physicalReturnComplementEnergy k N c ≤
      ηtail * physicalIncidentEnergy k N c) :
    (1-ηhead-ηtail) * physicalIncidentEnergy k N c ≤
      (remainingPair k N c c).re := by
  rw [← full_physical_balance_eq_original]
  unfold physicalSignedBalance
  nlinarith

/-- Source budget with a lower margin in the correct radial normalization.
This is the appropriate strength to survive near-singular Schur pivots.
The hypotheses are explicit separate physical certification obligations. -/
theorem physical_margin_of_normalized_two_loss_budget
    (k N : ℕ) (c : Fin N → ℂ) (ηhead ηtail μ : ℝ)
    (hdef : 0 < oneDeficit k)
    (hη : 0 ≤ 1-ηhead-ηtail)
    (hh : physicalReturnHeadEnergy k N c ≤
      ηhead * physicalIncidentEnergy k N c)
    (ht : physicalReturnComplementEnergy k N c ≤
      ηtail * physicalIncidentEnergy k N c)
    (hI : μ * oneDeficit k ≤ physicalIncidentEnergy k N c) :
    (1-ηhead-ηtail)*μ ≤
      (remainingPair k N c c).re/oneDeficit k := by
  have hh' := physical_relative_two_loss_budget k N c ηhead ηtail hh ht
  have hs := mul_le_mul_of_nonneg_left hI hη
  apply (le_div_iff₀ hdef).mpr
  nlinarith

/-- A *critical*, ADDITIVE margin is measured against the exact radial
denominator. Unlike fixed multiplicative contraction, this budget is
compatible with leading incident/return energies having ratio → 1.
No sign of the signed original form is assumed. -/
theorem physical_critical_additive_budget
    (k N : ℕ) (c : Fin N → ℂ) (μ : ℝ)
    (hdef : 0 < oneDeficit k)
    (hbudget :
      physicalReturnComplementEnergy k N c +
      physicalReturnHeadEnergy k N c + μ*oneDeficit k ≤
        physicalIncidentEnergy k N c) :
    μ ≤ (remainingPair k N c c).re/oneDeficit k := by
  rw [← full_physical_balance_eq_original]
  unfold physicalSignedBalance
  apply (le_div_iff₀ hdef).mpr
  linarith

/-- The literal SAME-Cauchy Gram comparison from the unmodified physical
incident and returned synthesizers. All cross terms are preserved.
The return head was not deleted; it was recombined exactly. -/
theorem physical_critical_budget_same_cauchy
    (k N : ℕ) (c : Fin N → ℂ) :
    physicalSignedBalance k (N+1) (tailInput c) =
      ‖tailSynthesis k N (incidentCoordinates k N c)‖^2 -
      ‖tailSynthesis k N (returnedCoordinates k N c)‖^2 := by
  rw [full_physical_balance_eq_original,
    residual_same_cauchy]
  simp only [Complex.sub_re, physical_inner_self_re]

/-- Both coefficient channels have the SAME nonzero leading tangent. -/
theorem native_incident_return_tangent_equal (i : ℕ) :
    (Tendsto
      (fun k => incidentCoefficient k i*radialScale k) atTop
        (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(i:ℂ)))) ∧
    (Tendsto
      (fun k => returnedCoefficient k i*radialScale k) atTop
        (nhds (4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(i:ℂ)))) :=
  ⟨incidentCoefficient_tangent i, returnedCoefficient_tangent i⟩

/-- The EXACT source-level cancellation behind the matching tangents:
the completed radial feedback contains the original deficit d_k and the
full returned coefficient. -/
theorem feedbackDenominator_eq_deficit_sub_return
    (k n : ℕ) :
    feedbackDenominator k n =
      (oneDeficit k : ℂ) -
        conj (oneReturn k)*returnedCoefficient k n := by
  unfold feedbackDenominator returnedCoefficient
  rw [← native_deficit]
  unfold deficit
  ring

theorem critical_incident_minus_return_exact (k n : ℕ) :
    incidentCoefficient k n - returnedCoefficient k n =
      ((n:ℂ)/((n:ℂ)+2))*(oneDeficit k:ℂ) -
      (((n:ℂ)/((n:ℂ)+2))*conj (oneReturn k)+1) *
        returnedCoefficient k n := by
  rw [incidentCoefficient, feedbackDenominator_eq_deficit_sub_return]
  ring

/-- The first order of the incident-minus-return coefficient vanishes in
the ORIGINAL radial scale. Higher jets, not a fixed contraction gap,
are needed to certify the remaining signed energy. -/
theorem critical_incident_minus_return_tangent_zero (n : ℕ) :
    Tendsto (fun k =>
       (incidentCoefficient k n - returnedCoefficient k n)*radialScale k)
       atTop (nhds (0:ℂ)) := by
  have ht := (incidentCoefficient_tangent n).sub (returnedCoefficient_tangent n)
  simpa only [sub_mul, sub_self] using ht

/-- A simple pointwise strict contraction in radial coordinates is
incompatible with the genuine completed native tangent at any nonzero i.
Here both energies are kept and their ratio is asymptotically one. -/
theorem native_return_over_incident_coeff_energy_tendsto_one
    (i : ℕ) (hi : 0 < i) :
    Tendsto (fun k =>
      Complex.normSq (returnedCoefficient k i * radialScale k) /
        Complex.normSq (incidentCoefficient k i * radialScale k))
      atTop (nhds (1:ℝ)) := by
  let a : ℂ := 4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ)*(i:ℂ)
  have ha : a ≠ 0 := by
    have h0 : (canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 := by
      exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
    have hi' : (i:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hi
    exact mul_ne_zero (mul_ne_zero (by norm_num) h0) hi'
  have ha2 : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  have hu : Tendsto (fun k =>
      Complex.normSq (incidentCoefficient k i*radialScale k))
      atTop (nhds (Complex.normSq a)) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp (incidentCoefficient_tangent i)
  have hv : Tendsto (fun k =>
      Complex.normSq (returnedCoefficient k i*radialScale k))
      atTop (nhds (Complex.normSq a)) :=
    Complex.continuous_normSq.continuousAt.tendsto.comp (returnedCoefficient_tangent i)
  have ht := hv.div hu ha2
  convert ht using 1
  · rfl
  · field_simp

/-- Exact equality of the physical Cauchy feature and its first-Schur
isometric successor; no target Gram was inserted. -/
theorem isometric_feature_norm_sq_eq
    (k i : ℕ) (hi : i ≠ 0) :
    ‖isometricFeature k i‖^2 = ‖feature k i‖^2 := by
  have hh := isometricFeature_inner k i i hi hi
  simpa only [physical_inner_self_re] using congrArg Complex.re hh

/-- Same physical carrier norm, with the authentic coefficient channels.
The raw return and incident energies differ only by their scalar factors. -/
theorem native_basis_return_incident_cross_energy
    (k N : ℕ) (i : Fin N) (hi : i.val ≠ 0) :
    ‖nativeOut k N (Pi.single i 1)‖^2 *
      Complex.normSq (incidentCoefficient k i) =
    ‖remainingIncident k N (Pi.single i 1)‖^2 *
      Complex.normSq (returnedCoefficient k i) := by
  rw [nativeOut_basis,
    remainingIncident_basis_isometric k N i hi,
    norm_smul, norm_smul]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  calc
    (‖returnedCoefficient k ↑i‖ * ‖feature k ↑i‖)^2 *
        ‖incidentCoefficient k ↑i‖^2 =
      ‖returnedCoefficient k ↑i‖^2 *
        ‖incidentCoefficient k ↑i‖^2 *
        ‖feature k ↑i‖^2 := by ring
    _ = _ := by rw [← isometric_feature_norm_sq_eq k i hi]; ring

/-- Cauchy tail basis vectors are strictly nonzero in the original carrier. -/
theorem cauchy_feature_norm_sq (k i : ℕ) :
    ‖feature k i‖^2 = ((k:ℝ)+1)/((i:ℝ)+(i:ℝ)+2) := by
  have hh := congrArg Complex.re (feature_inner k i i)
  simp only [physical_inner_self_re] at hh
  have hc : cauchy k i i =
      ((((k:ℝ)+1)/((i:ℝ)+(i:ℝ)+2)) : ℂ) := by
    simp [cauchy]
  rw [hc] at hh
  norm_cast at hh
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using hh

theorem cauchy_feature_norm_sq_pos (k i : ℕ) :
    0 < ‖feature k i‖^2 := by
  rw [cauchy_feature_norm_sq]
  positivity

theorem native_basis_incident_norm_sq
    (k N : ℕ) (i : Fin N) (hi : i.val ≠ 0) :
    ‖remainingIncident k N (Pi.single i 1)‖^2 =
      Complex.normSq (incidentCoefficient k i) * ‖feature k i‖^2 := by
  rw [remainingIncident_basis_isometric k N i hi, norm_smul,
    mul_pow, Complex.normSq_eq_norm_sq,
    isometric_feature_norm_sq_eq k i hi]

theorem native_basis_return_norm_sq
    (k N : ℕ) (i : Fin N) :
    ‖nativeOut k N (Pi.single i 1)‖^2 =
      Complex.normSq (returnedCoefficient k i) * ‖feature k i‖^2 := by
  rw [nativeOut_basis, norm_smul, mul_pow, Complex.normSq_eq_norm_sq]

theorem native_incident_coefficient_eventually_ne_zero
    (i : ℕ) (hi : 0 < i) :
    ∀ᶠ k : ℕ in atTop, incidentCoefficient k i ≠ 0 := by
  have h0 : (canonicalCompletedNativeLogDerivativeMoment 0:ℂ) ≠ 0 := by
    exact_mod_cast canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hi' : (i:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hi
  have ht := (incidentCoefficient_tangent i).eventually_ne
    (mul_ne_zero (mul_ne_zero (by norm_num) h0) hi')
  filter_upwards [ht] with k hk
  intro hzero
  apply hk
  simp [hzero]

/-- This is a theorem about actual physical norms, not just coefficients:
the relative return-to-incident energy tends to ONE at every non-head basis
coordinate, with the full original Cauchy norm in both channels. -/
theorem native_physical_basis_return_energy_ratio_tendsto_one
    (N : ℕ) (i : Fin N) (hi : i.val ≠ 0) :
    Tendsto (fun k =>
      ‖nativeOut k N (Pi.single i 1)‖^2 /
        ‖remainingIncident k N (Pi.single i 1)‖^2)
      atTop (nhds (1:ℝ)) := by
  have hi0 : 0 < i.val := Nat.pos_of_ne_zero hi
  have ht := native_return_over_incident_coeff_energy_tendsto_one i.val hi0
  apply ht.congr'
  filter_upwards [native_incident_coefficient_eventually_ne_zero i.val hi0] with k hk
  have hfeature : ‖feature k i‖^2 ≠ 0 :=
    (cauchy_feature_norm_sq_pos k i).ne'
  have ha : Complex.normSq (incidentCoefficient k i) ≠ 0 :=
    (Complex.normSq_pos.mpr hk).ne'
  have hfn : ‖feature k i‖ ≠ 0 := by
    intro hzero
    exact hfeature (by simp [hzero])
  have hr : Complex.normSq (radialScale k) ≠ 0 :=
    (Complex.normSq_pos.mpr (radialScale_ne_zero k)).ne'
  rw [native_basis_return_norm_sq k N i,
    native_basis_incident_norm_sq k N i hi]
  rw [Complex.normSq_mul, Complex.normSq_mul]
  field_simp [ha, hfeature, hfn, hr]

/-- Impossible uniform fixed strict contraction of the original return:
for any ρ<1 it is EVENTUALLY violated on each non-head basis direction. -/
theorem native_physical_return_not_uniformly_contractive
    (N : ℕ) (i : Fin N) (hi : i.val ≠ 0)
    (ρ : ℝ) (hρ : ρ < 1) :
    ∀ᶠ k : ℕ in atTop,
      ρ * ‖remainingIncident k N (Pi.single i 1)‖^2 <
        ‖nativeOut k N (Pi.single i 1)‖^2 := by
  have ht := native_physical_basis_return_energy_ratio_tendsto_one N i hi
  have hlt : ∀ᶠ k : ℕ in atTop,
      ρ < ‖nativeOut k N (Pi.single i 1)‖^2 /
            ‖remainingIncident k N (Pi.single i 1)‖^2 :=
    (tendsto_order.mp ht).1 ρ hρ
  have hi0 : 0 < i.val := Nat.pos_of_ne_zero hi
  filter_upwards [hlt, native_incident_coefficient_eventually_ne_zero i.val hi0]
    with k hlt hne
  have hs : 0 < ‖remainingIncident k N (Pi.single i 1)‖^2 := by
    rw [native_basis_incident_norm_sq k N i hi]
    exact mul_pos (Complex.normSq_pos.mpr hne) (cauchy_feature_norm_sq_pos k i)
  exact (lt_div_iff₀ hs).mp hlt

/-! ## Physical → first-Schur boundary transport (already existing radial jet)

Unlike a fixed strict contraction, a margin measured in units of the
actual radial deficit can survive the critical cancellation.
-/

def physicalJetSignedBudget (n k : ℕ) (x : Fin (2*(n+1)) → ℂ) : ℝ :=
  physicalSignedBalance k (2*(n+1))
    (nativeSourceChiralJetInput (n+1) k x)

theorem physicalJetSignedBudget_eq_jetSchur_re
    (n k : ℕ) (x : Fin (2*(n+1)) → ℂ) (hd : oneDeficit k ≠ 0) :
    physicalJetSignedBudget n k x / oneDeficit k =
      (jetSchurRemainder (n+1) k x x).re := by
  unfold physicalJetSignedBudget
  rw [full_physical_balance_eq_original]
  unfold jetSchurRemainder jetRemainingPair
  have h (z : ℂ) (d : ℝ) (hd : d ≠ 0) :
      (z/(d:ℂ)).re = z.re/d := by
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, Complex.normSq_ofReal]
    field_simp [hd]
    ring
  exact (h _ _ hd).symm

/-- The full physical budget converges to the genuine first-head
Schur reduction of the COMPLETE canonical boundary kernel. This has no
positivity hypothesis; the physical return head is retained. -/
theorem physicalJetSignedBudget_normalized_tendsto_firstSchur
    (n : ℕ) (x : Fin (2*(n+1)) → ℂ) :
    Tendsto (fun k =>
      physicalJetSignedBudget n k x / oneDeficit k)
      atTop
      (nhds ((2*(canonicalBoundaryPair (n+1) x x -
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x) *
          canonicalBoundaryPair (n+1) (headBoundary n) x /
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ))).re)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (jet_remaining_schur_tendsto n x x)
  apply ht.congr'
  filter_upwards [oneDeficit_eventually_pos] with k hk
  exact (physicalJetSignedBudget_eq_jetSchur_re n k x hk.ne').symm

/-- A positive normalized physical surplus yields a positive limiting
FIRST-Schur boundary margin, but does NOT close arbitrary higher Schur
directions without a further deflation/calibration. -/
theorem firstSchur_margin_of_eventual_physical_budget
    (n : ℕ) (x : Fin (2*(n+1)) → ℂ)
    (μ : ℝ) (hμ : 0 < μ)
    (hbudget : ∀ᶠ k : ℕ in atTop,
      μ ≤ physicalJetSignedBudget n k x / oneDeficit k) :
    0 < (2*(canonicalBoundaryPair (n+1) x x -
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x) *
          canonicalBoundaryPair (n+1) (headBoundary n) x /
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ))).re := by
  have ht := physicalJetSignedBudget_normalized_tendsto_firstSchur n x
  have hgt : μ ≤
      (2*(canonicalBoundaryPair (n+1) x x -
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x) *
          canonicalBoundaryPair (n+1) (headBoundary n) x /
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ))).re :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds (x := μ)) ht hbudget
  exact lt_of_lt_of_le hμ hgt

/-- The actual radial jet is the original physical source. If its signed
return deficit has a positive ADDITIVE margin of order oneDeficit, then
the limiting FIRST-Schur canonical boundary energy has a strict positive
margin. This is a CONDITIONAL bridge; no positivity of higher pivots is
postulated or proved. -/
theorem canonical_firstSchur_pos_of_physical_critical_budget
    (n : ℕ) (x : Fin (2*(n+1)) → ℂ)
    (μ : ℝ) (hμ : 0 < μ)
    (hbudget : ∀ᶠ k : ℕ in atTop,
      physicalReturnComplementEnergy k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k x) +
      physicalReturnHeadEnergy k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k x) +
      μ*oneDeficit k ≤
        physicalIncidentEnergy k (2*(n+1))
          (nativeSourceChiralJetInput (n+1) k x)) :
    0 < (2*(canonicalBoundaryPair (n+1) x x -
        conj (canonicalBoundaryPair (n+1) (headBoundary n) x) *
          canonicalBoundaryPair (n+1) (headBoundary n) x /
          (canonicalCompletedNativeLogDerivativeMoment 0:ℂ))).re := by
  apply firstSchur_margin_of_eventual_physical_budget n x μ hμ
  filter_upwards [hbudget, oneDeficit_eventually_pos] with k hbudget hk
  unfold physicalJetSignedBudget
  rw [full_physical_balance_eq_original]
  exact physical_critical_additive_budget k _ _ μ hk hbudget

#print axioms canonical_firstSchur_pos_of_physical_critical_budget
#print axioms physical_critical_budget_same_cauchy
#print axioms physical_critical_additive_budget
#print axioms physicalJetSignedBudget_normalized_tendsto_firstSchur
#print axioms critical_incident_minus_return_exact
#print axioms critical_incident_minus_return_tangent_zero
#print axioms native_physical_basis_return_energy_ratio_tendsto_one
#print axioms native_physical_return_not_uniformly_contractive
#print axioms native_basis_return_incident_cross_energy
#print axioms full_physical_balance_eq_original
#print axioms physical_relative_two_loss_budget
#print axioms native_incident_return_tangent_equal
#print axioms native_return_over_incident_coeff_energy_tendsto_one

end
end CarryCauchyResidual

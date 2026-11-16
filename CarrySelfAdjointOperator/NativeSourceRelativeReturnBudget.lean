import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import CarrySelfAdjointOperator.CompletedNativeSemidefiniteHardyGate
import Mathlib.Tactic

/-!
# Relative return budgets for the original native source synthesis

The incident and returned vectors below are the existing synthesis maps,
after the existing `nativeSourceChiralJetInput`.  The budget is an explicit
conditional premise: this module does not prove that the C² source satisfies
it.  The incident growth factor uses the current sup norm on `Fin N → ℂ`.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The original incident synthesis after the native finite-difference input
map. This is not synthesized from a moment Gram matrix. -/
def nativeSourceOriginalIncident (n k : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k (2*n) (nativeSourceChiralJetInput n k x)

/-- The original returned synthesis after the same native input map. -/
def nativeSourceOriginalReturn (n k : ℕ) (x : Fin (2*n) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialReturnedSynthesis k (2*n) (nativeSourceChiralJetInput n k x)

/-- Linear map underlying the original incident synthesis in source
coordinates. -/
def nativeSourceIncidentOperator (n k : ℕ) :
    (Fin (2*n) → ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier :=
  (radialIncidentSynthesis k (2*n)).comp (nativeSourceChiralJetInput n k)

@[simp] theorem nativeSourceIncidentOperator_apply (n k : ℕ)
    (x : Fin (2*n) → ℂ) :
    nativeSourceIncidentOperator n k x = nativeSourceOriginalIncident n k x := rfl

/-- The operator norm of the original incident map is a checked growth factor
for the existing domain norm on `Fin (2*n) → ℂ`. -/
def nativeSourceIncidentOperatorNormBudget (n k : ℕ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (nativeSourceIncidentOperator n k)‖^2

theorem nativeSourceIncidentOperatorNormBudget_nonneg (n k : ℕ) :
    0 ≤ nativeSourceIncidentOperatorNormBudget n k := by
  exact sq_nonneg _

/-- The current Pi norm is the sup norm, as witnessed coordinatewise. This
also records the exact domain norm used by the operator-norm budget. -/
theorem nativeSourceInput_coordinate_norm_le (n : ℕ)
    (x : Fin (2*n) → ℂ) (a : Fin (2*n)) : ‖x a‖ ≤ ‖x‖ :=
  norm_le_pi_norm x a

theorem nativeSourceIncident_norm_sq_le_operatorNormBudget (n k : ℕ)
    (x : Fin (2*n) → ℂ) :
    ‖nativeSourceOriginalIncident n k x‖^2 ≤
      nativeSourceIncidentOperatorNormBudget n k * ‖x‖^2 := by
  let I : (Fin (2*n) → ℂ) →L[ℂ] CanonicalCompletedNativeChiralCauchyCarrier :=
    LinearMap.toContinuousLinearMap (nativeSourceIncidentOperator n k)
  have hnorm : ‖nativeSourceIncidentOperator n k x‖ ≤ ‖I‖ * ‖x‖ := by
    exact I.le_opNorm x
  have hI : 0 ≤ ‖I‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquared : ‖nativeSourceIncidentOperator n k x‖^2 ≤ (‖I‖ * ‖x‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) hI).2 hnorm
  simpa only [nativeSourceIncidentOperator_apply,
    nativeSourceIncidentOperatorNormBudget, I, mul_pow] using hsquared

/-- Existing storage convergence, rewritten as convergence of the original
incident and return vectors in their original carrier. -/
theorem nativeSourceOriginal_synthesis_eventually_energy_control
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |2 * (‖nativeSourceOriginalIncident n k x‖^2 -
        ‖nativeSourceOriginalReturn n k x‖^2) -
          nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ ε * ‖x‖^2 := by
  filter_upwards [storage_one_chiralJetInput_eventually_energy_control n ε hε]
    with k hk
  intro x
  have h := hk x
  rw [storage_re_eq_norm_balance] at h
  simpa [nativeSourceOriginalIncident, nativeSourceOriginalReturn,
    radialIncidentSynthesis, radialReturnedSynthesis] using h

/-- Additive return budget. The error sequence need only converge to zero; no
positivity assumption on its terms is needed. -/
def HasNativeSourceAdditiveReturnBudget : Prop :=
  ∀ n, ∃ e : ℕ → ℝ,
    Tendsto e atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      ‖nativeSourceOriginalReturn n k x‖^2 ≤
        ‖nativeSourceOriginalIncident n k x‖^2 + e k * ‖x‖^2

/-- An additive relative estimate in the original synthesis coordinates,
together with the existing storage convergence, forces the original finite
boundary energy to be nonnegative. -/
theorem nativeSourceFiniteBoundaryEnergy_nonneg_of_additiveReturnBudget
    (hbudget : HasNativeSourceAdditiveReturnBudget) :
    ∀ n (x : Fin (2*n) → ℂ),
      0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
  intro n x
  rcases hbudget n with ⟨e, he, hreturn⟩
  let R : ℝ := ‖x‖^2
  have hR : 0 ≤ R := sq_nonneg _
  by_contra hnot
  have hEneg : nativeSourceFiniteBoundaryEnergy (2*n) x < 0 :=
    lt_of_not_ge hnot
  let δ : ℝ := -nativeSourceFiniteBoundaryEnergy (2*n) x / (8 * (R + 1))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (neg_pos.mpr hEneg) (by positivity)
  have hreturnSmall : ∀ᶠ k : ℕ in atTop, ∀ x' : Fin (2*n) → ℂ,
      ‖nativeSourceOriginalReturn n k x'‖^2 ≤
        ‖nativeSourceOriginalIncident n k x'‖^2 + e k * ‖x'‖^2 := hreturn
  have henergy := nativeSourceOriginal_synthesis_eventually_energy_control n δ hδ
  have heSmall : ∀ᶠ k : ℕ in atTop, |e k| < δ := by
    filter_upwards [he.eventually (Metric.ball_mem_nhds 0 hδ)] with k hk
    simpa [Real.dist_eq] using hk
  have hcommon : ∀ᶠ k : ℕ in atTop,
      (∀ x' : Fin (2*n) → ℂ,
        ‖nativeSourceOriginalReturn n k x'‖^2 ≤
          ‖nativeSourceOriginalIncident n k x'‖^2 + e k * ‖x'‖^2) ∧
      (∀ x' : Fin (2*n) → ℂ,
        |2 * (‖nativeSourceOriginalIncident n k x'‖^2 -
          ‖nativeSourceOriginalReturn n k x'‖^2) -
            nativeSourceFiniteBoundaryEnergy (2*n) x'| ≤ δ * ‖x'‖^2) ∧
      |e k| < δ := by
    filter_upwards [hreturnSmall, henergy, heSmall] with k hr hc hs
    exact ⟨hr, hc, hs⟩
  rcases hcommon.exists with ⟨k, ⟨hr, hc, hs⟩⟩
  have hrx := hr x
  have hcx := hc x
  have heAbs := abs_lt.mp hs
  have heR : -δ * R ≤ e k * R :=
    mul_le_mul_of_nonneg_right heAbs.1.le hR
  have hreturnLower :
      -(e k * R) ≤
        ‖nativeSourceOriginalIncident n k x‖^2 -
          ‖nativeSourceOriginalReturn n k x‖^2 := by
    dsimp [R]
    nlinarith [hrx]
  have henergyUpper := (abs_le.mp hcx).2
  have hElower : -3 * δ * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
    dsimp [R] at hreturnLower heR
    nlinarith [hreturnLower, henergyUpper, heR]
  have hδR : 3 * δ * R < -nativeSourceFiniteBoundaryEnergy (2*n) x := by
    calc
      3 * δ * R =
          (-nativeSourceFiniteBoundaryEnergy (2*n) x) *
            (3 * R / (8 * (R + 1))) := by
        dsimp [δ]
        ring
      _ < (-nativeSourceFiniteBoundaryEnergy (2*n) x) * 1 := by
        apply mul_lt_mul_of_pos_left _ (neg_pos.mpr hEneg)
        apply (div_lt_iff₀ (by positivity : 0 < 8 * (R + 1))).2
        nlinarith [hR]
      _ = -nativeSourceFiniteBoundaryEnergy (2*n) x := by ring
  linarith

/-- Multiplicative control plus an incident operator bound gives the
additive budget with error `η(k) * B(k)`. Thus `η → 0` alone is not used. -/
def HasNativeSourceMultiplicativeReturnBudget : Prop :=
  ∀ n, ∃ η B : ℕ → ℝ,
    (∀ k, 0 ≤ η k) ∧
    (∀ k, 0 ≤ B k) ∧
    Tendsto (fun k => η k * B k) atTop (nhds 0) ∧
    (∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      ‖nativeSourceOriginalReturn n k x‖^2 ≤
        (1 + η k) * ‖nativeSourceOriginalIncident n k x‖^2) ∧
    (∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      ‖nativeSourceOriginalIncident n k x‖^2 ≤ B k * ‖x‖^2)

theorem nativeSourceAdditiveReturnBudget_of_multiplicative
    (hbudget : HasNativeSourceMultiplicativeReturnBudget) :
    HasNativeSourceAdditiveReturnBudget := by
  intro n
  rcases hbudget n with ⟨η, B, hη, hB, hlim, hreturn, hincident⟩
  refine ⟨fun k => η k * B k, hlim, ?_⟩
  filter_upwards [hreturn, hincident] with k hreturnk hincidentk
  intro x
  have hηI := mul_le_mul_of_nonneg_left (hincidentk x) (hη k)
  calc
    ‖nativeSourceOriginalReturn n k x‖^2 ≤
        (1 + η k) * ‖nativeSourceOriginalIncident n k x‖^2 := hreturnk x
    _ = ‖nativeSourceOriginalIncident n k x‖^2 +
        η k * ‖nativeSourceOriginalIncident n k x‖^2 := by ring
    _ ≤ ‖nativeSourceOriginalIncident n k x‖^2 + η k * (B k * ‖x‖^2) :=
      add_le_add_right hηI _
    _ = ‖nativeSourceOriginalIncident n k x‖^2 +
        (η k * B k) * ‖x‖^2 := by ring

/-- A relative return bound with `η(k) * B(k) → 0`, where the incident
growth factor is checked by its operator norm on the existing sup-norm domain. -/
def HasNativeSourceOperatorRelativeReturnBudget : Prop :=
  ∀ n, ∃ η : ℕ → ℝ,
    (∀ k, 0 ≤ η k) ∧
    Tendsto (fun k => η k * nativeSourceIncidentOperatorNormBudget n k)
      atTop (nhds 0) ∧
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      ‖nativeSourceOriginalReturn n k x‖^2 ≤
        (1 + η k) * ‖nativeSourceOriginalIncident n k x‖^2

theorem nativeSourceMultiplicativeReturnBudget_of_operatorNormBudget
    (hbudget : HasNativeSourceOperatorRelativeReturnBudget) :
    HasNativeSourceMultiplicativeReturnBudget := by
  intro n
  rcases hbudget n with ⟨η, hη, hlim, hreturn⟩
  refine ⟨η, nativeSourceIncidentOperatorNormBudget n, hη,
    nativeSourceIncidentOperatorNormBudget_nonneg n, hlim, hreturn, ?_⟩
  filter_upwards [] with k
  intro x
  exact nativeSourceIncident_norm_sq_le_operatorNormBudget n k x

/-- Additive return budgets close the existing all-order PSD-to-PD gate,
using its harmonic nonrecurrence branch and no positive-real-zero premise. -/
theorem canonicalHankelPair_posDef_of_nativeSourceAdditiveReturnBudget_of_harmonicNonrecurrence
    (hbudget : HasNativeSourceAdditiveReturnBudget) :
    (∀ n, (hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef) ∧
    (∀ n, (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef) := by
  apply canonicalHankelPair_posDef_of_nativeSourceBoundary_nonneg_of_harmonicNonrecurrence
  exact nativeSourceFiniteBoundaryEnergy_nonneg_of_additiveReturnBudget hbudget

/-- A relative return estimate closes the same existing gate when its
relative defect times the verified incident operator norm budget tends to zero.
The budget itself remains an explicit hypothesis. -/
theorem canonicalHankelPair_posDef_of_nativeSourceOperatorRelativeReturnBudget_of_harmonicNonrecurrence
    (hbudget : HasNativeSourceOperatorRelativeReturnBudget) :
    (∀ n, (hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef) ∧
    (∀ n, (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef) := by
  exact canonicalHankelPair_posDef_of_nativeSourceAdditiveReturnBudget_of_harmonicNonrecurrence
    (nativeSourceAdditiveReturnBudget_of_multiplicative
      (nativeSourceMultiplicativeReturnBudget_of_operatorNormBudget hbudget))

end
end CarrySelfAdjointOperator

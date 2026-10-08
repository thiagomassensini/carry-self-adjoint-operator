import CarrySelfAdjointOperator.CompletedNativeChiralReturnGreenBoundaryTower
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Boundary cancellation in the original completed Cauchy source

The finite boundary jet map uses the existing degree jets and standard
coefficient space. Its kernel retains genuine nonzero incident states whenever
fewer jets than coefficients are observed. Repeated Green transport vanishes
on this kernel through the corresponding degree order. No metric or source is
replaced, and no moment positivity is used.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- The first r endpoint degree jets of the SAME coefficient synthesis. -/
def radialBoundaryJetAnalysis (N r : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun d j := radialEulerBoundaryJet d j
  map_add' d e := by
    funext j
    simp [radialEulerBoundaryJet, add_mul, Finset.sum_add_distrib]
  map_smul' z d := by
    funext j
    simp [radialEulerBoundaryJet, mul_assoc, Finset.mul_sum]

/-- Boundary cancellations are an existing-metric subspace, not a quotient
that discards the unobserved incident source. -/
def radialBoundaryJetKernel (N r : ℕ) : Submodule ℂ (Fin N → ℂ) :=
  (radialBoundaryJetAnalysis N r).ker

theorem mem_radialBoundaryJetKernel (N r : ℕ) (d : Fin N → ℂ) :
    d ∈ radialBoundaryJetKernel N r ↔
      ∀ m : ℕ, m < r → radialEulerBoundaryJet d m = 0 := by
  constructor
  · intro h m hm
    exact congrFun (LinearMap.mem_ker.mp h) ⟨m, hm⟩
  · intro h
    apply LinearMap.mem_ker.mpr
    funext j
    exact h j j.isLt

/-- Retaining more endpoint jets shrinks the same cancellation sector;
no source data is discarded by an implicit quotient. -/
theorem radialBoundaryJetKernel_antitone (N r s : ℕ) (hrs : r ≤ s) :
    radialBoundaryJetKernel N s ≤ radialBoundaryJetKernel N r := by
  intro d hd
  rw [mem_radialBoundaryJetKernel] at hd ⊢
  intro m hm
  exact hd m (lt_of_lt_of_le hm hrs)

/-- A finite set of endpoint jets cannot observe all higher coefficient
orders. This is rank-nullity, with no source or metric fitting. -/
theorem radialBoundaryJetKernel_ne_bot (N r : ℕ) (hr : r < N) :
    radialBoundaryJetKernel N r ≠ ⊥ := by
  apply LinearMap.ker_ne_bot_of_finrank_lt
  simpa using hr

/-- Nonzero complete incident states survive in every nontrivial boundary
cancellation sector. The source monomial synthesis remains injective. -/
theorem exists_nonzero_incident_boundary_cancellation (k N r : ℕ) (hr : r < N) :
    ∃ d : Fin N → ℂ, radialIncidentSynthesis k N d ≠ 0 ∧
      ∀ m : ℕ, m < r → radialEulerBoundaryJet d m = 0 := by
  obtain ⟨d, hd, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (radialBoundaryJetKernel_ne_bot N r hr)
  refine ⟨d, ?_, (mem_radialBoundaryJetKernel N r d).mp hd⟩
  intro hz
  apply hn
  apply radialIncidentSynthesis_injective k N
  simpa using hz

/-- Full polarization: if the first r jets vanish on BOTH sources, each
ordered boundary cross disappears for every transported degree m <= 2r. -/
theorem radialEulerPower_green_boundary_eq_zero_of_cancellation
    (k N r m : ℕ) (d e : Fin N → ℂ)
    (hd : d ∈ radialBoundaryJetKernel N r)
    (he : e ∈ radialBoundaryJetKernel N r) (hm : m ≤ 2 * r) :
    inner ℂ (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N m e) -
      (-1 : ℂ) ^ m * inner ℂ (radialEulerPowerSynthesis k N m d)
        (radialIncidentSynthesis k N e) = 0 := by
  have h := radialEulerPower_green_boundary k N m d e
  rw [radialEulerPowerSynthesis_zero, radialEulerPowerSynthesis_zero] at h
  rw [h]
  have hz : (∑ a ∈ Finset.range m, (-1 : ℂ) ^ a *
      conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet e (m - 1 - a)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have ha' := Finset.mem_range.mp ha
    by_cases har : a < r
    · rw [(mem_radialBoundaryJetKernel N r d).mp hd a har]
      simp
    · have hb : m - 1 - a < r := by omega
      rw [(mem_radialBoundaryJetKernel N r e).mp he _ hb]
      simp
  rw [hz, mul_zero]

/-- The odd-degree Hermitian energy vanishes on the cancellation sector;
this does NOT assert that the full completed-source energy vanishes. -/
theorem radialEulerPower_energy_eq_zero_of_cancellation
    (k N r m : ℕ) (d : Fin N → ℂ)
    (hd : d ∈ radialBoundaryJetKernel N r) (hm : m ≤ 2 * r) (ho : Odd m) :
    (inner ℂ (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N m d)).re = 0 := by
  have h := congrArg Complex.re
    (radialEulerPower_green_boundary_eq_zero_of_cancellation k N r m d d hd hd hm)
  rw [Odd.neg_one_pow ho] at h
  have hc := congrArg Complex.re (inner_conj_symm
    (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N m d))
  simp only [Complex.conj_re] at hc
  simp only [neg_one_mul, sub_neg_eq_add, Complex.add_re, Complex.zero_re] at h
  linarith

/-- No fixed finite set of endpoint jets controls the complete incident norm
once a nonzero cancellation sector exists. This is a local observability
obstruction, NOT a no-go for native storage positivity. -/
theorem not_radialBoundaryJet_coercive (k N r : ℕ) (hr : r < N) (C : ℝ) :
    ¬ (∀ d : Fin N → ℂ, ‖radialIncidentSynthesis k N d‖ ^ 2 ≤
      C * ∑ j : Fin r, Complex.normSq (radialEulerBoundaryJet d j)) := by
  obtain ⟨d, hd, hj⟩ := exists_nonzero_incident_boundary_cancellation k N r hr
  intro h
  have hz : (∑ j : Fin r, Complex.normSq (radialEulerBoundaryJet d j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hj j j.isLt]
    simp
  have hb := h d
  rw [hz, mul_zero] at hb
  have hn := norm_pos_iff.mpr hd
  nlinarith [sq_nonneg ‖radialIncidentSynthesis k N d‖]

/-- Raw real odd jet of the native transverse source slope, with the actual
radial and factorial normalization. No canonical moment occurs here.
No approximation rate or all-order sign is asserted for these coefficients. -/
def radialCompletedOddSourceJetScale (k j : ℕ) : ℝ :=
  (iteratedDeriv (2 * j + 1)
    (fun y : ℂ => -Complex.I * completedNativeOperatorLogDerivative (Complex.I * y)) 0).re /
      (((2 * j + 1).factorial : ℝ) * ((k : ℝ) + 1) ^ (2 * j + 1))

/-- Source-derived odd degree terms, synthesized in the unchanged Cauchy
carrier before any pairing is taken. -/
def radialCompletedOddSourceJetSynthesis (k N r : ℕ) (d : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ j ∈ Finset.range r, (radialCompletedOddSourceJetScale k j : ℂ) •
    radialEulerPowerSynthesis k N (2 * j + 1) d

/-- The entire exact source minus its own finite odd jets. This subtraction
retains every higher term, tail and completion; it is not a new source. -/
def radialCompletedOddSourceRemainderSynthesis (k N r : ℕ) (d : Fin N → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k N (fun i => d i * radialCompletedSlope k i) -
    radialCompletedOddSourceJetSynthesis k N r d

/-- Exact vector reconstruction, independent of any Taylor remainder bound. -/
theorem radialCompletedSlopeSynthesis_eq_oddJets_add_remainder
    (k N r : ℕ) (d : Fin N → ℂ) :
    radialIncidentSynthesis k N (fun i => d i * radialCompletedSlope k i) =
      radialCompletedOddSourceJetSynthesis k N r d +
        radialCompletedOddSourceRemainderSynthesis k N r d := by
  unfold radialCompletedOddSourceRemainderSynthesis
  abel

/-- All r lower odd source jets contribute zero Hermitian energy on the
r-jet cancellation sector. The full source remainder is still retained. -/
theorem radialCompletedOddSourceJet_energy_eq_zero_of_cancellation
    (k N r : ℕ) (d : Fin N → ℂ) (hd : d ∈ radialBoundaryJetKernel N r) :
    (inner ℂ (radialIncidentSynthesis k N d)
      (radialCompletedOddSourceJetSynthesis k N r d)).re = 0 := by
  classical
  simp only [radialCompletedOddSourceJetSynthesis, inner_sum, inner_smul_right,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  apply Finset.sum_eq_zero
  intro j hj
  have hm : 2 * j + 1 ≤ 2 * r := by have h := Finset.mem_range.mp hj; omega
  rw [radialEulerPower_energy_eq_zero_of_cancellation k N r (2 * j + 1) d hd hm
    (by exact ⟨j, by omega⟩), mul_zero]

/-- Full completed storage in source-amplitude coordinates. Synthesis of F
and -F' precedes this readout; the original source denominators are the only
regularity hypotheses. -/
theorem storage_one_eq_complete_slope_pairing (k N : ℕ) (d : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k d) 1).re =
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialIncidentSynthesis k N (fun i => d i * radialCompletedSlope k i))).re := by
  rw [storage_re_eq_source_cross k _ 1 hP,
    sourceValue_eq_completedCoefficients,
    sourceCompanion_eq_completedSlope k N _ hF,
    radialCompletedValueCoefficients_input k N d hF hP, inner_smul_right]
  simp [Complex.mul_im]

/-- All-order exact frontier on the genuine boundary cancellation sector:
EVERY retained source contribution is in the exact higher vector remainder.
This identity gives no sign to that remainder. -/
theorem storage_one_boundary_cancellation_eq_odd_source_remainder
    (k N r : ℕ) (d : Fin N → ℂ) (hd : d ∈ radialBoundaryJetKernel N r)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k d) 1).re =
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedOddSourceRemainderSynthesis k N r d)).re := by
  rw [storage_one_eq_complete_slope_pairing k N d hF hP,
    radialCompletedSlopeSynthesis_eq_oddJets_add_remainder k N r d, inner_add_right,
    Complex.add_re, radialCompletedOddSourceJet_energy_eq_zero_of_cancellation k N r d hd,
    zero_add]

/-- Canonical three-sample cancellation belongs to the new second sector. -/
theorem secondDifference_mem_radialBoundaryJetKernel :
    (![1, -2, 1] : Fin 3 → ℂ) ∈ radialBoundaryJetKernel 3 2 := by
  rw [mem_radialBoundaryJetKernel]
  intro m hm
  have h := radialEulerBoundaryJet_secondDifference_zero
  interval_cases m <;> tauto


/-- The next source-independent finite-difference direction cancels the first
THREE endpoint jets, including the value/curvature jet of the cubic split. -/
theorem thirdDifference_mem_radialBoundaryJetKernel :
    (![1, -3, 3, -1] : Fin 4 → ℂ) ∈ radialBoundaryJetKernel 4 3 := by
  rw [mem_radialBoundaryJetKernel]
  intro m hm
  interval_cases m <;> norm_num [radialEulerBoundaryJet, Fin.sum_univ_succ]

/-- The three-jet cancellation is a genuine nonzero complete incident state. -/
theorem radialIncidentSynthesis_thirdDifference_ne_zero (k : ℕ) :
    radialIncidentSynthesis k 4 (![1, -3, 3, -1] : Fin 4 → ℂ) ≠ 0 := by
  intro h
  have hc : (![1, -3, 3, -1] : Fin 4 → ℂ) = 0 := by
    apply radialIncidentSynthesis_injective k 4
    simpa using h
  have h0 := congrFun hc 0
  norm_num at h0

/-- Exact four-sample native source test. It uses the original full slopes,
not a Taylor approximation, canonical moment or fitted coefficient. -/
theorem storage_one_completed_thirdDifference_eq_four_slopes (k : ℕ)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k (![1, -3, 3, -1] : Fin 4 → ℂ)) 1).re =
      ((k : ℝ) + 1) / 70 *
        (14 * (radialCompletedSlope k 0).re - 14 * (radialCompletedSlope k 1).re +
          6 * (radialCompletedSlope k 2).re - (radialCompletedSlope k 3).re) := by
  rw [storage_one_eq_complete_slope_pairing k 4 _ hF hP]
  have hi : inner ℂ (radialIncidentSynthesis k 4 ![1, -3, 3, -1])
      (radialIncidentSynthesis k 4 (fun i => (![1, -3, 3, -1] : Fin 4 → ℂ) i *
        radialCompletedSlope k i)) =
      ((((k : ℝ) + 1) / 280 : ℝ) : ℂ) *
        (14 * radialCompletedSlope k 0 - 14 * radialCompletedSlope k 1 +
          6 * radialCompletedSlope k 2 - radialCompletedSlope k 3) := by
    simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul, one_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_completedNativeRadialChiralCauchyState]
    push_cast
    norm_num [map_ofNat]
    ring
  rw [hi]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.sub_re]
  norm_num
  ring

end
end CarrySelfAdjointOperator.ChiralReturn

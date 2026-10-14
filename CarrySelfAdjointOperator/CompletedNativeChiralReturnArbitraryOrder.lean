import CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport

/-!
# Fixed-order extension from the original boundary margin

Zero padding preserves both complete syntheses and the original storage.
At each fixed order, the existing whole-source remainder estimate transfers a
strict boundary margin to the actual return. The resulting positive energy
ports realize the native kernel and all its finite jet pairings.

The boundary margin is an explicit hypothesis, not an all-order certificate.
All cutoffs are chosen after the dimension. No global vector limit or uniform
cutoff in the dimension is asserted.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Continuity of the original finite boundary form, including every ordered
coefficient cross. No replacement positive form is introduced. -/
theorem nativeSourceFiniteBoundaryEnergy_continuous (N : ℕ) :
    Continuous (nativeSourceFiniteBoundaryEnergy N) := by
  have he : nativeSourceFiniteBoundaryEnergy N = fun x : Fin N → ℂ =>
      ∑ a : Fin N, ∑ b : Fin N,
        if Even (a.val+b.val) then
          2 * (-1 : ℝ)^((a.val+b.val)/2+a.val) *
            nativeSourceOddBoundaryCoefficient ((a.val+b.val)/2) *
            (conj (x a)*x b).re else 0 := by
    funext x
    exact nativeSourceFiniteBoundaryEnergy_eq_coefficient_sum N x
  rw [he]
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  split_ifs <;> fun_prop

/-- At each fixed finite dimension, strict positivity of the ACTUAL boundary
form is equivalent to a margin. Compactness chooses the margin after N and
before the source direction. This does not prove the positivity premise. -/
theorem nativeSourceFiniteBoundaryEnergy_pos_iff_margin (N : ℕ) :
    (∀ x : Fin N → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy N x) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin N → ℂ,
        ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy N x := by
  constructor
  · intro hp
    obtain ⟨ε, hε, hu⟩ := (isCompact_sphere (0 : Fin N → ℂ) 1).exists_forall_le'
      (nativeSourceFiniteBoundaryEnergy_continuous N).continuousOn (a := (0 : ℝ)) (by
        intro x hx
        have hn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
        exact hp x (by intro hx; simp [hx] at hn))
    refine ⟨ε, hε, ?_⟩
    intro x
    by_cases hx : x = 0
    · subst x
      simp [nativeSourceFiniteBoundaryEnergy]
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      let y : Fin N → ℂ := (‖x‖⁻¹ : ℝ) • x
      have hy : ‖y‖ = 1 := by
        simp [y, norm_smul, norm_inv, inv_mul_cancel₀ hn]
      have hxy : (‖x‖ : ℂ) • y = x := by
        funext i
        simp only [y, Pi.smul_apply, smul_eq_mul, Complex.real_smul, ← mul_assoc]
        norm_cast
        simp [hn]
      have hb := hu y (by simpa only [Metric.mem_sphere, dist_zero_right] using hy)
      have he := nativeSourceFiniteBoundaryEnergy_smul N (‖x‖ : ℂ) y
      rw [hxy, Complex.normSq_ofReal] at he
      rw [he]
      nlinarith [sq_nonneg ‖x‖]
  · rintro ⟨ε, hε, hb⟩ x hx
    exact lt_of_lt_of_le (mul_pos hε (sq_pos_of_pos (norm_pos_iff.mpr hx))) (hb x)

/-- Include an original source prefix, adding zero coefficients only. -/
def radialSourcePad {N M : ℕ} (h : N ≤ M) (c : Fin N → ℂ) : Fin M → ℂ :=
  ∑ i : Fin N, Pi.single (Fin.castLE h i) (c i)

/-- Padding preserves the entire incident vector before any readout. -/
theorem radialIncidentSynthesis_pad (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (c : Fin N → ℂ) :
    radialIncidentSynthesis k M (radialSourcePad h c) = radialIncidentSynthesis k N c := by
  classical
  rw [radialSourcePad, map_sum]
  simp [radialIncidentSynthesis]

/-- Padding also preserves the complete return, with the same amplitudes. -/
theorem radialReturnedSynthesis_pad (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (c : Fin N → ℂ) :
    radialReturnedSynthesis k M (radialSourcePad h c) = radialReturnedSynthesis k N c := by
  classical
  rw [radialSourcePad, map_sum]
  simp [radialReturnedSynthesis]

/-- No cross term or correction is lost by including a shorter prefix. -/
theorem storage_one_radialSourcePad (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (c : Fin N → ℂ) :
    (storage k (radialSourcePad h c) 1).re = (storage k c 1).re := by
  simp only [storage_one_eq_finiteTransfer_energy, radialIncidentVector_norm,
    radialReturnTransfer_exact, radialIncidentSynthesis_pad, radialReturnedSynthesis_pad]

/-- Contractivity descends to every original source prefix. -/
theorem radialReturnTransfer_norm_le_one_of_prefix (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k M‖ ≤ 1) : ‖radialReturnTransfer k N‖ ≤ 1 := by
  apply (radialReturnTransfer_norm_le_one_iff_storage k N).mpr
  intro c
  have hc := (radialReturnTransfer_norm_le_one_iff_storage k M).mp hM (radialSourcePad h c)
  rwa [storage_one_radialSourcePad] at hc

/-- The existing unconditional seven-source result includes every shorter
original prefix, with a cutoff still allowed to depend on N. -/
theorem radialReturnTransfer_eventually_norm_le_one_of_le_seven (N : ℕ) (hN : N ≤ 7) :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  filter_upwards [radialReturnTransfer_seven_eventually_norm_le_one] with k hk
  exact radialReturnTransfer_norm_le_one_of_prefix k hN hk

/-- Every fixed even dimension: the actual storage inherits half the boundary
margin, with the existing factor two in the source energy identity retained. -/
theorem storage_one_chiralJetInput_eventually_margin (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hboundary : ∀ x : Fin (2*n) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      (ε/4) * ‖x‖^2 ≤ (storage k (nativeSourceChiralJetInput n k x) 1).re := by
  filter_upwards [storage_one_chiralJetInput_eventually_energy_control n (ε/2)
    (by positivity)] with k hk
  intro x
  have hb := hboundary x
  have he := (abs_le.mp (hk x)).1
  nlinarith

/-- The geometric jet chart covers every original coefficient vector, so a
boundary margin proves strict storage for ALL nonzero inputs, not just jets. -/
theorem storage_one_even_eventually_pos_of_boundary_margin (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hboundary : ∀ x : Fin (2*n) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ᶠ k : ℕ in atTop, ∀ c : Fin (2*n) → ℂ, c ≠ 0 → 0 < (storage k c 1).re := by
  filter_upwards [nativeSourceChiralJetInput_eventually_bijective n,
    storage_one_chiralJetInput_eventually_margin n ε hε hboundary] with k hbij hk
  intro c hc
  obtain ⟨x, rfl⟩ := hbij.2 c
  have hx : x ≠ 0 := by
    intro hx
    exact hc (hx ▸ map_zero (nativeSourceChiralJetInput n k))
  exact lt_of_lt_of_le (mul_pos (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr hx))) (hk x)

/-- Boundary coercivity suffices for contractivity of the SAME finite return. -/
theorem radialReturnTransfer_even_eventually_norm_le_one_of_boundary_margin
    (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hboundary : ∀ x : Fin (2*n) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (2*n)‖ ≤ 1 := by
  filter_upwards [storage_one_even_eventually_pos_of_boundary_margin n ε hε hboundary] with k hk
  apply (radialReturnTransfer_norm_le_one_iff_storage k (2*n)).mpr
  intro c
  by_cases hc : c = 0
  · subst c
    simp [storage_one_eq_finiteTransfer_energy, radialReturnTransfer_exact]
  · exact (hk c hc).le

/-- Arbitrary finite N, including odd N: use its original prefix in 2N.
The assumed margin concerns the native source boundary form, not a fitted Gram. -/
theorem radialReturnTransfer_eventually_norm_le_one_of_boundary_margin
    (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hboundary : ∀ x : Fin (2*N) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*N) x) :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  filter_upwards [radialReturnTransfer_even_eventually_norm_le_one_of_boundary_margin
    N ε hε hboundary] with k hk
  exact radialReturnTransfer_norm_le_one_of_prefix k (by omega : N ≤ 2*N) hk

/-- Necessary sign condition: eventual source contractivity cannot hide a
negative direction of the actual boundary limit. No strict margin is inferred. -/
theorem nativeSourceFiniteBoundaryEnergy_nonneg_of_eventually_contractive (n : ℕ)
    (hcontract : ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (2*n)‖ ≤ 1)
    (x : Fin (2*n) → ℂ) : 0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
  have ht : Tendsto (fun k => 2 * (storage k (nativeSourceChiralJetInput n k x) 1).re)
      atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
    simpa only [nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage] using
      nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto n x
  apply ge_of_tendsto ht
  filter_upwards [hcontract] with k hk
  exact mul_nonneg (by norm_num)
    ((radialReturnTransfer_norm_le_one_iff_storage k (2*n)).mp hk _)

/-- A genuinely negative boundary direction rules out eventual contractivity
in that same finite dimension; no theory-wide impossibility is inferred. -/
theorem not_eventually_contractive_of_negative_boundary_direction (n : ℕ)
    (x : Fin (2*n) → ℂ) (hx : nativeSourceFiniteBoundaryEnergy (2*n) x < 0) :
    ¬ (∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (2*n)‖ ≤ 1) := by
  intro hc
  exact (not_lt_of_ge (nativeSourceFiniteBoundaryEnergy_nonneg_of_eventually_contractive
    n hc x)) hx

/-- Exact two-variable native kernel for each fixed N, once its explicit
source boundary margin is proved. Regularity is supplied by the original source. -/
theorem radialReturnSampleEnergyPort_eventually_kernel_of_boundary_margin
    (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hboundary : ∀ x : Fin (2*N) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*N) x) :
    ∀ᶠ k : ℕ in atTop, ∀ i j : Fin N,
      inner ℂ (radialReturnSampleEnergyPort k N i) (radialReturnSampleEnergyPort k N j) =
        canonicalCompletedNativeRadialDslopeSampleMatrix k N i j := by
  filter_upwards [radialReturnTransfer_eventually_norm_le_one_of_boundary_margin N ε hε hboundary,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk hreg
  intro i j
  exact radialReturnSampleEnergyPort_inner k N hk hreg i j

/-- All independent jet pairings at arbitrary fixed order. This is convergence
of the full Gram block; no convergence of the energy vectors is asserted. -/
theorem radialReturnEnergyJet_inner_tendsto_of_boundary_margin
    (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hboundary : ∀ x : Fin (2*N) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*N) x) (a b : Fin N) :
    Tendsto (fun k => inner ℂ (radialReturnEnergyJet k N a) (radialReturnEnergyJet k N b))
      atTop (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment a.val b.val)) := by
  exact radialReturnEnergyJet_inner_tendsto_of_eventually_contractive N
    (radialReturnTransfer_eventually_norm_le_one_of_boundary_margin N ε hε hboundary) a b

/-- The family statement has the original quantifiers: for every N its own
eventual cutoff. The unresolved boundary-margin family stays an explicit premise. -/
theorem radialReturnTransfer_all_orders_of_boundary_margins
    (hboundary : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin (2*n) → ℂ,
      ε * ‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  intro N
  obtain ⟨ε, hε, hb⟩ := hboundary N
  exact radialReturnTransfer_eventually_norm_le_one_of_boundary_margin N ε hε hb

/-- All finite orders follow from strict positivity of the existing boundary
forms. The premise is precisely a sign obligation, not an analytic tail bound. -/
theorem radialReturnTransfer_all_orders_of_strict_boundary_positivity
    (hboundary : ∀ n : ℕ, ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  apply radialReturnTransfer_all_orders_of_boundary_margins
  intro n
  exact (nativeSourceFiniteBoundaryEnergy_pos_iff_margin (2*n)).mp (hboundary n)

end
end CarrySelfAdjointOperator.ChiralReturn

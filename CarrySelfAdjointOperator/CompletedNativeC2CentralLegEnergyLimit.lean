import CarrySelfAdjointOperator.CompletedNativeC2LegEnvelopeTransport
import CarrySelfAdjointOperator.CompletedNativeC2ExactTailConvergence
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import CarrySelfAdjointOperator.CompletedNativeChiralReturnArbitraryOrder

/-!
# Quantitative radial transport from the exact C2 carrier to boundary energy

For each fixed order the original C2 central-plus-legs readout, at the exact
diagonal cutoff already selected for its tail, converges uniformly in the
input vector to one eighth of the original finite boundary energy. The
radial variable is kept distinct from both the Hankel order and C2 cutoff.
-/

namespace CarrySelfAdjointOperator

open Filter Topology
open ChiralReturn
open CPFormal.Analytic.Cp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The finite C2 readout differs from minus the complete Gamma correction
gap by at most the exact omitted-tail budget, uniformly in the source vector.
The selected cutoff is the one from the exact-tail convergence theorem. -/
theorem nativeSourceC2CentralLeg_gamma_gap_error (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |nativeSourceGammaCorrectionGap n k x +
        2 * nativeSourceC2CentralLegReadout n k
          (nativeSourceC2TailCutoff n k) x| ≤
        nativeSourceC2TailBudget k * ‖x‖^2 := by
  filter_upwards [nativeSourceC2TailError_eventually_bounded_by_budget n,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)]
    with k htail hregular
  intro x
  have hstrip : ∀ i : Fin (2*n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip :=
    fun i => (hregular i).1
  have hpositive : ∀ i : Fin (2*n),
      completedNativePositiveHermiteBiehlerCoordinate
        (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 :=
    fun i => (hregular i).2.2
  have herr := nativeSourceC2GammaGap_approx_error_bound n k
    (nativeSourceC2TailCutoff n k) x hstrip hpositive
  rw [nativeSourceC2ApproxDefect_eq_centralLegReadout] at herr
  have habs := abs_le.mp herr
  have ht := htail x
  have hup : nativeSourceGammaCorrectionGap n k x +
      2 * nativeSourceC2CentralLegReadout n k
        (nativeSourceC2TailCutoff n k) x ≤
      nativeSourceC2TailBudget k * ‖x‖^2 := by
    nlinarith [habs.2, ht]
  have hlow : -(nativeSourceC2TailBudget k * ‖x‖^2) ≤
      nativeSourceGammaCorrectionGap n k x +
        2 * nativeSourceC2CentralLegReadout n k
          (nativeSourceC2TailCutoff n k) x := by
    nlinarith [habs.1, ht]
  exact abs_le.mpr ⟨hlow, hup⟩

/-- Exact quantitative compensation identity, with the original factors and
the diagonal C2 tail budget `1/(k+1)`. -/
theorem nativeSourceC2CentralLeg_energy_error_bound
    (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |8 * nativeSourceC2CentralLegReadout n k
            (nativeSourceC2TailCutoff n k) x -
        nativeSourceFiniteBoundaryEnergy (2*n) x| ≤
        (η + 4 / ((k : ℝ) + 1)) * ‖x‖^2 := by
  have hraw := rawGamma_chiralJetInput_eventually_energy_control n η hη
  have hgap := nativeSourceC2CentralLeg_gamma_gap_error n
  filter_upwards [hraw, hgap] with k hraw hk
  intro x
  let G := nativeSourceGammaCorrectionGap n k x
  let Q := nativeSourceC2CentralLegReadout n k
    (nativeSourceC2TailCutoff n k) x
  let E := nativeSourceFiniteBoundaryEnergy (2*n) x
  have hgapx : |G + 2*Q| ≤ nativeSourceC2TailBudget k * ‖x‖^2 := by
    simpa [G, Q] using hk x
  have henergy : |-4*G-E| ≤ η*‖x‖^2 := by
    have hx := hraw x
    dsimp only at hx
    have heq : -4*G-E =
        4*(‖gammaSourceSynthesis k (nativeSourceChiralJetInput n k x) 1‖^2 -
          (rawGammaWronskianBalance k (nativeSourceChiralJetInput n k x)
            (nativeSourceChiralJetInput n k x) 1 1).im) -
          nativeSourceFiniteBoundaryEnergy (2*n) x := by
      dsimp [G, nativeSourceGammaCorrectionGap]
      ring
    rw [heq]
    simpa [E] using hx
  have hsum : |8*Q-E| ≤
      (η + 4*nativeSourceC2TailBudget k) * ‖x‖^2 := by
    calc
      |8*Q-E| = |(-4*G-E) + 4*(G+2*Q)| := by congr 1; ring
      _ ≤ |-4*G-E| + |4*(G+2*Q)| := abs_add_le _ _
      _ ≤ η*‖x‖^2 + 4*(nativeSourceC2TailBudget k*‖x‖^2) := by
        apply add_le_add henergy
        calc
          |4*(G+2*Q)| = 4*|G+2*Q| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
          _ ≤ 4*(nativeSourceC2TailBudget k*‖x‖^2) :=
            mul_le_mul_of_nonneg_left hgapx (by norm_num)
      _ = (η + 4*nativeSourceC2TailBudget k)*‖x‖^2 := by ring
  have hbudget : nativeSourceC2TailBudget k = 1 / ((k:ℝ)+1) := rfl
  change |8*Q-E| ≤
      (η + 4 / ((k:ℝ)+1))*‖x‖^2
  rw [hbudget] at hsum
  calc
    |8*Q-E| ≤ (η + 4*(1 / ((k:ℝ)+1)))*‖x‖^2 := hsum
    _ = (η + 4 / ((k:ℝ)+1))*‖x‖^2 := by congr 1; ring

/-- Uniform-on-the-unit-ball form of the radial limit. Equivalently, the
estimate below holds for every input with the homogeneous factor `‖x‖²`.
The order n is fixed; no uniformity in n or in the transverse boundary limit
is asserted. -/
theorem nativeSourceC2CentralLeg_energy_eventually_uniform
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |nativeSourceC2CentralLegReadout n k
          (nativeSourceC2TailCutoff n k) x -
        nativeSourceFiniteBoundaryEnergy (2*n) x / 8| ≤ ε*‖x‖^2 := by
  have henergy := nativeSourceC2CentralLeg_energy_error_bound n (4*ε)
    (by positivity)
  have hbudget := nativeSourceC2TailBudget_tendsto_zero.eventually
    (Iio_mem_nhds hε)
  filter_upwards [henergy, hbudget] with k hk hb
  intro x
  have hx := hk x
  have hcoef : 4*ε + 4 / ((k:ℝ)+1) ≤ 8*ε := by
    have hb' : 1 / ((k:ℝ)+1) ≤ ε := by
      simpa [nativeSourceC2TailBudget] using hb.le
    calc
      4*ε + 4 / ((k:ℝ)+1) = 4*ε + 4*(1 / ((k:ℝ)+1)) := by ring
      _ = 4*(1 / ((k:ℝ)+1)) + 4*ε := by ring
      _ ≤ 4*ε + 4*ε := by
        have hmul := mul_le_mul_of_nonneg_left hb'
          (by norm_num : (0:ℝ) ≤ 4)
        nlinarith
      _ = 8*ε := by ring
  have hnorm : 0 ≤ ‖x‖^2 := sq_nonneg ‖x‖
  have heq :
      nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x -
        nativeSourceFiniteBoundaryEnergy (2*n) x / 8 =
      (8*nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x -
        nativeSourceFiniteBoundaryEnergy (2*n) x) / 8 := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
  have hdiv := div_le_div_of_nonneg_right hx (by norm_num : (0:ℝ) ≤ 8)
  have hfactor :
      (4*ε + 4 / ((k:ℝ)+1))*‖x‖^2 ≤ 8*ε*‖x‖^2 :=
    mul_le_mul_of_nonneg_right hcoef hnorm
  have hfactor_div := div_le_div_of_nonneg_right hfactor
    (by norm_num : (0:ℝ) ≤ 8)
  exact hdiv.trans (by nlinarith)

/-- Any strict margin for the original finite boundary energy transfers to a
uniform eventual margin for the exact-cutoff C2 central-plus-legs readout.
This is the interface used downstream by finite source certificates; it
does not assume or manufacture the boundary-energy sign. -/
theorem nativeSourceC2CentralLeg_eventually_margin_of_boundary_margin
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hboundary : ∀ x : Fin (2*n) → ℂ,
      δ*‖x‖^2 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      (δ/16)*‖x‖^2 ≤ nativeSourceC2CentralLegReadout n k
        (nativeSourceC2TailCutoff n k) x := by
  have herr := nativeSourceC2CentralLeg_energy_error_bound n (δ/4) (by positivity)
  have hbudget := nativeSourceC2TailBudget_tendsto_zero.eventually
    (Iio_mem_nhds (by positivity : (0:ℝ) < δ/16))
  filter_upwards [herr, hbudget] with k hk hb
  intro x
  have happrox := hk x
  have herror :
      |8*nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x -
        nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ (δ/2)*‖x‖^2 := by
    have hb' : nativeSourceC2TailBudget k ≤ δ/16 := hb.le
    have hcoeff : δ/4 + 4*nativeSourceC2TailBudget k ≤ δ/2 := by linarith
    have hnorm : 0 ≤ ‖x‖^2 := sq_nonneg ‖x‖
    have hfactor := mul_le_mul_of_nonneg_right hcoeff hnorm
    have happrox' := happrox
    have hbudget_eq : nativeSourceC2TailBudget k = 1/((k:ℝ)+1) := rfl
    rw [hbudget_eq] at hfactor
    have hfactor' :
        (δ/4 + 4/((k:ℝ)+1))*‖x‖^2 ≤ (δ/2)*‖x‖^2 := by
      calc
        (δ/4 + 4/((k:ℝ)+1))*‖x‖^2 =
            (δ/4 + 4*(1/((k:ℝ)+1)))*‖x‖^2 := by congr 1; ring
        _ ≤ (δ/2)*‖x‖^2 := hfactor
    exact happrox'.trans hfactor'
  have hlow := (abs_le.mp herror).1
  have henergy := hboundary x
  have hscaled : (δ/2)*‖x‖^2 ≤
      8*nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x := by
    nlinarith
  have hscaled' := div_le_div_of_nonneg_right hscaled
    (by norm_num : (0:ℝ) ≤ 8)
  nlinarith

/-- Strict positivity of the original finite boundary form is sufficient to
obtain a uniform eventual positive margin for the exact-cutoff C2 readout.
The boundary positivity remains an explicit premise. -/
theorem nativeSourceC2CentralLeg_eventually_margin_of_boundary_pos
    (n : ℕ)
    (hpositive : ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
        (δ/16)*‖x‖^2 ≤ nativeSourceC2CentralLegReadout n k
          (nativeSourceC2TailCutoff n k) x := by
  obtain ⟨δ, hδ, hmargin⟩ :=
    (nativeSourceFiniteBoundaryEnergy_pos_iff_margin (2*n)).mp hpositive
  exact ⟨δ, hδ,
    nativeSourceC2CentralLeg_eventually_margin_of_boundary_margin n δ hδ hmargin⟩

end
end CarrySelfAdjointOperator

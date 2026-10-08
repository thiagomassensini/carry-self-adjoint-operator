import CarrySelfAdjointOperator.CompletedNativeChiralReturnGammaCorrectionCancellation
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCancellation

/-!
# First surviving Green boundary pairing in every cancellation sector

The two source families are synthesized in the original Cauchy carrier.
Boundary cancellations remove only terms certified zero by the existing
Green identity. The first surviving cross and the full higher source remainder
are retained. No source sign or moment kernel is assumed.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Different cancellation depths retain one exact polarized boundary cross
at their first observable degree. This is an identity, not a sign assertion. -/
theorem radialEulerPower_firstSurviving_boundary
    (k N r s : ℕ) (d e : Fin N → ℂ)
    (hd : d ∈ radialBoundaryJetKernel N r)
    (he : e ∈ radialBoundaryJetKernel N s) :
    inner ℂ (radialIncidentSynthesis k N d)
        (radialEulerPowerSynthesis k N (r+s+1) e) -
      (-1 : ℂ)^(r+s+1) * inner ℂ
        (radialEulerPowerSynthesis k N (r+s+1) d)
        (radialIncidentSynthesis k N e) =
      (((k : ℝ)+1 : ℝ) : ℂ) * (-1 : ℂ)^r *
        conj (radialEulerBoundaryJet d r) * radialEulerBoundaryJet e s := by
  rw [← radialEulerPowerSynthesis_zero k N d,
    ← radialEulerPowerSynthesis_zero k N e,
    radialEulerPower_green_boundary]
  have hs : (∑ a ∈ Finset.range (r+s+1), (-1 : ℂ)^a *
      conj (radialEulerBoundaryJet d a) *
        radialEulerBoundaryJet e (r+s+1-1-a)) =
      (-1 : ℂ)^r * conj (radialEulerBoundaryJet d r) *
        radialEulerBoundaryJet e s := by
    rw [Finset.sum_eq_single r]
    · congr 2
      omega
    · intro a ha har
      by_cases hlt : a < r
      · rw [(mem_radialBoundaryJetKernel N r d).mp hd a hlt]
        simp
      · have htail : r+s+1-1-a < s := by
          have ha' := Finset.mem_range.mp ha
          omega
        rw [(mem_radialBoundaryJetKernel N s e).mp he _ htail]
        simp
    · intro hr
      exact False.elim (hr (Finset.mem_range.mpr (by omega)))
  rw [hs]
  ring

/-- On one cancellation sector, the first surviving Hermitian Euler energy
is a single boundary square, with its geometric alternating sign explicit. -/
theorem radialEulerPower_firstSurviving_energy
    (k N r : ℕ) (d : Fin N → ℂ) (hd : d ∈ radialBoundaryJetKernel N r) :
    (inner ℂ (radialIncidentSynthesis k N d)
      (radialEulerPowerSynthesis k N (2*r+1) d)).re =
      ((k : ℝ)+1)/2 * (-1 : ℝ)^r * Complex.normSq (radialEulerBoundaryJet d r) := by
  have h := radialEulerPower_firstSurviving_boundary k N r r d d hd hd
  rw [show r+r+1 = 2*r+1 by omega, Odd.neg_one_pow (show Odd (2*r+1) from ⟨r, by omega⟩)] at h
  rw [show (((k : ℝ)+1 : ℝ) : ℂ) * (-1 : ℂ)^r *
      conj (radialEulerBoundaryJet d r) * radialEulerBoundaryJet d r =
      (((k : ℝ)+1 : ℝ) : ℂ) * (-1 : ℂ)^r *
        (Complex.normSq (radialEulerBoundaryJet d r) : ℂ) by
    rw [Complex.normSq_eq_conj_mul_self]; ring] at h
  have hr := congrArg Complex.re h
  have hc := congrArg Complex.re (inner_conj_symm
    (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N (2*r+1) d))
  simp only [Complex.conj_re] at hc
  have hp : (-1 : ℂ)^r = (((-1 : ℝ)^r : ℝ) : ℂ) := by push_cast; rfl
  rw [hp] at hr
  simp only [neg_one_mul, sub_neg_eq_add, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hr
  linarith

/-- Incrementing the existing source jet tower exposes one source-derived
coefficient. The exact higher vector remainder is unchanged by approximation. -/
theorem radialCompletedOddSourceRemainder_step (k N r : ℕ) (d : Fin N → ℂ) :
    radialCompletedOddSourceRemainderSynthesis k N r d =
      (radialCompletedOddSourceJetScale k r : ℂ) •
        radialEulerPowerSynthesis k N (2*r+1) d +
      radialCompletedOddSourceRemainderSynthesis k N (r+1) d := by
  unfold radialCompletedOddSourceRemainderSynthesis radialCompletedOddSourceJetSynthesis
  rw [Finset.sum_range_succ]
  abel

/-- Actual completed storage after r boundary cancellations: first surviving
boundary square PLUS the full higher source readout, before any estimate. -/
theorem storage_one_cancellation_eq_firstBoundary_add_higher
    (k N r : ℕ) (d : Fin N → ℂ) (hd : d ∈ radialBoundaryJetKernel N r)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k d) 1).re =
      2 * ((k : ℝ)+1) * (-1 : ℝ)^r * radialCompletedOddSourceJetScale k r *
        Complex.normSq (radialEulerBoundaryJet d r) +
      4 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedOddSourceRemainderSynthesis k N (r+1) d)).re := by
  rw [storage_one_boundary_cancellation_eq_odd_source_remainder k N r d hd hF hP,
    radialCompletedOddSourceRemainder_step, inner_add_right, inner_smul_right,
    Complex.add_re, Complex.re_ofReal_mul,
    radialEulerPower_firstSurviving_energy k N r d hd]
  ring

/-- The same arbitrary-order Gamma correction gap now has a first surviving
boundary term and ONE exact higher source remainder; all crosses remain. -/
theorem rawGammaCorrection_cancellation_gap_eq_firstBoundary_add_higher
    (k N r : ℕ) (d : Fin N → ℂ) (hd : d ∈ radialBoundaryJetKernel N r)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    let c := radialCompletedInputCoefficients k d
    ‖gammaSourceSynthesis k c 1‖^2 - (rawGammaWronskianBalance k c c 1 1).im =
      ((k : ℝ)+1) * (-1 : ℝ)^r * radialCompletedOddSourceJetScale k r *
        Complex.normSq (radialEulerBoundaryJet d r) +
      2 * (inner ℂ (radialIncidentSynthesis k N d)
        (radialCompletedOddSourceRemainderSynthesis k N (r+1) d)).re := by
  dsimp only
  have h1 := storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k
    (radialCompletedInputCoefficients k d) 1 hstrip hP
  have h2 := storage_one_cancellation_eq_firstBoundary_add_higher k N r d hd hF hP
  linarith

/-- The estimate controls the retained higher vector term without assigning
it a sign. A positive first coefficient alone cannot replace this term. -/
theorem rawGammaCorrection_cancellation_higher_abs_bound
    (k N r : ℕ) (d : Fin N → ℂ) (hd : d ∈ radialBoundaryJetKernel N r)
    (hstrip : ∀ i : Fin N, operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    let c := radialCompletedInputCoefficients k d
    |‖gammaSourceSynthesis k c 1‖^2 - (rawGammaWronskianBalance k c c 1 1).im -
      ((k : ℝ)+1) * (-1 : ℝ)^r * radialCompletedOddSourceJetScale k r *
        Complex.normSq (radialEulerBoundaryJet d r)| ≤
      2 * ‖radialIncidentSynthesis k N d‖ *
        ‖radialCompletedOddSourceRemainderSynthesis k N (r+1) d‖ := by
  dsimp only
  rw [rawGammaCorrection_cancellation_gap_eq_firstBoundary_add_higher k N r d hd hstrip hF hP]
  simp only [add_sub_cancel_left, abs_mul]
  norm_num only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have h := (Complex.abs_re_le_norm (inner ℂ (radialIncidentSynthesis k N d)
    (radialCompletedOddSourceRemainderSynthesis k N (r+1) d))).trans
      (norm_inner_le_norm _ _)
  nlinarith

/-- For each finite source size, one threshold controls EVERY cancellation
depth and coefficient vector. No sign or remainder rate is added. -/
theorem rawGammaCorrection_cancellation_eventually_complete (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, ∀ d : Fin N → ℂ,
      d ∈ radialBoundaryJetKernel N r →
      let c := radialCompletedInputCoefficients k d
      ‖gammaSourceSynthesis k c 1‖^2 - (rawGammaWronskianBalance k c c 1 1).im =
        ((k : ℝ)+1) * (-1 : ℝ)^r * radialCompletedOddSourceJetScale k r *
          Complex.normSq (radialEulerBoundaryJet d r) +
        2 * (inner ℂ (radialIncidentSynthesis k N d)
          (radialCompletedOddSourceRemainderSynthesis k N (r+1) d)).re := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hreg
  intro r d hd
  exact rawGammaCorrection_cancellation_gap_eq_firstBoundary_add_higher k N r d hd
    (fun i => (hreg i).1) (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)

/-- A source-independent six-step difference on the original seven nodes.
It is a diagnostic direction, not a target-fitted moment vector. -/
def sixthDifference : Fin 7 → ℂ := ![1, -6, 15, -20, 15, -6, 1]

theorem sixthDifference_mem_radialBoundaryJetKernel :
    sixthDifference ∈ radialBoundaryJetKernel 7 6 := by
  rw [mem_radialBoundaryJetKernel]
  intro m hm
  interval_cases m <;> norm_num [sixthDifference, radialEulerBoundaryJet, Fin.sum_univ_succ]

theorem sixthDifference_first_boundary : radialEulerBoundaryJet sixthDifference 6 = 720 := by
  norm_num [sixthDifference, radialEulerBoundaryJet, Fin.sum_univ_succ]

/-- The new diagnostic retains a nonzero COMPLETE incident state despite
the vanishing of every previously certified boundary coordinate. -/
theorem radialIncidentSynthesis_sixthDifference_ne_zero (k : ℕ) :
    radialIncidentSynthesis k 7 sixthDifference ≠ 0 := by
  intro h
  have hd : sixthDifference = 0 := by
    apply radialIncidentSynthesis_injective k 7
    simpa using h
  have h0 := congrFun hd 0
  norm_num [sixthDifference] at h0

/-- Exact seven-sample canary: the first observable source degree is thirteen.
The full higher synthesis, including completion/tail, is NOT dropped. -/
theorem storage_one_sixthDifference_eq_thirteenth_add_higher
    (k : ℕ)
    (hF : ∀ i : Fin 7, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin 7, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k sixthDifference) 1).re =
      1036800 * ((k : ℝ)+1) * radialCompletedOddSourceJetScale k 6 +
      4 * (inner ℂ (radialIncidentSynthesis k 7 sixthDifference)
        (radialCompletedOddSourceRemainderSynthesis k 7 7 sixthDifference)).re := by
  rw [storage_one_cancellation_eq_firstBoundary_add_higher k 7 6 sixthDifference
    sixthDifference_mem_radialBoundaryJetKernel hF hP, sixthDifference_first_boundary]
  norm_num [Complex.normSq_apply]
  ring

/-- The same canary directly in the FULL nonlinear source slopes. The seven
rational coefficients are forced by the old Cauchy Gram and the difference
vector, not chosen from a target readout. -/
theorem storage_one_sixthDifference_eq_seven_slopes
    (k : ℕ)
    (hF : ∀ i : Fin 7, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin 7, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k sixthDifference) 1).re =
      ((k : ℝ)+1)/6006 *
        (429*(radialCompletedSlope k 0).re - 572*(radialCompletedSlope k 1).re +
          429*(radialCompletedSlope k 2).re - 208*(radialCompletedSlope k 3).re +
          65*(radialCompletedSlope k 4).re - 12*(radialCompletedSlope k 5).re +
          (radialCompletedSlope k 6).re) := by
  rw [storage_one_eq_complete_slope_pairing k 7 sixthDifference hF hP]
  have hi : inner ℂ (radialIncidentSynthesis k 7 sixthDifference)
      (radialIncidentSynthesis k 7 (fun i => sixthDifference i * radialCompletedSlope k i)) =
      ((((k : ℝ)+1)/24024 : ℝ) : ℂ) *
        (429*radialCompletedSlope k 0 - 572*radialCompletedSlope k 1 +
          429*radialCompletedSlope k 2 - 208*radialCompletedSlope k 3 +
          65*radialCompletedSlope k 4 - 12*radialCompletedSlope k 5 + radialCompletedSlope k 6) := by
    simp only [sixthDifference, radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
      Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, one_mul, one_smul,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_completedNativeRadialChiralCauchyState]
    push_cast
    norm_num [map_ofNat]
    ring
  rw [hi]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re, Complex.sub_re]
  norm_num
  ring

/-- A single radial threshold works for the full seven-source canary, including
the exact Gamma gap. This packages no sign of either source expression. -/
theorem sixthDifference_gammaGap_eventually_eq_seven_slopes :
    ∀ᶠ k : ℕ in atTop,
      let c := radialCompletedInputCoefficients k sixthDifference
      ‖gammaSourceSynthesis k c 1‖^2 - (rawGammaWronskianBalance k c c 1 1).im =
        ((k : ℝ)+1)/12012 *
          (429*(radialCompletedSlope k 0).re - 572*(radialCompletedSlope k 1).re +
            429*(radialCompletedSlope k 2).re - 208*(radialCompletedSlope k 3).re +
            65*(radialCompletedSlope k 4).re - 12*(radialCompletedSlope k 5).re +
            (radialCompletedSlope k 6).re) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 7] with k hreg
  dsimp only
  have h1 := storage_re_eq_gammaEnergy_sub_rawGammaBalance 0 k
    (radialCompletedInputCoefficients k sixthDifference) 1
    (fun i => (hreg i).1) (fun i => (hreg i).2.2)
  have h2 := storage_one_sixthDifference_eq_seven_slopes k
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)
  linarith

end
end CarrySelfAdjointOperator.ChiralReturn

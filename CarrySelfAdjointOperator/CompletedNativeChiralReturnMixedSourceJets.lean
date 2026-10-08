import CarrySelfAdjointOperator.CompletedNativeChiralReturnSeventhSourceJet
import CarrySelfAdjointOperator.CompletedNativeSixthOrderHankelGate

/-!
# Mixed boundary source jets through order seven

Coefficients are derivatives of the existing -F'/F source, before moment
identification. The two alternating boundary blocks retain their cross terms.
This finite jet result does not replace the full radial source by a polynomial,
change the Cauchy metric, or assert positivity of the full four-sample storage.
Only the pure real polynomial certificate is used from the historical
sixth-order module; the dedicated audit traverses declaration dependencies.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Factorial-normalized odd derivative of the original completed source. -/
def nativeSourceOddBoundaryCoefficient (j : ℕ) : ℝ :=
  (iteratedDeriv (2 * j + 1) completedNativeOperatorLogDerivative 0).re /
    ((2 * j + 1).factorial : ℝ)

/-- The four coefficients come directly from the division-free source recurrence. -/
theorem nativeSourceOddBoundaryCoefficient_integral_formulas :
    let a := completedNativeXiCosineMoment 0
    let b := completedNativeXiCosineMoment 1
    let c := completedNativeXiCosineMoment 2
    let d := completedNativeXiCosineMoment 3
    let e := completedNativeXiCosineMoment 4
    nativeSourceOddBoundaryCoefficient 0 = b / a ∧
    nativeSourceOddBoundaryCoefficient 1 = (3 * b^2 - a*c) / (6*a^2) ∧
    nativeSourceOddBoundaryCoefficient 2 = (30*b^3 - 15*a*b*c + a^2*d) / (120*a^3) ∧
    nativeSourceOddBoundaryCoefficient 3 = nativeSourceSeventhNumerator a b c d e / (5040*a^4) := by
  obtain ⟨_, h1, _, h3, _, h5, _, h7⟩ := nativeSourceLogSlope_center_jets
  have r1 : iteratedDeriv 1 completedNativeOperatorLogDerivative 0 =
      (completedNativeXiCosineMoment 1 / completedNativeXiCosineMoment 0 : ℝ) := by
    rw [h1]
    push_cast
    rfl
  have r3 : iteratedDeriv 3 completedNativeOperatorLogDerivative 0 =
      ((3 * completedNativeXiCosineMoment 1^2 - completedNativeXiCosineMoment 0 *
        completedNativeXiCosineMoment 2) / completedNativeXiCosineMoment 0^2 : ℝ) := by
    rw [h3]
    push_cast
    rfl
  have r5 : iteratedDeriv 5 completedNativeOperatorLogDerivative 0 =
      ((30 * completedNativeXiCosineMoment 1^3 - 15 * completedNativeXiCosineMoment 0 *
        completedNativeXiCosineMoment 1 * completedNativeXiCosineMoment 2 +
        completedNativeXiCosineMoment 0^2 * completedNativeXiCosineMoment 3) /
          completedNativeXiCosineMoment 0^3 : ℝ) := by
    rw [h5]
    push_cast
    rfl
  have r7 := nativeSourceLogSlope_seventh_derivative_eq_positive_integralRatio
  dsimp only
  norm_num only [nativeSourceOddBoundaryCoefficient, Nat.reduceMul, Nat.reduceAdd, Nat.factorial]
  rw [r1, r3, r5, r7]
  simp only [Complex.ofReal_re]
  repeat' constructor
  all_goals ring

/-- Upstream integral margin for the first mixed block. No moment determinant
or positivity certificate is used: this invokes only a real polynomial lemma. -/
theorem nativeSourceSixthMixedNumerator_pos :
    0 < 15 * completedNativeXiCosineMoment 1 ^ 2 * completedNativeXiCosineMoment 2 +
      3 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 1 *
        completedNativeXiCosineMoment 3 -
      10 * completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 ^ 2 := by
  obtain ⟨ha0, ha1, hb0, _, hc0, hc1, hd0, _, _, _⟩ := nativeSourceCosineIntegral_refined_box
  have h := xiSixthMoment_numerator_lower_bound_of_box
    (completedNativeXiCosineMoment 0) (completedNativeXiCosineMoment 1)
    (completedNativeXiCosineMoment 2) (completedNativeXiCosineMoment 3)
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  exact lt_of_lt_of_le (by norm_num) h

/-- Exact source discriminants. These are coefficients of the alternating
Green boundary tower, not definitions from a canonical target Gram. -/
theorem nativeSourceMixedDiscriminants_integral_formulas :
    let a := completedNativeXiCosineMoment 0
    let b := completedNativeXiCosineMoment 1
    let c := completedNativeXiCosineMoment 2
    let d := completedNativeXiCosineMoment 3
    let e := completedNativeXiCosineMoment 4
    nativeSourceOddBoundaryCoefficient 0 * nativeSourceOddBoundaryCoefficient 2 -
      nativeSourceOddBoundaryCoefficient 1 ^ 2 =
        (15*b^2*c + 3*a*b*d - 10*a*c^2) / (360*a^3) ∧
    nativeSourceOddBoundaryCoefficient 1 * nativeSourceOddBoundaryCoefficient 3 -
      nativeSourceOddBoundaryCoefficient 2 ^ 2 =
        xiEighthMomentNumerator a b c d e / (302400*a^4) := by
  obtain ⟨h0, h1, h2, h3⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  dsimp only at h0 h1 h2 h3 ⊢
  rw [h0, h1, h2, h3]
  have ha := (completedNativeXiCosineMoment_pos 0).ne'
  constructor
  · field_simp [ha]
    ring
  · unfold nativeSourceSeventhNumerator xiEighthMomentNumerator
    field_simp [ha]
    ring

/-- Both mixed-block determinants are strictly positive by source integral
certificates, independently of any moment positivity premise. -/
theorem nativeSourceMixedDiscriminants_pos :
    0 < nativeSourceOddBoundaryCoefficient 0 * nativeSourceOddBoundaryCoefficient 2 -
      nativeSourceOddBoundaryCoefficient 1 ^ 2 ∧
    0 < nativeSourceOddBoundaryCoefficient 1 * nativeSourceOddBoundaryCoefficient 3 -
      nativeSourceOddBoundaryCoefficient 2 ^ 2 := by
  obtain ⟨hE, hO⟩ := nativeSourceMixedDiscriminants_integral_formulas
  rw [hE, hO]
  have ha := completedNativeXiCosineMoment_pos 0
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1, he0, he1⟩ :=
    nativeSourceCosineIntegral_refined_box
  have hp := xiEighthMoment_numerator_lower_bound_of_refined_box _ _ _ _ _
    ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 he0 he1
  exact ⟨div_pos nativeSourceSixthMixedNumerator_pos (by positivity),
    div_pos (lt_of_lt_of_le (by norm_num) hp) (by positivity)⟩

/-- The leading entries have their own independent source sign. -/
theorem nativeSourceMixedLeadingCoefficients_pos :
    0 < nativeSourceOddBoundaryCoefficient 0 ∧
      0 < nativeSourceOddBoundaryCoefficient 1 := by
  obtain ⟨h0, h1, _, _⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  rw [h0, h1]
  have ha := completedNativeXiCosineMoment_pos 0
  exact ⟨div_pos (completedNativeXiCosineMoment_pos 1) (completedNativeXiCosineMoment_pos 0),
    div_pos (by linarith [completedNativeXiCosineMoment_strict_kurtosis]) (by positivity)⟩

/-- Square completion in the existing complex norm, with the cross term
retained exactly. No metric or vector is fitted to this scalar expression. -/
theorem nativeSourceMixedBoundary_square (a b c : ℝ) (ha : a ≠ 0) (u v : ℂ) :
    a * Complex.normSq u - 2*b*(conj u*v).re + c*Complex.normSq v =
      a * Complex.normSq (u - ((b/a : ℝ) : ℂ)*v) +
        ((a*c-b^2)/a) * Complex.normSq v := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im, zero_mul, add_zero, sub_zero]
  field_simp [ha]
  ring

private theorem mixedBoundary_pos (a b c : ℝ) (ha : 0 < a) (hd : 0 < a*c-b^2)
    (u v : ℂ) (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < a * Complex.normSq u - 2*b*(conj u*v).re + c*Complex.normSq v := by
  rw [nativeSourceMixedBoundary_square a b c ha.ne']
  by_cases hv : v = 0
  · have hu : u ≠ 0 := huv.resolve_right (not_ne_iff.mpr hv)
    simpa [hv] using mul_pos ha (Complex.normSq_pos.mpr hu)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (Complex.normSq_nonneg _))
      (mul_pos (div_pos hd ha) (Complex.normSq_pos.mpr hv))

/-- Even boundary orders 0 and 2, with the exact source cross term. -/
def nativeSourceEvenBoundaryEnergy (u v : ℂ) : ℝ :=
  nativeSourceOddBoundaryCoefficient 0 * Complex.normSq u -
    2 * nativeSourceOddBoundaryCoefficient 1 * (conj u*v).re +
    nativeSourceOddBoundaryCoefficient 2 * Complex.normSq v

/-- Odd boundary orders 1 and 3, with the exact source cross term. -/
def nativeSourceOddBoundaryEnergy (u v : ℂ) : ℝ :=
  nativeSourceOddBoundaryCoefficient 1 * Complex.normSq u -
    2 * nativeSourceOddBoundaryCoefficient 2 * (conj u*v).re +
    nativeSourceOddBoundaryCoefficient 3 * Complex.normSq v

theorem nativeSourceEvenBoundaryEnergy_pos (u v : ℂ) (h : u ≠ 0 ∨ v ≠ 0) :
    0 < nativeSourceEvenBoundaryEnergy u v :=
  mixedBoundary_pos _ _ _ nativeSourceMixedLeadingCoefficients_pos.1
    nativeSourceMixedDiscriminants_pos.1 u v h

theorem nativeSourceOddBoundaryEnergy_pos (u v : ℂ) (h : u ≠ 0 ∨ v ≠ 0) :
    0 < nativeSourceOddBoundaryEnergy u v :=
  mixedBoundary_pos _ _ _ nativeSourceMixedLeadingCoefficients_pos.2
    nativeSourceMixedDiscriminants_pos.2 u v h

/-- The four-jet boundary face has both parity blocks. This is a finite
source-jet energy, NOT the storage of an arbitrary full radial source. -/
def nativeSourceFourBoundaryEnergy (x : Fin 4 → ℂ) : ℝ :=
  2 * (nativeSourceEvenBoundaryEnergy (x 0) (x 2) +
    nativeSourceOddBoundaryEnergy (x 1) (x 3))

theorem nativeSourceFourBoundaryEnergy_pos (x : Fin 4 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFourBoundaryEnergy x := by
  have he : 0 ≤ nativeSourceEvenBoundaryEnergy (x 0) (x 2) := by
    by_cases h : x 0 ≠ 0 ∨ x 2 ≠ 0
    · exact (nativeSourceEvenBoundaryEnergy_pos _ _ h).le
    · simp only [not_or, not_ne_iff] at h
      simp [nativeSourceEvenBoundaryEnergy, h.1, h.2]
  have ho : 0 ≤ nativeSourceOddBoundaryEnergy (x 1) (x 3) := by
    by_cases h : x 1 ≠ 0 ∨ x 3 ≠ 0
    · exact (nativeSourceOddBoundaryEnergy_pos _ _ h).le
    · simp only [not_or, not_ne_iff] at h
      simp [nativeSourceOddBoundaryEnergy, h.1, h.2]
  have hn : (x 0 ≠ 0 ∨ x 2 ≠ 0) ∨ (x 1 ≠ 0 ∨ x 3 ≠ 0) := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    apply hx
    funext i
    fin_cases i <;> simp [h]
  unfold nativeSourceFourBoundaryEnergy
  rcases hn with hn | hn
  · exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg
      (nativeSourceEvenBoundaryEnergy_pos _ _ hn) ho)
  · exact mul_pos (by norm_num) (add_pos_of_nonneg_of_pos he
      (nativeSourceOddBoundaryEnergy_pos _ _ hn))


/-- Zero extension only for exposing the four-coordinate face of the already
proved alternating Green boundary tower. It is not a source reconstruction. -/
def nativeSourceFourBoundaryExtension (x : Fin 4 → ℂ) (m : ℕ) : ℂ :=
  if h : m < 4 then x ⟨m, h⟩ else 0

/-- Exact sewing to the alternating Green boundary expression. All crosses
within the four-coordinate face are included, with the Cauchy orientation.
Higher boundary coordinates of a full source have NOT been set to zero by
this theorem: the zero extension here defines only this finite jet face. -/
theorem nativeSourceFourBoundaryEnergy_eq_alternating_green (x : Fin 4 → ℂ) :
    nativeSourceFourBoundaryEnergy x =
      2 * ∑ j ∈ Finset.range 4, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
        (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (nativeSourceFourBoundaryExtension x a) *
            nativeSourceFourBoundaryExtension x (2*j-a)).re) := by
  norm_num [Finset.sum_range_succ, nativeSourceFourBoundaryExtension,
    nativeSourceFourBoundaryEnergy, nativeSourceEvenBoundaryEnergy,
    nativeSourceOddBoundaryEnergy, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  simp only [show (⟨2, by omega⟩ : Fin 4) = 2 from rfl,
    show (⟨3, by omega⟩ : Fin 4) = 3 from rfl]
  ring



/-- The coefficients are literally the raw odd source derivatives, with the
factorials fixed by differentiation, not by a target kernel. -/
theorem nativeSourceOddBoundaryCoefficient_cast_jets :
    iteratedDeriv 1 completedNativeOperatorLogDerivative 0 =
      (nativeSourceOddBoundaryCoefficient 0 : ℂ) ∧
    iteratedDeriv 3 completedNativeOperatorLogDerivative 0 =
      6 * (nativeSourceOddBoundaryCoefficient 1 : ℂ) ∧
    iteratedDeriv 5 completedNativeOperatorLogDerivative 0 =
      120 * (nativeSourceOddBoundaryCoefficient 2 : ℂ) ∧
    iteratedDeriv 7 completedNativeOperatorLogDerivative 0 =
      5040 * (nativeSourceOddBoundaryCoefficient 3 : ℂ) := by
  obtain ⟨h0, h1, h2, h3⟩ := nativeSourceOddBoundaryCoefficient_integral_formulas
  obtain ⟨_, q1, _, q3, _, q5, _, q7⟩ := nativeSourceLogSlope_center_jets
  rw [h0, h1, h2, h3, q1, q3, q5, q7]
  unfold nativeSourceSeventhNumerator
  push_cast
  have ha : (completedNativeXiCosineMoment 0 : ℂ) ≠ 0 := by
    exact_mod_cast (completedNativeXiCosineMoment_pos 0).ne'
  repeat' constructor
  all_goals field_simp [ha]

/-- Exact transverse-source Taylor sewing on the original imaginary radial
line. Its alternating coefficients are the ones in the Green boundary face;
the entire analytic eighth-order remainder remains explicitly present. -/
theorem nativeSourceTransverseSlope_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ h : ℂ in nhds 0,
      -Complex.I * completedNativeOperatorLogDerivative (Complex.I*h) =
        (∑ j ∈ Finset.range 4, (-1 : ℂ)^j *
          (nativeSourceOddBoundaryCoefficient j : ℂ) * h^(2*j+1)) + h^8*R h := by
  obtain ⟨G, hGa, hG⟩ := nativeSourceLogSlope_analyticAt.exists_eventuallyEq_sum_add_pow_mul 8
  let R : ℂ → ℂ := fun h => -Complex.I * G (Complex.I*h)
  have hGc : AnalyticAt ℂ (fun h => G (Complex.I*h)) 0 :=
    hGa.fun_comp_of_eq (by fun_prop) (by simp)
  refine ⟨R, (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I) 0).fun_mul hGc, ?_⟩
  have ht : Filter.Tendsto (fun h : ℂ => Complex.I*h) (nhds 0) (nhds 0) := by
    simpa only [id_eq, mul_zero] using
      (Filter.tendsto_id : Filter.Tendsto (fun h : ℂ => h) (nhds 0) (nhds 0)).const_mul Complex.I
  obtain ⟨q0, _, q2, _, q4, _, q6, _⟩ := nativeSourceLogSlope_center_jets
  obtain ⟨q1, q3, q5, q7⟩ := nativeSourceOddBoundaryCoefficient_cast_jets
  filter_upwards [ht.eventually hG] with h hh
  rw [hh]
  dsimp only [R]
  norm_num [Finset.sum_range_succ, q0, q1, q2, q3, q4, q5, q6, q7, smul_eq_mul]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod, Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]
  ring

open ChiralReturn

/-- Diagonal readout of the EXISTING polarized Green identity at any odd
order. Every ordered boundary cross is retained. -/
theorem radialEulerPower_odd_green_energy (k N j : ℕ) (d : Fin N → ℂ) :
    2 * (inner ℂ (radialIncidentSynthesis k N d)
      (radialEulerPowerSynthesis k N (2*j+1) d)).re =
        ((k : ℝ)+1) * ∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re := by
  have h := congrArg Complex.re (radialEulerPower_green_boundary k N (2*j+1) d d)
  have hc := congrArg Complex.re (inner_conj_symm
    (radialIncidentSynthesis k N d) (radialEulerPowerSynthesis k N (2*j+1) d))
  have ho : Odd (2*j+1) := ⟨j, by omega⟩
  rw [Odd.neg_one_pow ho] at h
  simp only [radialEulerPowerSynthesis_zero, neg_one_mul, sub_neg_eq_add,
    Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum] at h
  have hr (a : ℕ) : ((-1 : ℂ)^a * conj (radialEulerBoundaryJet d a) *
      radialEulerBoundaryJet d (2*j+1-1-a)).re =
        (-1 : ℝ)^a * (conj (radialEulerBoundaryJet d a) *
          radialEulerBoundaryJet d (2*j-a)).re := by
    rw [show (-1 : ℂ)^a = (((-1 : ℝ)^a : ℝ) : ℂ) by push_cast; rfl]
    rw [mul_assoc, Complex.re_ofReal_mul]
    congr 2
  simp only [hr] at h
  simp only [Complex.conj_re] at hc
  linarith

/-- The FULL storage splits into its own finite alternating boundary tower
and its exact higher source remainder. No tail is removed and no positivity
of either summand is inferred from this identity. -/
theorem storage_one_eq_odd_green_tower_and_remainder (k N r : ℕ) (d : Fin N → ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (storage k (radialCompletedInputCoefficients k d) 1).re =
      2*((k : ℝ)+1) * ∑ j ∈ Finset.range r,
        radialCompletedOddSourceJetScale k j *
          (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
            (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re) +
        4 * (inner ℂ (radialIncidentSynthesis k N d)
          (radialCompletedOddSourceRemainderSynthesis k N r d)).re := by
  rw [storage_one_eq_complete_slope_pairing k N d hF hP,
    radialCompletedSlopeSynthesis_eq_oddJets_add_remainder k N r d,
    inner_add_right, Complex.add_re]
  have ht : 4 * (inner ℂ (radialIncidentSynthesis k N d)
      (radialCompletedOddSourceJetSynthesis k N r d)).re =
        2*((k : ℝ)+1) * ∑ j ∈ Finset.range r,
          radialCompletedOddSourceJetScale k j *
            (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
              (conj (radialEulerBoundaryJet d a) * radialEulerBoundaryJet d (2*j-a)).re) := by
    classical
    simp only [radialCompletedOddSourceJetSynthesis, inner_sum, inner_smul_right,
      Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h := radialEulerPower_odd_green_energy k N j d
    simp only [Complex.mul_re] at h
    linear_combination 2 * radialCompletedOddSourceJetScale k j * h
  rw [mul_add, ht]

end
end CarrySelfAdjointOperator

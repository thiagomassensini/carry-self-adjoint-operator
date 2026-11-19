import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge
import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz
import CarrySelfAdjointOperator.NativeSourceSchurThetaMasses
import Mathlib.Tactic

/-!
# Third-order native incident/return defect

The COMPLETE native characteristic F is locally F(z)=Phi(z²), and
H(u)=-Phi'(u)/Phi(u) is the genuine completed logarithmic response.
This yields an exact Cayley form along the radial imaginary axis.

The underlying scalar cubic identity is proved without identifying
pointwise contraction with matrix positivity.
-/

namespace CarrySelfAdjointOperator.HigherOrderCayleyDefect
open CarrySelfAdjointOperator
open Filter Topology
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Differentiated Schwarz reflection from the original material
completed characteristic, valid in the native entire reflection domain.
This is used to identify the radial quotient as REAL along the imaginary
axis, not merely as a complex Cayley shadow. -/
theorem native_characteristic_deriv_neg_conj (z : ℂ) :
    deriv completedNativeOperatorCharacteristic (-conj z) =
      -conj (deriv completedNativeOperatorCharacteristic z) := by
  let F : ℂ → ℂ := completedNativeOperatorCharacteristic
  have hF : (conj ∘ (fun w : ℂ => F (-w)) ∘ conj) = F := by
    funext w
    change conj (F (-conj w)) = F w
    have h := completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel w
    simpa [F] using (congrArg conj h)
  have hd : deriv F z =
      conj (deriv (fun w : ℂ => F (-w)) (conj z)) := by
    conv_lhs => rw [← hF]
    rw [deriv_conj_conj]
    rfl
  rw [deriv_comp_neg] at hd
  have hc : conj (deriv F z) = -deriv F (-conj z) := by
    simpa using congrArg conj hd
  change deriv F (-conj z) = -conj (deriv F z)
  linear_combination hc

theorem native_characteristic_radial_real (t : ℝ) :
    conj (completedNativeOperatorCharacteristic (Complex.I*(t:ℂ))) =
      completedNativeOperatorCharacteristic (Complex.I*(t:ℂ)) := by
  have h := completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel
    (Complex.I*(t:ℂ))
  have hfix : -(conj (Complex.I*(t:ℂ))) = Complex.I*(t:ℂ) := by simp
  rw [hfix] at h
  exact h.symm

theorem native_characteristic_deriv_radial_antireal (t : ℝ) :
    conj (deriv completedNativeOperatorCharacteristic (Complex.I*(t:ℂ))) =
      -deriv completedNativeOperatorCharacteristic (Complex.I*(t:ℂ)) := by
  have h := native_characteristic_deriv_neg_conj (Complex.I*(t:ℂ))
  have hfix : -(conj (Complex.I*(t:ℂ))) = Complex.I*(t:ℂ) := by simp
  rw [hfix] at h
  linear_combination h

/-- The actual completed radial chiral quotient is REAL on the imaginary
axis: conjugation of both HB coordinates reverses both signs. This
fact supplies the missing conjugation step in the physical feedback. -/
theorem native_chiral_radial_real (t : ℝ) :
    conj (completedNativeHermiteBiehlerChiralQuotient (Complex.I*(t:ℂ))) =
      completedNativeHermiteBiehlerChiralQuotient (Complex.I*(t:ℂ)) := by
  let z : ℂ := Complex.I*(t:ℂ)
  have hr := native_characteristic_radial_real t
  have hd := native_characteristic_deriv_radial_antireal t
  have hP : conj (completedNativePositiveHermiteBiehlerCoordinate z) =
      -completedNativePositiveHermiteBiehlerCoordinate z := by
    unfold completedNativePositiveHermiteBiehlerCoordinate
    dsimp [z] at hr hd ⊢
    simp only [map_add, map_neg, map_mul, Complex.conj_I, hr, hd]
    ring
  have hN : conj (completedNativeNegativeHermiteBiehlerCoordinate z) =
      -completedNativeNegativeHermiteBiehlerCoordinate z := by
    unfold completedNativeNegativeHermiteBiehlerCoordinate
    dsimp [z] at hr hd ⊢
    simp only [map_sub, map_neg, map_mul, Complex.conj_I, hr, hd]
    ring
  unfold completedNativeHermiteBiehlerChiralQuotient
  rw [map_div₀, hN, hP]
  simpa only [z] using
    (show (-completedNativeNegativeHermiteBiehlerCoordinate z) /
      (-completedNativePositiveHermiteBiehlerCoordinate z) =
        completedNativeNegativeHermiteBiehlerCoordinate z /
          completedNativePositiveHermiteBiehlerCoordinate z by simp)

def actualReducedRadialResponse (t : ℝ) : ℂ :=
  2 * (t:ℂ) * completedNativeLogDerivative (-(t:ℂ)^2)

def actualRadialCayley (t : ℝ) : ℂ :=
  (actualReducedRadialResponse t-1)/(actualReducedRadialResponse t+1)

/-- Source-derived exact Cayley formula in the squared variable, not a
formal arbitrary test multiplier. -/
theorem native_chiral_eq_reduced_cayley_eventually :
    ∀ᶠ t : ℝ in nhds 0,
      completedNativeHermiteBiehlerChiralQuotient (Complex.I*(t:ℂ)) =
        actualRadialCayley t := by
  have hp : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun t : ℝ => Complex.I*(t:ℂ)) 0 := by
      fun_prop
    simpa using hcont.tendsto
  filter_upwards
    [hp.eventually completedNativeChiralPickFactorization_eventually_regular,
     hp.eventually completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate]
    with t hreg hLog
  obtain ⟨_, hF, _⟩ := hreg
  rw [completedNativeHermiteBiehlerChiralQuotient_eq_cayley hF]
  change (completedNativeOperatorLogDerivative (Complex.I*(t:ℂ))-Complex.I)/
    (completedNativeOperatorLogDerivative (Complex.I*(t:ℂ))+Complex.I) = _
  rw [hLog]
  unfold actualRadialCayley actualReducedRadialResponse
  have hs : (Complex.I*(t:ℂ))^2 = -(t:ℂ)^2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [hs]
  have hi : Complex.I ≠ 0 := Complex.I_ne_zero
  have hr : 2*(Complex.I*(t:ℂ))*completedNativeLogDerivative (-(t:ℂ)^2) =
      Complex.I*(2*(t:ℂ)*completedNativeLogDerivative (-(t:ℂ)^2)) := by ring
  rw [hr]
  let A : ℂ := 2*(t:ℂ)*completedNativeLogDerivative (-(t:ℂ)^2)
  change (Complex.I*A-Complex.I)/(Complex.I*A+Complex.I) = (A-1)/(A+1)
  have hn : Complex.I*A-Complex.I = Complex.I*(A-1) := by ring
  have hd : Complex.I*A+Complex.I = Complex.I*(A+1) := by ring
  rw [hn, hd]
  exact mul_div_mul_left _ _ hi

/-- Exact algebraic product budget for a Cayley radial pair.
No asymptotics, and crucially no small-energy assumption. -/
theorem cayley_cubic_defect_cross_mul
    (i : ℕ) (u v : ℂ)
    (hu : u+1 ≠ 0) (hv : v+1 ≠ 0) :
    ((i:ℂ)/((i:ℂ)+2)*
        (1-((u-1)/(u+1))*((v-1)/(v+1))) -
      (((v-1)/(v+1))-((u-1)/(u+1)))) *
      (((i:ℂ)+2)*(u+1)*(v+1)) =
        4*(((i:ℂ)+1)*u-v) := by
  have hi : ((i:ℂ)+2) ≠ 0 := by
    exact_mod_cast (show (i:ℝ)+2 ≠ 0 by positivity)
  field_simp [hi, hu, hv]
  ring

/-! ## Third-order remainder of the genuine analytic completed response -/

def complexReducedResponse (z : ℂ) : ℂ :=
  2*z*completedNativeLogDerivative (-(z^2))

/-- The quadratic cancellation is exact for the genuine completed
response; the first potential nonzero remainder is cubic.
No asymptotic notation or unknown remainder has been used. -/
theorem cubic_difference_exact (z m : ℂ) :
    m*complexReducedResponse z - complexReducedResponse (m*z) =
      2*m*z^3 *
        (m^2*dslope completedNativeLogDerivative 0 (-(m*z)^2) -
          dslope completedNativeLogDerivative 0 (-(z^2))) := by
  have ha := sub_smul_dslope completedNativeLogDerivative 0 (-(z^2))
  have hb := sub_smul_dslope completedNativeLogDerivative 0 (-(m*z)^2)
  simp only [sub_zero, smul_eq_mul] at ha hb
  unfold complexReducedResponse
  have hz : completedNativeLogDerivative (-(z^2)) =
      completedNativeLogDerivative 0 -
        z^2*dslope completedNativeLogDerivative 0 (-(z^2)) := by
    linear_combination -ha
  have hw : completedNativeLogDerivative (-(m*z)^2) =
      completedNativeLogDerivative 0 -
        (m*z)^2*dslope completedNativeLogDerivative 0 (-(m*z)^2) := by
    linear_combination -hb
  rw [hz, hw]
  ring

def nativeRadialQuotient (t : ℝ) : ℂ :=
  completedNativeHermiteBiehlerChiralQuotient (Complex.I*(t:ℂ))

def actualRadialIncidentCoefficient (i : ℕ) (t : ℝ) : ℂ :=
  ((i:ℂ)/((i:ℂ)+2)) *
    (1-conj (nativeRadialQuotient t)*
      nativeRadialQuotient (((i+1:ℕ):ℝ)*t))

def actualRadialReturnedCoefficient (i : ℕ) (t : ℝ) : ℂ :=
  nativeRadialQuotient (((i+1:ℕ):ℝ)*t) - nativeRadialQuotient t

theorem actualReducedRadialResponse_tendsto_zero :
    Tendsto actualReducedRadialResponse (nhds (0:ℝ)) (nhds (0:ℂ)) := by
  have hinner : Tendsto (fun t : ℝ => -((t:ℂ)^2))
      (nhds 0) (nhds (0:ℂ)) := by
    have hc : ContinuousAt (fun t : ℝ => -((t:ℂ)^2)) 0 := by
      fun_prop
    simpa using hc.tendsto
  have hH := completedNativeLogDerivative_analyticAt.continuousAt.tendsto.comp
    hinner
  have ht : Tendsto (fun t : ℝ => (t:ℂ)) (nhds 0) (nhds (0:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto
  have h := (ht.mul hH).const_mul (2:ℂ)
  convert h using 1
  · funext t
    unfold actualReducedRadialResponse
    simp only [Function.comp_def]
    ring
  · simp

theorem actualReducedRadialResponse_zero :
    actualReducedRadialResponse 0 = 0 := by
  simp [actualReducedRadialResponse]

/-- The finite physical incident-return coefficient has an EXACT cubic
numerator, with both actual radial chiral source values and conjugation.
The extra denominator is forced by the genuine Cayley coordinate. -/
theorem native_radial_physical_defect_cross_mul_eventually (i : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      (actualRadialIncidentCoefficient i t -
         actualRadialReturnedCoefficient i t) *
      (((i:ℂ)+2)*(actualReducedRadialResponse t+1)*
        (actualReducedRadialResponse (((i+1:ℕ):ℝ)*t)+1)) =
      4*(((i:ℂ)+1)*actualReducedRadialResponse t -
        actualReducedRadialResponse (((i+1:ℕ):ℝ)*t)) := by
  let m : ℝ := ((i+1:ℕ):ℝ)
  have hm : Tendsto (fun t : ℝ => m*t) (nhds 0) (nhds 0) := by
    have ht : ContinuousAt (fun t : ℝ => m*t) 0 := by fun_prop
    simpa using ht.tendsto
  have hu := actualReducedRadialResponse_tendsto_zero
  have hu0 : ∀ᶠ t : ℝ in nhds 0,
      actualReducedRadialResponse t+1 ≠ 0 := by
    have ht : Tendsto
        (fun t : ℝ => actualReducedRadialResponse t+1)
        (nhds 0) (nhds (1:ℂ)) := by
      simpa using (hu.add_const (1:ℂ))
    exact ht.eventually_ne (by norm_num)
  filter_upwards [native_chiral_eq_reduced_cayley_eventually,
    hm.eventually native_chiral_eq_reduced_cayley_eventually,
    hu0, hm.eventually hu0] with t hq0 hq1 hden0 hden1
  have hReal := native_chiral_radial_real t
  unfold actualRadialIncidentCoefficient actualRadialReturnedCoefficient
    nativeRadialQuotient
  rw [hReal, hq0, hq1]
  exact cayley_cubic_defect_cross_mul i
    (actualReducedRadialResponse t)
    (actualReducedRadialResponse (m*t)) hden0 hden1

theorem completed_reduced_response_deriv_eq_h1 :
    deriv completedNativeLogDerivative 0 =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
  have h := completedNativeLogDerivativeTaylorCoefficient_eq_canonical 1
  simpa [completedNativeLogDerivativeTaylorCoefficient, iteratedDeriv_one] using h

def radialStep (k : ℕ) : ℂ := ((1/((k:ℝ)+1):ℝ) : ℂ)

theorem radialStep_ne_zero (k : ℕ) : radialStep k ≠ 0 := by
  unfold radialStep
  exact Complex.ofReal_ne_zero.mpr (by positivity)

theorem radialStep_tendsto_zero :
    Tendsto radialStep atTop (nhds (0:ℂ)) := by
  have hreal : Tendsto (fun k : ℕ => (1/((k:ℝ)+1):ℝ))
      atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  change Tendsto (fun k : ℕ => Complex.ofReal ((1/((k:ℝ)+1):ℝ)))
    atTop (nhds (0:ℂ))
  simpa only [Function.comp_def, Complex.ofReal_zero] using hcomplex

theorem completed_log_derivative_dslope_tendsto_h1 :
    Tendsto (dslope completedNativeLogDerivative 0)
      (nhds (0:ℂ))
      (nhds (canonicalCompletedNativeLogDerivativeMoment 1:ℂ)) := by
  have hc : ContinuousAt (dslope completedNativeLogDerivative 0) 0 :=
    continuousAt_dslope_same.mpr
      completedNativeLogDerivative_analyticAt.differentiableAt
  simpa [dslope_same, completed_reduced_response_deriv_eq_h1] using hc.tendsto

/-- The FIRST nonzero cubic coefficient is 2*m*(m²-1)*h₁ for the exact
reduced response. In particular, all h₀ terms cancel before differentiation. -/
theorem cubic_difference_normalized_tendsto (m : ℂ) :
    Tendsto (fun k : ℕ =>
      (m*complexReducedResponse (radialStep k) -
          complexReducedResponse (m*radialStep k)) /
        (radialStep k)^3)
      atTop
      (nhds (2*m*(m^2-1)*
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ))) := by
  have hz := radialStep_tendsto_zero
  have hz1 : Tendsto (fun k : ℕ => -(radialStep k)^2) atTop
      (nhds (0:ℂ)) := by
    simpa using (hz.pow 2).neg
  have hzm : Tendsto (fun k : ℕ => -(m*radialStep k)^2) atTop
      (nhds (0:ℂ)) := by
    simpa using ((hz.const_mul m).pow 2).neg
  have h1 := completed_log_derivative_dslope_tendsto_h1.comp hz1
  have h2 := completed_log_derivative_dslope_tendsto_h1.comp hzm
  have hlim := ((h2.const_mul (m^2)).sub h1).const_mul (2*m)
  have heq : 2*m*(m^2*
      (canonicalCompletedNativeLogDerivativeMoment 1:ℂ) -
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ)) =
      2*m*(m^2-1)*
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ) := by ring
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [] with k
  rw [cubic_difference_exact]
  have hk := radialStep_ne_zero k
  field_simp [hk]
  simp only [Function.comp_def]

def radialStepReal (k : ℕ) : ℝ := 1/((k:ℝ)+1)

theorem radialStepReal_tendsto_zero :
    Tendsto radialStepReal atTop (nhds (0:ℝ)) := by
  change Tendsto (fun k : ℕ => (1/((k:ℝ)+1):ℝ)) atTop (nhds 0)
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem actualReducedRadialResponse_eq_complex (t : ℝ) :
    actualReducedRadialResponse t = complexReducedResponse (t:ℂ) := rfl

theorem native_actual_incident_return_cubic_tendsto (i : ℕ) :
    Tendsto
      (fun k : ℕ =>
        (actualRadialIncidentCoefficient i (radialStepReal k) -
          actualRadialReturnedCoefficient i (radialStepReal k)) /
            (radialStep k)^3)
      atTop
      (nhds (8*(i:ℂ)*((i:ℂ)+1)*
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ))) := by
  let m : ℂ := (i:ℂ)+1
  let mr : ℝ := ((i+1:ℕ):ℝ)
  have ht := radialStepReal_tendsto_zero
  have hq := ht.eventually (native_radial_physical_defect_cross_mul_eventually i)
  have h0 := actualReducedRadialResponse_tendsto_zero.comp ht
  have htm : Tendsto (fun k : ℕ => mr*radialStepReal k)
      atTop (nhds (0:ℝ)) := by
    simpa using (ht.const_mul mr)
  have h1 := actualReducedRadialResponse_tendsto_zero.comp htm
  have hden : Tendsto (fun k : ℕ =>
      ((i:ℂ)+2)*(actualReducedRadialResponse (radialStepReal k)+1)*
        (actualReducedRadialResponse (mr*radialStepReal k)+1))
      atTop (nhds (((i:ℂ)+2))) := by
    have h := ((h0.add_const 1).mul (h1.add_const 1)).const_mul ((i:ℂ)+2)
    convert h using 1
    · funext k
      simp only [Function.comp_def, mr, Nat.cast_add, Nat.cast_one]
      ring
    · simp
  have hdenNe : ∀ᶠ k : ℕ in atTop,
      ((i:ℂ)+2)*(actualReducedRadialResponse (radialStepReal k)+1)*
        (actualReducedRadialResponse (mr*radialStepReal k)+1) ≠ 0 :=
    hden.eventually_ne (by
      exact_mod_cast (show (i:ℝ)+2 ≠ 0 by positivity))
  have hNum : Tendsto
      (fun k : ℕ =>
        (m*actualReducedRadialResponse (radialStepReal k) -
          actualReducedRadialResponse (mr*radialStepReal k)) /
          (radialStep k)^3)
      atTop
      (nhds (2*m*(m^2-1)*
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ))) := by
    convert cubic_difference_normalized_tendsto m using 1
    · funext k
      simp only [actualReducedRadialResponse_eq_complex]
      have he : (radialStepReal k:ℂ) = radialStep k := rfl
      rw [he]
      have hm : ((mr*radialStepReal k:ℝ):ℂ) = m*radialStep k := by
        simp [m, mr, radialStep, radialStepReal]
      rw [hm]
  have h := (hNum.const_mul (4:ℂ)).div hden (by
    exact_mod_cast (show (i:ℝ)+2 ≠ 0 by positivity))
  have hLim : 4*(2*m*(m^2-1)*
      (canonicalCompletedNativeLogDerivativeMoment 1:ℂ)) /
      ((i:ℂ)+2) =
      8*(i:ℂ)*((i:ℂ)+1)*
        (canonicalCompletedNativeLogDerivativeMoment 1:ℂ) := by
    have hi : ((i:ℂ)+2) ≠ 0 := by
      exact_mod_cast (show (i:ℝ)+2 ≠ 0 by positivity)
    dsimp [m]
    field_simp [hi]
    ring
  rw [hLim] at h
  apply h.congr'
  filter_upwards [hq, hdenNe] with k hc hne
  have htne : radialStep k ≠ 0 := radialStep_ne_zero k
  have heq :
      actualRadialIncidentCoefficient i (radialStepReal k) -
        actualRadialReturnedCoefficient i (radialStepReal k) =
      4*(m*actualReducedRadialResponse (radialStepReal k) -
          actualReducedRadialResponse (mr*radialStepReal k)) /
        (((i:ℂ)+2)*(actualReducedRadialResponse (radialStepReal k)+1)*
          (actualReducedRadialResponse (mr*radialStepReal k)+1)) :=
    (eq_div_iff hne).mpr (by simpa [m,mr] using hc)
  change
    (4 * ((m*actualReducedRadialResponse (radialStepReal k) -
      actualReducedRadialResponse (mr*radialStepReal k)) /
      (radialStep k)^3)) /
        (((i:ℂ)+2)*(actualReducedRadialResponse (radialStepReal k)+1)*
          (actualReducedRadialResponse (mr*radialStepReal k)+1)) =
    (actualRadialIncidentCoefficient i (radialStepReal k) -
        actualRadialReturnedCoefficient i (radialStepReal k)) /
      (radialStep k)^3
  rw [heq]
  simp only [div_eq_mul_inv]
  ring

/-- Strict sign is inherited from the independently proved odd material
source coefficient. The cubic expression itself did not presume h₁>0. -/
theorem completed_h1_positive_from_native_source :
    0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
  have h := nativeSourceMixedLeadingCoefficients_pos.2
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at h
  linarith

theorem native_actual_cubic_defect_coefficient_positive
    (i : ℕ) (hi : 0 < i) :
    0 < 8 * (i:ℝ) * ((i:ℝ)+1) *
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  have hi' : (0:ℝ) < (i:ℝ) := by exact_mod_cast hi
  exact mul_pos (mul_pos (mul_pos (by norm_num) hi') (by positivity))
    completed_h1_positive_from_native_source

/-- The fifth-order *symbolic candidate* in the first null direction (2,-1).
Its coefficient was derived by rational Taylor expansion and checked by
SymPy; the corresponding physical t⁻⁵ limit is NOT a Lean theorem yet. -/
def secondNullFifthCoefficientCandidate : ℝ :=
  128 * (4*(canonicalCompletedNativeLogDerivativeMoment 0)^3 *
    canonicalCompletedNativeLogDerivativeMoment 1 +
      (canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 2 -
        (canonicalCompletedNativeLogDerivativeMoment 1)^2))

/-- The candidate is positive using the already-known first two source signs
plus the independently established C3 two-even determinant certificate.
Only the sign of this named expression is proved, not its identification
as the actual t⁵ coefficient of the complete physical energy. -/
theorem secondNullFifthCoefficientCandidate_pos_of_two_even_det
    (hdet : 0 < canonicalCompletedNativeLogDerivativeMoment 0 *
        canonicalCompletedNativeLogDerivativeMoment 2 -
        (canonicalCompletedNativeLogDerivativeMoment 1)^2) :
    0 < secondNullFifthCoefficientCandidate := by
  have h0 : 0 < canonicalCompletedNativeLogDerivativeMoment 0 :=
    canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have h1 : 0 < canonicalCompletedNativeLogDerivativeMoment 1 :=
    completed_h1_positive_from_native_source
  have hpos : 0 < 4*(canonicalCompletedNativeLogDerivativeMoment 0)^3 *
    canonicalCompletedNativeLogDerivativeMoment 1 := by positivity
  unfold secondNullFifthCoefficientCandidate
  exact mul_pos (by norm_num : (0:ℝ) < 128) (add_pos hpos hdet)

#print axioms secondNullFifthCoefficientCandidate_pos_of_two_even_det
#print axioms completed_h1_positive_from_native_source
#print axioms native_actual_cubic_defect_coefficient_positive
#print axioms native_actual_incident_return_cubic_tendsto
#print axioms cubic_difference_normalized_tendsto
#print axioms cubic_difference_exact
#print axioms completed_reduced_response_deriv_eq_h1
#print axioms native_chiral_eq_reduced_cayley_eventually
#print axioms cayley_cubic_defect_cross_mul

end
end CarrySelfAdjointOperator.HigherOrderCayleyDefect

import CarrySelfAdjointOperator.CompletedNativeRawRealAllOrderBridge
import CarrySelfAdjointOperator.CompletedNativeAnalyticMomentGrowth
import Mathlib.Tactic

/-!
# Completed native moments from the bracket--TFVD Wronskian

The raw real-axis bridge proves that one concrete bracket--TFVD completion
carrier supplies both the Green readout and the completed trace `(F,-F')`.
This file reads the scalar moment germ directly from the two-point Wronskian
of that carrier.  The second point is fixed at the centered origin and the
two nonzero center factors are removed only on their proved nonvanishing
neighborhood.

The resulting Taylor coefficients are then compared with the canonical
division-free moment sequence.  No Green Gram representation, positivity
premise, zero hypothesis, or spectral data enters this construction.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace
  RealInnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- Scalar response read from the completed Wronskian projection of the
bracket--TFVD carrier. -/
def canonicalC3BracketTfvdNormalizedResponse
    (M : ℕ) (z : ℂ) : ℂ :=
  canonicalC3BracketTfvdCompletedWronskianReadout (M + 1) z 0 /
    ((2 : ℂ) * completedNativeOperatorCharacteristic z *
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0))

/-- Near the centered origin, the response extracted from the TFVD
Wronskian is exactly the canonical normalized response `-F'/(2F)`. -/
theorem canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed
    (M : ℕ) :
    canonicalC3BracketTfvdNormalizedResponse M =ᶠ[nhds 0]
      completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  have hdomain : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  have hcenterStar :
      (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hdomain, hnonzero] with z hzDomain hzNonzero
  have hzeroDomain : operatorHeightParameter 0 ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  rw [canonicalC3BracketTfvdNormalizedResponse,
    canonicalC3BracketTfvdCompletedWronskianReadout_eq_F_negFprime
      (M + 1) hzDomain hzeroDomain]
  change
    completedGreenWronskian completedNativeOperatorCharacteristic
          (fun u => -deriv completedNativeOperatorCharacteristic u) z 0 /
        ((2 : ℂ) * completedNativeOperatorCharacteristic z *
          (starRingEnd ℂ) (completedNativeOperatorCharacteristic 0)) =
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        (fun u => -deriv completedNativeOperatorCharacteristic u) z
  have hderivZero : deriv completedNativeOperatorCharacteristic 0 = 0 :=
    deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
      completedNativeOperatorCharacteristic_eventually_even
  unfold completedGreenWronskian completedGreenNormalizedResponse
  dsimp only
  rw [hderivZero]
  simp only [map_zero, neg_zero, mul_zero, sub_zero]
  field_simp [hzNonzero, hcenterStar]

/-- Taylor coefficient of the normalized response extracted from the
bracket--TFVD Wronskian. -/
def canonicalC3BracketTfvdResponseTaylorCoefficient
    (M order : ℕ) : ℂ :=
  iteratedDeriv order (canonicalC3BracketTfvdNormalizedResponse M) 0 /
    order.factorial

/-- Taylor coefficient of the canonical completed normalized response. -/
def completedNativeGreenResponseTaylorCoefficient (order : ℕ) : ℂ :=
  iteratedDeriv order
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) 0 /
    order.factorial

/-- The TFVD Wronskian coefficients are cutoff-independent and equal the
coefficients of the completed normalized response. -/
theorem canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed
    (M order : ℕ) :
    canonicalC3BracketTfvdResponseTaylorCoefficient M order =
      completedNativeGreenResponseTaylorCoefficient order := by
  unfold canonicalC3BracketTfvdResponseTaylorCoefficient
    completedNativeGreenResponseTaylorCoefficient
  rw [Filter.EventuallyEq.iteratedDeriv_eq order
    (canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed M)]

/-- The response coefficient does not depend on which finite TFVD carrier
cutoff is used to read the completed Wronskian. -/
theorem canonicalC3BracketTfvdResponseTaylorCoefficient_cutoff_independent
    (M₁ M₂ order : ℕ) :
    canonicalC3BracketTfvdResponseTaylorCoefficient M₁ order =
      canonicalC3BracketTfvdResponseTaylorCoefficient M₂ order := by
  rw [canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed,
    canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed]

/-! ## Coefficient recurrence of the completed response -/

/-- Full Taylor coefficient of the concrete completed characteristic. -/
def completedNativeFullCharacteristicTaylorCoefficient (order : ℕ) : ℂ :=
  iteratedDeriv order completedNativeOperatorCharacteristic 0 /
    order.factorial

/-- Even full coefficients are exactly the coefficients used by the
division-free native moment recurrence. -/
theorem completedNativeFullCharacteristicTaylorCoefficient_even
    (n : ℕ) :
    completedNativeFullCharacteristicTaylorCoefficient (2 * n) =
      completedNativeEvenCharacteristicCoefficient n := by
  unfold completedNativeFullCharacteristicTaylorCoefficient
    completedNativeEvenCharacteristicCoefficient completedGreenTaylorJet
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- Every odd Taylor derivative of the completed characteristic vanishes at
the centered origin, as a direct consequence of its proved even germ. -/
theorem iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero
    (n : ℕ) :
    iteratedDeriv (2 * n + 1) completedNativeOperatorCharacteristic 0 = 0 := by
  have h := Filter.EventuallyEq.iteratedDeriv_eq (2 * n + 1)
    completedNativeOperatorCharacteristic_eventually_even
  rw [iteratedDeriv_comp_neg] at h
  have hpow : (-1 : ℂ) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpow] at h
  simp only [neg_zero, neg_one_smul] at h
  have htwo : (2 : ℂ) *
      iteratedDeriv (2 * n + 1) completedNativeOperatorCharacteristic 0 = 0 := by
    calc
      (2 : ℂ) *
          iteratedDeriv (2 * n + 1) completedNativeOperatorCharacteristic 0 =
        iteratedDeriv (2 * n + 1)
            completedNativeOperatorCharacteristic 0 -
          (-iteratedDeriv (2 * n + 1)
            completedNativeOperatorCharacteristic 0) := by ring
      _ = 0 := by rw [h]; ring
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Consequently every odd full Taylor coefficient is zero. -/
theorem completedNativeFullCharacteristicTaylorCoefficient_odd
    (n : ℕ) :
    completedNativeFullCharacteristicTaylorCoefficient (2 * n + 1) = 0 := by
  unfold completedNativeFullCharacteristicTaylorCoefficient
  rw [iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero]
  simp

/-- The completed normalized response is analytic at the centered origin. -/
theorem completedNativeGreenNormalizedResponse_analyticAt :
    AnalyticAt ℂ
      (completedGreenNormalizedResponse
        completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) 0 := by
  have hF := completedNativeOperatorCharacteristic_analyticAt
    zero_mem_completedNativeHeightDomain
  have hcompanion :
      completedNativeOperatorBoundaryCompanion =
        fun z => -deriv completedNativeOperatorCharacteristic z := by
    funext z
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv z
  rw [hcompanion]
  unfold completedGreenNormalizedResponse
  exact hF.deriv.neg.div
    ((analyticAt_const.mul hF))
    (mul_ne_zero (by norm_num)
      completedNativeOperatorCharacteristic_zero_ne_zero)

/-- The normalized response satisfies its defining product identity on the
proved nonvanishing neighborhood of the center. -/
theorem completedNativeGreenNormalizedResponse_mul_characteristic_eventually :
    (fun z =>
      completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z *
        completedNativeOperatorCharacteristic z) =ᶠ[nhds 0]
      fun z => -(1 / 2 : ℂ) *
        deriv completedNativeOperatorCharacteristic z := by
  have hnonzero : ∀ᶠ z in nhds (0 : ℂ),
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hnonzero] with z hz
  unfold completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  field_simp [hz]

/-- Raw Leibniz recurrence obtained by differentiating the completed response
product identity in arbitrary order. -/
theorem completedNativeGreenResponse_rawDerivativeRecurrence
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) *
          iteratedDeriv i
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) 0 *
          iteratedDeriv (n - i)
            completedNativeOperatorCharacteristic 0 =
      -(1 / 2 : ℂ) *
        iteratedDeriv (n + 1) completedNativeOperatorCharacteristic 0 := by
  calc
    _ = iteratedDeriv n
        (fun z =>
          completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion z *
            completedNativeOperatorCharacteristic z) 0 := by
      exact (iteratedDeriv_mul
        completedNativeGreenNormalizedResponse_analyticAt.contDiffAt
        (completedNativeOperatorCharacteristic_analyticAt
          zero_mem_completedNativeHeightDomain).contDiffAt).symm
    _ = iteratedDeriv n
        (fun z => -(1 / 2 : ℂ) *
          deriv completedNativeOperatorCharacteristic z) 0 :=
      Filter.EventuallyEq.iteratedDeriv_eq n
        completedNativeGreenNormalizedResponse_mul_characteristic_eventually
    _ = -(1 / 2 : ℂ) *
        iteratedDeriv (n + 1) completedNativeOperatorCharacteristic 0 := by
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_succ']

/-- Factorial-normalized coefficient recurrence for the actual completed
response and characteristic. -/
theorem completedNativeGreenResponse_coefficientRecurrence
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        completedNativeGreenResponseTaylorCoefficient i *
          completedNativeFullCharacteristicTaylorCoefficient (n - i) =
      -(((n + 1 : ℕ) : ℂ) / 2) *
        completedNativeFullCharacteristicTaylorCoefficient (n + 1) := by
  have hraw := completedNativeGreenResponse_rawDerivativeRecurrence n
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) 0 *
            iteratedDeriv (n - i)
              completedNativeOperatorCharacteristic 0 =
        (n.factorial : ℂ) *
          ∑ i ∈ Finset.range (n + 1),
            completedNativeGreenResponseTaylorCoefficient i *
              completedNativeFullCharacteristicTaylorCoefficient (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold completedNativeGreenResponseTaylorCoefficient
      completedNativeFullCharacteristicTaylorCoefficient
    have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hfactorial :
        (n.choose i : ℂ) * (i.factorial : ℂ) *
            ((n - i).factorial : ℂ) =
          (n.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
    field_simp [show (i.factorial : ℂ) ≠ 0 by
        exact_mod_cast i.factorial_ne_zero,
      show ((n - i).factorial : ℂ) ≠ 0 by
        exact_mod_cast (n - i).factorial_ne_zero]
    calc
      (n.choose i : ℂ) *
            iteratedDeriv i
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) 0 *
          iteratedDeriv (n - i) completedNativeOperatorCharacteristic 0 *
        (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
        ((n.choose i : ℂ) * (i.factorial : ℂ) *
            ((n - i).factorial : ℂ)) *
          (iteratedDeriv i
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) 0 *
            iteratedDeriv (n - i)
              completedNativeOperatorCharacteristic 0) := by ring
      _ = (n.factorial : ℂ) *
          (iteratedDeriv i
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) 0 *
            iteratedDeriv (n - i)
              completedNativeOperatorCharacteristic 0) := by rw [hfactorial]
      _ = iteratedDeriv i
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) 0 *
          iteratedDeriv (n - i)
            completedNativeOperatorCharacteristic 0 *
          (n.factorial : ℂ) := by ring
  apply mul_left_cancel₀
    (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)
  calc
    (n.factorial : ℂ) *
          ∑ i ∈ Finset.range (n + 1),
            completedNativeGreenResponseTaylorCoefficient i *
              completedNativeFullCharacteristicTaylorCoefficient (n - i) =
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) 0 *
            iteratedDeriv (n - i)
              completedNativeOperatorCharacteristic 0 := hsum.symm
    _ = -(1 / 2 : ℂ) *
          iteratedDeriv (n + 1)
            completedNativeOperatorCharacteristic 0 := hraw
    _ = (n.factorial : ℂ) *
          (-(((n + 1 : ℕ) : ℂ) / 2) *
            completedNativeFullCharacteristicTaylorCoefficient (n + 1)) := by
      unfold completedNativeFullCharacteristicTaylorCoefficient
      field_simp [show ((n + 1).factorial : ℂ) ≠ 0 by
        exact_mod_cast (n + 1).factorial_ne_zero]
      rw [Nat.factorial_succ]
      push_cast
      ring

/-! ## Odd response coefficients are the canonical moments -/

/-- On an odd total degree, the full response convolution reduces exactly to
the odd response coefficients against the even characteristic coefficients. -/
theorem completedNativeGreenResponse_oddCoefficient_fullConvolution
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        completedNativeGreenResponseTaylorCoefficient (2 * k + 1) *
          completedNativeEvenCharacteristicCoefficient (n - k) =
      -(((n + 1 : ℕ) : ℂ) *
        completedNativeEvenCharacteristicCoefficient (n + 1)) := by
  classical
  let term : ℕ → ℂ := fun i =>
    completedNativeGreenResponseTaylorCoefficient i *
      completedNativeFullCharacteristicTaylorCoefficient (2 * n + 1 - i)
  have hfilter :
      ∑ i ∈ Finset.range (2 * n + 2), term i =
        ∑ i ∈ (Finset.range (2 * n + 2)).filter Odd, term i := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hiRange hiNotFiltered
    have hnotOdd : ¬ Odd i := by
      simpa only [Finset.mem_filter, hiRange, true_and] using hiNotFiltered
    have heven : Even i := Nat.not_odd_iff_even.mp hnotOdd
    rcases heven with ⟨k, hk⟩
    have hiLt : i < 2 * n + 2 := Finset.mem_range.mp hiRange
    have hkLe : k ≤ n := by omega
    unfold term
    rw [show 2 * n + 1 - i = 2 * (n - k) + 1 by omega,
      completedNativeFullCharacteristicTaylorCoefficient_odd]
    simp
  have hreindex :
      ∑ k ∈ Finset.range (n + 1),
          completedNativeGreenResponseTaylorCoefficient (2 * k + 1) *
            completedNativeEvenCharacteristicCoefficient (n - k) =
        ∑ i ∈ (Finset.range (2 * n + 2)).filter Odd, term i := by
    refine Finset.sum_bij (fun k _ => 2 * k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hkLt : k < n + 1 := Finset.mem_range.mp hk
        omega
      · exact ⟨k, by omega⟩
    · intro k₁ hk₁ k₂ hk₂ heq
      omega
    · intro i hi
      have hi' := Finset.mem_filter.mp hi
      have hiLt : i < 2 * n + 2 := Finset.mem_range.mp hi'.1
      rcases hi'.2 with ⟨k, hk⟩
      refine ⟨k, ?_, by omega⟩
      apply Finset.mem_range.mpr
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      unfold term
      rw [show 2 * n + 1 - (2 * k + 1) = 2 * (n - k) by omega,
        completedNativeFullCharacteristicTaylorCoefficient_even]
  have hrec := completedNativeGreenResponse_coefficientRecurrence (2 * n + 1)
  have hindex : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega] at hrec
  change (∑ i ∈ Finset.range (2 * n + 2), term i) = _ at hrec
  rw [hfilter, ← hreindex] at hrec
  rw [hindex, completedNativeFullCharacteristicTaylorCoefficient_even] at hrec
  convert hrec using 1
  all_goals push_cast
  all_goals ring

/-- Boundary-separated form of the same recurrence, matching the canonical
moment-sequence interface exactly. -/
theorem completedNativeGreenResponse_oddCoefficient_recurrence
    (n : ℕ) :
    completedNativeEvenCharacteristicCoefficient 0 *
          completedNativeGreenResponseTaylorCoefficient (2 * n + 1) +
        ∑ k ∈ Finset.range n,
          completedNativeGreenResponseTaylorCoefficient (2 * k + 1) *
            completedNativeEvenCharacteristicCoefficient (n - k) =
      -(((n + 1 : ℕ) : ℂ) *
        completedNativeEvenCharacteristicCoefficient (n + 1)) := by
  have h := completedNativeGreenResponse_oddCoefficient_fullConvolution n
  rw [Finset.sum_range_succ] at h
  simp only [Nat.sub_self] at h
  simpa [add_comm, mul_comm] using h

/-- The odd Taylor coefficients of the completed TFVD response are exactly
the canonical division-free logarithmic moments. -/
theorem completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical
    (n : ℕ) :
    completedNativeGreenResponseTaylorCoefficient (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hrest :
          ∑ k ∈ Finset.range n,
              completedNativeGreenResponseTaylorCoefficient (2 * k + 1) *
                completedNativeEvenCharacteristicCoefficient (n - k) =
            ∑ k ∈ Finset.range n,
              (canonicalCompletedNativeLogDerivativeMoment k : ℂ) *
                completedNativeEvenCharacteristicCoefficient (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      have hresponse :=
        completedNativeGreenResponse_oddCoefficient_recurrence n
      have hcanonical :=
        canonicalCompletedNativeLogDerivativeMoment_isMomentSequence n
      rw [hrest] at hresponse
      have hproduct :
          completedNativeEvenCharacteristicCoefficient 0 *
              completedNativeGreenResponseTaylorCoefficient (2 * n + 1) =
            completedNativeEvenCharacteristicCoefficient 0 *
              (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
        apply add_right_cancel
        exact hresponse.trans hcanonical.symm
      exact mul_left_cancel₀
        completedNativeEvenCharacteristicCoefficient_zero_ne_zero hproduct

/-- The quadratic reduction from the notes is exact coefficient by
coefficient: the `z^(2n+1)` coefficient of `-F'/(2F)` is the `u^n`
coefficient of the reduced logarithmic derivative `q(u)`. -/
theorem canonicalC3BracketTfvdResponseTaylorCoefficient_odd_eq_logDerivative
    (M n : ℕ) :
    canonicalC3BracketTfvdResponseTaylorCoefficient M (2 * n + 1) =
      completedNativeLogDerivativeTaylorCoefficient n := by
  rw [canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    completedNativeLogDerivativeTaylorCoefficient_eq_canonical]

/-! ## Concrete moments read from the TFVD carrier -/

/-- Real moment sequence obtained from the odd Taylor coefficients of the
normalized Wronskian readout of one bracket--TFVD carrier. -/
def canonicalC3BracketTfvdMoment (M n : ℕ) : ℝ :=
  (canonicalC3BracketTfvdResponseTaylorCoefficient M (2 * n + 1)).re

/-- The TFVD/Wronskian construction produces exactly the canonical native
moment at every order and every cutoff. -/
theorem canonicalC3BracketTfvdMoment_eq_canonical
    (M n : ℕ) :
    canonicalC3BracketTfvdMoment M n =
      canonicalCompletedNativeLogDerivativeMoment n := by
  rw [canonicalC3BracketTfvdMoment,
    canonicalC3BracketTfvdResponseTaylorCoefficient_eq_completed,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  simp

/-- Hence the moments read from every TFVD carrier satisfy the exact
division-free completed-native recurrence. -/
theorem canonicalC3BracketTfvdMoment_isMomentSequence (M : ℕ) :
    IsCompletedNativeLogDerivativeMomentSequence
      (canonicalC3BracketTfvdMoment M) := by
  have heq : canonicalC3BracketTfvdMoment M =
      canonicalCompletedNativeLogDerivativeMoment := by
    funext n
    exact canonicalC3BracketTfvdMoment_eq_canonical M n
  rw [heq]
  exact canonicalCompletedNativeLogDerivativeMoment_isMomentSequence

/-- The completed moment sequence read from the TFVD Wronskian is independent
of the finite carrier cutoff. -/
theorem canonicalC3BracketTfvdMoment_cutoff_independent
    (M₁ M₂ : ℕ) :
    canonicalC3BracketTfvdMoment M₁ =
      canonicalC3BracketTfvdMoment M₂ := by
  funext n
  rw [canonicalC3BracketTfvdMoment_eq_canonical,
    canonicalC3BracketTfvdMoment_eq_canonical]

/-! ## Cyclic Jacobi readout of the same TFVD moments -/

namespace CompletedNativeGreenWeylReducedHeightCertificate

/-- On every completed Green/Jacobi realization, the cyclic moments of the
positive operator are exactly the moments read from the TFVD Wronskian. -/
theorem completedJacobiCyclicMoment_eq_canonicalC3BracketTfvdMoment
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (M n : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let heven := completedGreenJet_even_linearIndependent
      certificate.evenIndependent
    greenJetJacobiCoreCyclicMoment
        (jet := completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)) heven n =
      canonicalC3BracketTfvdMoment M n := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  rw [certificate.completedJacobiCyclicMoment_eq_canonicalLogDerivativeMoment,
    canonicalC3BracketTfvdMoment_eq_canonical]

set_option maxHeartbeats 800000 in
/-- The finite cyclic resolvent readout is the truncated generating function
of the moments extracted from the bracket--TFVD Wronskian, with no root list
or fitted spectral input. -/
theorem completedJacobiResolventPrefixScalarReadout_eq_tfvdWronskianMoments
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (M : ℕ) (u : ℝ) (N : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ⟪(greenJetJacobiCoreResolventPrefix (jet := jet) u N :
        greenJetEvenHilbertSubspace jet),
      greenJetEvenSectorJet jet 0⟫_ℝ =
      ∑ k ∈ Finset.range (N + 1),
        u ^ k * canonicalC3BracketTfvdMoment M k := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  rw [certificate.completedJacobiResolventPrefixScalarReadout_eq_canonical]
  apply Finset.sum_congr rfl
  intro k hk
  rw [canonicalC3BracketTfvdMoment_eq_canonical]

set_option synthInstance.maxHeartbeats 200000 in
/-- On a nontrivial neighborhood of the centered point, the TFVD moment
polynomials converge to the scalar readout of the completed Jacobi resolvent
vector. -/
theorem tfvdWronskianMomentPolynomial_tendsto_completedJacobiResolventReadout
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (M : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      Tendsto
        (fun N : ℕ ↦
          ∑ k ∈ Finset.range (N + 1),
            u ^ k * canonicalC3BracketTfvdMoment M k)
        atTop
        (nhds
          ⟪(∑' n : ℕ,
              u ^ n • greenJetEvenSectorJet jet n),
            greenJetEvenSectorJet jet 0⟫_ℝ) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  obtain ⟨r, hr, hresolvent⟩ :=
    certificate.completedJacobiResolventPrefix_tendsto_tsum
  refine ⟨r, hr, fun u hu ↦ ?_⟩
  have hinner := Filter.Tendsto.inner (𝕜 := ℝ)
    (hresolvent u hu)
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ greenJetEvenSectorJet jet 0) atTop
      (nhds (greenJetEvenSectorJet jet 0)))
  apply hinner.congr'
  filter_upwards [] with N
  exact
    (certificate.completedJacobiResolventPrefixScalarReadout_eq_tfvdWronskianMoments
      M u N)

set_option synthInstance.maxHeartbeats 200000 in
/-- On a real neighborhood of the centered point, the bracket--TFVD moment
polynomials converge directly to the analytic logarithmic derivative of the
completed native characteristic.  The intermediate limit is the scalar
readout of the actual completed Jacobi resolvent. -/
theorem tfvdWronskianMomentPolynomial_tendsto_nativeLogDerivative
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylReducedHeightCertificate xiState moments)
    (M : ℕ) :
    ∀ᶠ u : ℝ in nhds 0,
      Tendsto
        (fun N : ℕ => Complex.ofReal
          (∑ k ∈ Finset.range (N + 1),
            u ^ k * canonicalC3BracketTfvdMoment M k))
        atTop
        (nhds (completedNativeLogDerivative (u : ℂ))) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨r, hr, hpolynomial⟩ :=
    certificate.tfvdWronskianMomentPolynomial_tendsto_completedJacobiResolventReadout M
  have hsmall : ∀ᶠ u : ℝ in nhds 0, |u| * r < 1 := by
    have htend : Tendsto (fun u : ℝ => |u| * r) (nhds 0) (nhds 0) := by
      simpa using Filter.Tendsto.mul_const r
        (_root_.continuous_abs.tendsto (0 : ℝ))
    simpa using htend.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hreadout :=
    certificate.completedJacobiResolventReadout_eventually_eq_nativeLogDerivative
  filter_upwards [hsmall, hreadout] with u hu hvalue
  have hcomplex := (hpolynomial u hu).ofReal
  rw [hvalue] at hcomplex
  exact hcomplex

end CompletedNativeGreenWeylReducedHeightCertificate

end

end CarrySelfAdjointOperator

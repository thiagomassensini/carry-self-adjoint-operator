import CarrySelfAdjointOperator.CompletedNativeHardyAlgebra
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import CarrySelfAdjointOperator.CompletedNativeLogDerivativePoles
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-!
# Hardy nonrecurrence: analytic bridge

The intended analytic argument is carried out in the centered height variable.
This module builds the Taylor coefficient tools needed to turn a finite
moment relation into an analytic identity on the existing height strip.
-/

open Filter Topology

namespace CarrySelfAdjointOperator

noncomputable section

private def hardyNativeGreenResponse (z : ℂ) : ℂ :=
  completedGreenNormalizedResponse completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion z

private def hardyTaylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The completed normalized response is an odd analytic germ, because the
completed characteristic is even and its boundary companion is its negative
derivative. -/
theorem completedNativeHardyResponse_eventually_odd :
    (fun z => hardyNativeGreenResponse (-z)) =ᶠ[𝓝 0]
      (fun z => -hardyNativeGreenResponse z) := by
  have hF := completedNativeOperatorCharacteristic_eventually_even
  have hF' := hF.deriv
  filter_upwards [hF, hF'] with z hz hdz
  rw [deriv_comp_neg] at hdz
  have hderiv : deriv completedNativeOperatorCharacteristic (-z) =
      -deriv completedNativeOperatorCharacteristic z := by
    linear_combination -hdz
  unfold hardyNativeGreenResponse completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
    completedNativeOperatorBoundaryCompanion_eq_neg_deriv, hz, hderiv]
  ring

/-- Every even Taylor coefficient of the completed normalized response
vanishes. -/
theorem completedNativeHardyResponseTaylorCoefficient_even_eq_zero
    (n : ℕ) :
    hardyTaylorCoefficient hardyNativeGreenResponse (2 * n) = 0 := by
  have h := Filter.EventuallyEq.iteratedDeriv_eq (2 * n)
    completedNativeHardyResponse_eventually_odd
  rw [iteratedDeriv_comp_neg] at h
  have hpow : (-1 : ℂ) ^ (2 * n) = 1 := by
    rw [pow_mul]
    norm_num
  have h' : iteratedDeriv (2 * n) hardyNativeGreenResponse 0 =
      -iteratedDeriv (2 * n) hardyNativeGreenResponse 0 := by
    simpa [hpow, iteratedDeriv_fun_neg] using h
  have hzero :
      iteratedDeriv (2 * n) hardyNativeGreenResponse 0 = 0 := by
    have htwo : (2 : ℂ) * iteratedDeriv (2 * n) hardyNativeGreenResponse 0 = 0 := by
      linear_combination h'
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  unfold hardyTaylorCoefficient
  rw [hzero]
  simp

/-- Factorial-normalized Taylor coefficients turn multiplication of analytic
germs into the usual coefficient convolution. -/
private theorem hardyTaylorCoefficient_mul
    {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (n : ℕ) :
    hardyTaylorCoefficient (fun z => f z * g z) n =
      ∑ i ∈ Finset.range (n + 1),
        hardyTaylorCoefficient f i * hardyTaylorCoefficient g (n - i) := by
  have hraw := iteratedDeriv_mul (n := n) hf.contDiffAt hg.contDiffAt
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 =
        (n.factorial : ℂ) *
          ∑ i ∈ Finset.range (n + 1),
            hardyTaylorCoefficient f i * hardyTaylorCoefficient g (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold hardyTaylorCoefficient
    have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hfactorial :
        (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
          (n.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
    field_simp [show (i.factorial : ℂ) ≠ 0 by
        exact_mod_cast i.factorial_ne_zero,
      show ((n - i).factorial : ℂ) ≠ 0 by
        exact_mod_cast (n - i).factorial_ne_zero]
    calc
      (n.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 *
          (i.factorial : ℂ) * ((n - i).factorial : ℂ) =
        ((n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ)) *
          (iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0) := by ring
      _ = (n.factorial : ℂ) *
          (iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0) := by
        rw [hfactorial]
      _ = iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0 *
          (n.factorial : ℂ) := by ring
  change iteratedDeriv n (f * g) 0 / (n.factorial : ℂ) = _
  rw [div_eq_iff (show (n.factorial : ℂ) ≠ 0 by
    exact_mod_cast n.factorial_ne_zero)]
  rw [hraw, hsum]
  ring

/-- Taylor coefficients commute with finite sums of analytic germs. -/
private theorem hardyTaylorCoefficient_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (n : ℕ) :
    hardyTaylorCoefficient (fun z => ∑ i ∈ s, f i z) n =
      ∑ i ∈ s, hardyTaylorCoefficient (f i) n := by
  classical
  change iteratedDeriv n (fun z => ∑ i ∈ s, f i z) 0 /
      (n.factorial : ℂ) = _
  rw [iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt)]
  simp only [hardyTaylorCoefficient, div_eq_mul_inv]
  rw [Finset.sum_mul]

/-- The Taylor coefficient of a scalar monomial. -/
private theorem hardyTaylorCoefficient_monomial
    (c : ℂ) (m n : ℕ) :
    hardyTaylorCoefficient (fun z => c * z ^ m) n =
      if n = m then c else 0 := by
  unfold hardyTaylorCoefficient
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  by_cases h : n = m
  · subst n
    simp only [if_true]
    simp [show (m.factorial : ℂ) ≠ 0 by
      exact_mod_cast m.factorial_ne_zero]
  · simp [h]

private theorem hardyResponse_analyticAt_zero :
    AnalyticAt ℂ hardyNativeGreenResponse 0 := by
  change AnalyticAt ℂ
    (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion) 0
  exact completedNativeGreenNormalizedResponse_analyticAt

private theorem hardyResponseTaylorCoefficient_odd (n : ℕ) :
    hardyTaylorCoefficient hardyNativeGreenResponse (2 * n + 1) =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  change completedNativeGreenResponseTaylorCoefficient (2 * n + 1) = _
  exact completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n

private theorem hardyResponseTaylorCoefficient_even (n : ℕ) :
    hardyTaylorCoefficient hardyNativeGreenResponse (2 * n) = 0 := by
  exact completedNativeHardyResponseTaylorCoefficient_even_eq_zero n

/-- Multiplying the response by one monomial shifts its Taylor coefficients. -/
private theorem hardyTaylorCoefficient_constMonomial_mul_response
    (c : ℂ) (m n : ℕ) :
    hardyTaylorCoefficient (fun z => (c * z ^ m) * hardyNativeGreenResponse z) n =
      if m ≤ n then
        c * hardyTaylorCoefficient hardyNativeGreenResponse (n - m) else 0 := by
  rw [hardyTaylorCoefficient_mul
    (by fun_prop)
    hardyResponse_analyticAt_zero]
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
        hardyTaylorCoefficient (fun z => c * z ^ m) i *
          hardyTaylorCoefficient hardyNativeGreenResponse (n - i)) =
      if m ≤ n then
        c * hardyTaylorCoefficient hardyNativeGreenResponse (n - m) else 0 := by
    by_cases hmn : m ≤ n
    · have hmem : m ∈ Finset.range (n + 1) := by
        simp [Nat.lt_succ_iff.mpr hmn]
      rw [Finset.sum_eq_single m]
      · simp [hardyTaylorCoefficient_monomial, hmn]
      · intro i hi hne
        simp [hardyTaylorCoefficient_monomial, hne]
      · intro hnot
        exact (hnot hmem).elim
    · have hsumZero :
          (∑ i ∈ Finset.range (n + 1),
            hardyTaylorCoefficient (fun z => c * z ^ m) i *
              hardyTaylorCoefficient hardyNativeGreenResponse (n - i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hne : i ≠ m := by omega
        simp [hardyTaylorCoefficient_monomial, hne]
      simp [hmn, hsumZero]
  exact hsum

private def hardyConvolutionCoefficient
    (moments : ℕ → ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (d k : ℕ) : ℂ :=
  ∑ i ∈ s, if d - i ≤ k then
    (a i : ℂ) * (moments (k - (d - i)) : ℂ) else 0

private def hardyDenominatorPolynomial
    (s : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) : Polynomial ℂ :=
  ∑ i ∈ s, Polynomial.C (a i : ℂ) * Polynomial.X ^ (d - i)

private def hardyNumeratorPolynomial
    (q : ℕ → ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range d, Polynomial.C (q k) * Polynomial.X ^ k

private def hardyLocalResponseResidual
    (D A : Polynomial ℂ) (z : ℂ) : ℂ :=
  D.eval (z ^ 2) * hardyNativeGreenResponse z -
    z * A.eval (z ^ 2)

private def hardyAnalyticResidual
    (D A : Polynomial ℂ) (z : ℂ) : ℂ :=
  -D.eval (z ^ 2) * deriv completedNativeOperatorCharacteristic z -
    (2 : ℂ) * z * A.eval (z ^ 2) * completedNativeOperatorCharacteristic z

private theorem hardyDenominatorPolynomial_eval
    (s : Finset ℕ) (a : ℕ → ℝ) (d : ℕ) (z : ℂ) :
    (hardyDenominatorPolynomial s a d).eval (z ^ 2) =
      ∑ i ∈ s, (a i : ℂ) * z ^ (2 * (d - i)) := by
  simp [hardyDenominatorPolynomial, Polynomial.eval_finsetSum,
    pow_mul, Polynomial.eval_mul]

private theorem hardyNumeratorPolynomial_eval
    (q : ℕ → ℂ) (d : ℕ) (z : ℂ) :
    z * (hardyNumeratorPolynomial q d).eval (z ^ 2) =
      ∑ k ∈ Finset.range d, q k * z ^ (2 * k + 1) := by
  rw [hardyNumeratorPolynomial, Polynomial.eval_finsetSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [← pow_mul]
  rw [pow_succ]
  ring

private theorem hardyConvolutionCoefficient_zero_of_relation
    {moments : ℕ → ℝ} (s : Finset ℕ) (a : ℕ → ℝ) (d k : ℕ)
    (hd : ∀ i, i ∈ s → i ≤ d)
    (hrel : ∀ j : ℕ, ∑ i ∈ s, a i * moments (i + j) = 0)
    (hdk : d ≤ k) :
    hardyConvolutionCoefficient moments s a d k = 0 := by
  rw [hardyConvolutionCoefficient]
  have hsum :
      (∑ i ∈ s, if d - i ≤ k then
        (a i : ℂ) * (moments (k - (d - i)) : ℂ) else 0) =
        ∑ i ∈ s, (a i : ℂ) * (moments (i + (k - d)) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hid := hd i hi
    have hle : d - i ≤ k := by omega
    have hindex : k - (d - i) = i + (k - d) := by omega
    simp [hle, hindex]
  rw [hsum]
  exact_mod_cast hrel (k - d)

private theorem hardyDenominatorPolynomial_ne_zero
    (s : Finset ℕ) (a : ℕ → ℝ) (d : ℕ)
    (hd : ∀ i, i ∈ s → i ≤ d)
    (ha : ∃ i, i ∈ s ∧ a i ≠ 0) :
    hardyDenominatorPolynomial s a d ≠ 0 := by
  obtain ⟨i, hi, hai⟩ := ha
  have hcoeff :
      (hardyDenominatorPolynomial s a d).coeff (d - i) = (a i : ℂ) := by
    simp only [hardyDenominatorPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hne : d - i ≠ d - j := by
        intro heq
        have hdi := hd i hi
        have hdj := hd j hj
        have hji' : j = i := by omega
        exact hji hji'
      simp [hne]
    · intro hnot
      exact (hnot hi).elim
  intro hzero
  rw [hzero] at hcoeff
  have hcast : (a i : ℂ) ≠ 0 := by exact_mod_cast hai
  exact hcast hcoeff.symm

private theorem hardyDenominatorResponseTaylorCoefficient
    (s : Finset ℕ) (a : ℕ → ℝ) (d n : ℕ) :
    hardyTaylorCoefficient
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
        hardyNativeGreenResponse z) n =
      ∑ i ∈ s, if 2 * (d - i) ≤ n then
        (a i : ℂ) * hardyTaylorCoefficient hardyNativeGreenResponse
          (n - 2 * (d - i)) else 0 := by
  have hfun :
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
        hardyNativeGreenResponse z) =
      (fun z => ∑ i ∈ s,
        ((a i : ℂ) * z ^ (2 * (d - i))) * hardyNativeGreenResponse z) := by
    funext z
    rw [hardyDenominatorPolynomial_eval, Finset.sum_mul]
  rw [hfun]
  have hterm : ∀ i ∈ s, AnalyticAt ℂ
      (fun z => ((a i : ℂ) * z ^ (2 * (d - i))) *
        hardyNativeGreenResponse z) 0 := by
    intro i hi
    have hmon : AnalyticAt ℂ
        (fun z => (a i : ℂ) * z ^ (2 * (d - i))) 0 := by
      fun_prop
    exact hmon.mul hardyResponse_analyticAt_zero
  rw [hardyTaylorCoefficient_sum s _ hterm n]
  apply Finset.sum_congr rfl
  intro i hi
  exact hardyTaylorCoefficient_constMonomial_mul_response _ _ _

private theorem hardyDenominatorResponseTaylorCoefficient_even
    (s : Finset ℕ) (a : ℕ → ℝ) (d n : ℕ) :
    hardyTaylorCoefficient
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
        hardyNativeGreenResponse z) (2 * n) = 0 := by
  rw [hardyDenominatorResponseTaylorCoefficient]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hle : 2 * (d - i) ≤ 2 * n
  · have hindex : 2 * n - 2 * (d - i) = 2 * (n - (d - i)) := by omega
    simp [hle, hindex, hardyResponseTaylorCoefficient_even]
  · simp [hle]

private theorem hardyDenominatorResponseTaylorCoefficient_odd
    (s : Finset ℕ) (a : ℕ → ℝ) (d n : ℕ) :
    hardyTaylorCoefficient
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
        hardyNativeGreenResponse z) (2 * n + 1) =
      hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment
        s a d n := by
  rw [hardyDenominatorResponseTaylorCoefficient]
  rw [hardyConvolutionCoefficient]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hdi : d - i ≤ n
  · have hle : 2 * (d - i) ≤ 2 * n + 1 := by omega
    have hindex : 2 * n + 1 - 2 * (d - i) =
        2 * (n - (d - i)) + 1 := by omega
    rw [if_pos hle, hindex, hardyResponseTaylorCoefficient_odd]
    simp [hdi]
  · have hnot : ¬ 2 * (d - i) ≤ 2 * n + 1 := by omega
    simp [hnot, hdi]

private theorem hardyNumeratorTaylorCoefficient
    (q : ℕ → ℂ) (d n : ℕ) :
    hardyTaylorCoefficient
      (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) n =
      ∑ k ∈ Finset.range d, if n = 2 * k + 1 then q k else 0 := by
  have hfun :
      (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) =
        (fun z => ∑ k ∈ Finset.range d, q k * z ^ (2 * k + 1)) := by
    funext z
    exact hardyNumeratorPolynomial_eval q d z
  rw [hfun, hardyTaylorCoefficient_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact hardyTaylorCoefficient_monomial (q k) (2 * k + 1) n
  · intro k hk
    fun_prop

private theorem hardyNumeratorTaylorCoefficient_even
    (q : ℕ → ℂ) (d n : ℕ) :
    hardyTaylorCoefficient
      (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) (2 * n) = 0 := by
  rw [hardyNumeratorTaylorCoefficient]
  apply Finset.sum_eq_zero
  intro k hk
  have hne : 2 * n ≠ 2 * k + 1 := by omega
  simp [hne]

private theorem hardyNumeratorTaylorCoefficient_odd
    (q : ℕ → ℂ) (d n : ℕ) :
    hardyTaylorCoefficient
      (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) (2 * n + 1) =
      if n < d then q n else 0 := by
  rw [hardyNumeratorTaylorCoefficient]
  have hcond (k : ℕ) : (2 * n + 1 = 2 * k + 1) ↔ n = k := by omega
  simp_rw [hcond]
  by_cases hn : n < d
  · have hnmem : n ∈ Finset.range d := Finset.mem_range.mpr hn
    rw [Finset.sum_eq_single n]
    · simp [hn]
    · intro k hk hkn
      simp [Ne.symm hkn]
    · intro hnot
      exact (hnot hnmem).elim
  · simp only [if_neg hn]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : n ≠ k := by
      intro heq
      subst k
      exact hn (Finset.mem_range.mp hk)
    simp only [if_neg hne]

private theorem hardyTaylorCoefficient_sub
    {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (n : ℕ) :
    hardyTaylorCoefficient (fun z => f z - g z) n =
      hardyTaylorCoefficient f n - hardyTaylorCoefficient g n := by
  change iteratedDeriv n (fun z => f z - g z) 0 / (n.factorial : ℂ) = _
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt]
  simp only [hardyTaylorCoefficient, div_eq_mul_inv]
  ring

private theorem hardyLocalResponseResidualTaylorCoefficient_zero
    (s : Finset ℕ) (a : ℕ → ℝ) (d n : ℕ)
    (hrel : ∀ j : ℕ,
      ∑ i ∈ s, a i * canonicalCompletedNativeLogDerivativeMoment (i + j) = 0)
    (hd : ∀ i, i ∈ s → i ≤ d) :
    hardyTaylorCoefficient
      (hardyLocalResponseResidual
        (hardyDenominatorPolynomial s a d)
        (hardyNumeratorPolynomial
          (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment
            s a d) d)) n = 0 := by
  let q : ℕ → ℂ :=
    hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment s a d
  have hDeval :
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2)) =
        (fun z => ∑ i ∈ s, (a i : ℂ) * z ^ (2 * (d - i))) := by
    funext z
    exact hardyDenominatorPolynomial_eval s a d z
  have hDanalytic : AnalyticAt ℂ
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2)) 0 := by
    rw [hDeval]
    fun_prop
  have hAeval :
      (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) =
        (fun z => ∑ k ∈ Finset.range d, q k * z ^ (2 * k + 1)) := by
    funext z
    exact hardyNumeratorPolynomial_eval q d z
  have hAanalytic : AnalyticAt ℂ
      (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) 0 := by
    rw [hAeval]
    fun_prop
  have hmulAnalytic := hDanalytic.mul hardyResponse_analyticAt_zero
  have hsub := hardyTaylorCoefficient_sub hmulAnalytic hAanalytic n
  change hardyTaylorCoefficient
    (fun z =>
      (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
          hardyNativeGreenResponse z -
        z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) n = _ at hsub
  change hardyTaylorCoefficient
    (fun z =>
      (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
          hardyNativeGreenResponse z -
        z * (hardyNumeratorPolynomial q d).eval (z ^ 2)) n = 0
  rcases n.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst n
    rw [hsub]
    change hardyTaylorCoefficient
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
        hardyNativeGreenResponse z) (k + k) -
      hardyTaylorCoefficient
        (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2))
        (k + k) = 0
    rw [← two_mul k]
    rw [hardyDenominatorResponseTaylorCoefficient_even,
      hardyNumeratorTaylorCoefficient_even]
    simp
  · subst n
    rw [hsub]
    change hardyTaylorCoefficient
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2) *
        hardyNativeGreenResponse z) (2 * k + 1) -
      hardyTaylorCoefficient
        (fun z => z * (hardyNumeratorPolynomial q d).eval (z ^ 2))
        (2 * k + 1) = 0
    rw [hardyDenominatorResponseTaylorCoefficient_odd,
      hardyNumeratorTaylorCoefficient_odd]
    by_cases hkd : k < d
    · simp [q, hkd]
    · have hdk : d ≤ k := by omega
      rw [if_neg hkd,
        hardyConvolutionCoefficient_zero_of_relation s a d k hd hrel hdk]
      simp

/-- If every Taylor coefficient of an analytic residual vanishes, the
residual vanishes on a neighborhood of the centre. -/
private theorem hardyLocalResponseResidual_eventuallyEq_zero
    (s : Finset ℕ) (a : ℕ → ℝ) (d : ℕ)
    (hrel : ∀ j : ℕ,
      ∑ i ∈ s, a i * canonicalCompletedNativeLogDerivativeMoment (i + j) = 0)
    (hd : ∀ i, i ∈ s → i ≤ d) :
    hardyLocalResponseResidual
      (hardyDenominatorPolynomial s a d)
      (hardyNumeratorPolynomial
        (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment
          s a d) d) =ᶠ[nhds 0] fun _ => 0 := by
  let D := hardyDenominatorPolynomial s a d
  let A := hardyNumeratorPolynomial
    (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment s a d) d
  have hDanalytic : AnalyticAt ℂ
      (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2)) 0 := by
    have heval : (fun z => (hardyDenominatorPolynomial s a d).eval (z ^ 2)) =
        (fun z => ∑ i ∈ s, (a i : ℂ) * z ^ (2 * (d - i))) := by
      funext z
      exact hardyDenominatorPolynomial_eval s a d z
    rw [heval]
    fun_prop
  have hAanalytic : AnalyticAt ℂ
      (fun z => z * (hardyNumeratorPolynomial
        (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment s a d)
        d).eval (z ^ 2)) 0 := by
    have heval : (fun z => z * (hardyNumeratorPolynomial
        (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment s a d)
        d).eval (z ^ 2)) =
        (fun z => ∑ k ∈ Finset.range d,
          hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment
            s a d k * z ^ (2 * k + 1)) := by
      funext z
      exact hardyNumeratorPolynomial_eval _ d z
    rw [heval]
    fun_prop
  have hHanalytic : AnalyticAt ℂ
      (hardyLocalResponseResidual D A) 0 := by
    dsimp [hardyLocalResponseResidual, D, A]
    exact (hDanalytic.mul hardyResponse_analyticAt_zero).sub hAanalytic
  have hcoeff : ∀ n : ℕ,
      hardyTaylorCoefficient (hardyLocalResponseResidual D A) n = 0 := by
    intro n
    simpa [D, A] using
      hardyLocalResponseResidualTaylorCoefficient_zero s a d n hrel hd
  have hderiv : ∀ n : ℕ,
      iteratedDeriv n (hardyLocalResponseResidual D A) 0 = 0 := by
    intro n
    have hn := hcoeff n
    unfold hardyTaylorCoefficient at hn
    have hfactorial : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    exact (div_eq_zero_iff.mp hn).resolve_right hfactorial
  have horder : analyticOrderAt (hardyLocalResponseResidual D A) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hHanalytic).2
    intro i hi
    exact hderiv i
  rw [analyticOrderAt_eq_top] at horder
  filter_upwards [horder] with z hz
  exact hz

/-- The polynomial residual is analytic throughout the existing height strip. -/
private theorem hardyAnalyticResidual_analyticOnNhd (D A : Polynomial ℂ) :
    AnalyticOnNhd ℂ (hardyAnalyticResidual D A)
      completedNativeHeightDomain := by
  intro z hz
  have hF := completedNativeOperatorCharacteristic_analyticAt hz
  have hDfun : (fun w : ℂ => D.eval (w ^ 2)) =
      (fun w => ∑ i ∈ Finset.range (D.natDegree + 1),
        D.coeff i * w ^ (2 * i)) := by
    funext w
    rw [Polynomial.eval_eq_sum_range]
    simp only [pow_mul]
  have hAfun : (fun w : ℂ => A.eval (w ^ 2)) =
      (fun w => ∑ i ∈ Finset.range (A.natDegree + 1),
        A.coeff i * w ^ (2 * i)) := by
    funext w
    rw [Polynomial.eval_eq_sum_range]
    simp only [pow_mul]
  have hD : AnalyticAt ℂ (fun w : ℂ => D.eval (w ^ 2)) z := by
    rw [hDfun]
    fun_prop
  have hA : AnalyticAt ℂ (fun w : ℂ => A.eval (w ^ 2)) z := by
    rw [hAfun]
    fun_prop
  have hlinear : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by
    fun_prop
  change AnalyticAt ℂ
    (fun w => -(D.eval (w ^ 2)) * deriv completedNativeOperatorCharacteristic w -
      ((2 : ℂ) * w) * A.eval (w ^ 2) * completedNativeOperatorCharacteristic w) z
  exact (hD.neg.mul hF.deriv).sub ((hlinear.mul hA).mul hF)

private theorem hardy_mem_height_iff_im_bounds {z : ℂ} :
    z ∈ completedNativeHeightDomain ↔
      -((1 : ℝ) / 2) < z.im ∧ z.im < (1 : ℝ) / 2 := by
  unfold completedNativeHeightDomain
  change (0 < (operatorHeightParameter z).re ∧
      (operatorHeightParameter z).re < 1) ↔ _
  simp only [operatorHeightParameter, Complex.add_re, Complex.div_re,
    Complex.one_re, Complex.I_mul_re]
  norm_num
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The centered native height domain is a horizontal convex strip. -/
theorem isPreconnected_completedNativeHeightDomain :
    IsPreconnected completedNativeHeightDomain := by
  have hset : completedNativeHeightDomain =
      {z : ℂ | -((1 : ℝ) / 2) < z.im ∧ z.im < (1 : ℝ) / 2} := by
    ext z
    exact hardy_mem_height_iff_im_bounds
  rw [hset]
  exact ((convex_halfSpace_im_gt (-((1 : ℝ) / 2))).inter
    (convex_halfSpace_im_lt ((1 : ℝ) / 2))).isPreconnected

/-- A finite moment recurrence produces a residual identity on the whole
height strip by analytic continuation. -/
private theorem hardyAnalyticResidual_eq_zero_of_moment_relation
    (s : Finset ℕ) (a : ℕ → ℝ) (d : ℕ)
    (hrel : ∀ j : ℕ,
      ∑ i ∈ s, a i * canonicalCompletedNativeLogDerivativeMoment (i + j) = 0)
    (hd : ∀ i, i ∈ s → i ≤ d) :
    Set.EqOn
      (hardyAnalyticResidual (hardyDenominatorPolynomial s a d)
        (hardyNumeratorPolynomial
          (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment
            s a d) d))
      0 completedNativeHeightDomain := by
  let D := hardyDenominatorPolynomial s a d
  let A := hardyNumeratorPolynomial
    (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment s a d) d
  have hlocal := hardyLocalResponseResidual_eventuallyEq_zero s a d hrel hd
  have hproduct := completedNativeGreenNormalizedResponse_mul_characteristic_eventually
  have hevent : hardyAnalyticResidual D A =ᶠ[nhds 0] fun _ => 0 := by
    filter_upwards [hlocal, hproduct] with z hlocalz hproductz
    have hlocalz' : D.eval (z ^ 2) * hardyNativeGreenResponse z -
        z * A.eval (z ^ 2) = 0 := by
      simpa [hardyLocalResponseResidual, D, A] using hlocalz
    have hresponse : hardyNativeGreenResponse z *
        completedNativeOperatorCharacteristic z =
          -(1 / 2 : ℂ) * deriv completedNativeOperatorCharacteristic z := by
      simpa [hardyNativeGreenResponse] using hproductz
    have hfirst : D.eval (z ^ 2) * hardyNativeGreenResponse z *
        (2 * completedNativeOperatorCharacteristic z) =
          -(D.eval (z ^ 2) * deriv completedNativeOperatorCharacteristic z) := by
      calc
        _ = D.eval (z ^ 2) *
            (hardyNativeGreenResponse z * completedNativeOperatorCharacteristic z * 2) := by ring
        _ = D.eval (z ^ 2) *
            ((-(1 / 2 : ℂ) * deriv completedNativeOperatorCharacteristic z) * 2) := by
              rw [hresponse]
        _ = _ := by ring
    change hardyAnalyticResidual D A z = 0
    unfold hardyAnalyticResidual
    calc
      _ = -(D.eval (z ^ 2) * deriv completedNativeOperatorCharacteristic z) -
          2 * z * A.eval (z ^ 2) * completedNativeOperatorCharacteristic z := by ring
      _ = D.eval (z ^ 2) * hardyNativeGreenResponse z *
          (2 * completedNativeOperatorCharacteristic z) -
          z * A.eval (z ^ 2) * (2 * completedNativeOperatorCharacteristic z) := by
            rw [← hfirst]
            ring
      _ = (D.eval (z ^ 2) * hardyNativeGreenResponse z -
          z * A.eval (z ^ 2)) *
          (2 * completedNativeOperatorCharacteristic z) := by ring
      _ = 0 := by rw [hlocalz']; ring
  exact (hardyAnalyticResidual_analyticOnNhd D A).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_completedNativeHeightDomain
    zero_mem_completedNativeHeightDomain hevent

/-- User-supplied hypothesis of infinitely many positive real zeros of the
native characteristic. -/
def InfinitePositiveRealNativeZeros : Prop :=
  Set.Infinite {t : ℝ | 0 < t ∧ completedNativeOperatorCharacteristic (t : ℂ) = 0}

/-- Polynomial evaluation at `z²` is an analytic function of the height
variable. -/
private theorem hardyPolynomialEvalSq_analyticAt (P : Polynomial ℂ) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => P.eval (w ^ 2)) z := by
  have heval : (fun w : ℂ => P.eval (w ^ 2)) =
      (fun w => ∑ i ∈ Finset.range (P.natDegree + 1),
        P.coeff i * w ^ (2 * i)) := by
    funext w
    rw [Polynomial.eval_eq_sum_range]
    simp only [pow_mul]
  rw [heval]
  fun_prop

/-- Near a zero of `F`, a nonvanishing denominator in the recurrence would
make its logarithmic derivative analytic, contradicting its simple pole. -/
private theorem hardyDenominator_vanishes_at_positive_zero
    (D A : Polynomial ℂ)
    (hidentity : Set.EqOn (hardyAnalyticResidual D A) 0
      completedNativeHeightDomain)
    {t : ℝ} (_ht : 0 < t)
    (hzero : completedNativeOperatorCharacteristic (t : ℂ) = 0) :
    D.eval ((t : ℂ) ^ 2) = 0 := by
  let z : ℂ := t
  have hzDomain : z ∈ completedNativeHeightDomain := by
    simpa [z] using ofReal_mem_completedNativeHeightDomain t
  by_contra hDzero
  have hFanalytic := completedNativeOperatorCharacteristic_analyticAt hzDomain
  have hFne : ∀ᶠ w : ℂ in nhdsWithin z {z}ᶜ,
      completedNativeOperatorCharacteristic w ≠ 0 :=
    hFanalytic.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (completedNativeOperatorCharacteristic_not_eventually_zero hzDomain)
  have hDne : ∀ᶠ w : ℂ in nhds z, D.eval (w ^ 2) ≠ 0 :=
    (hardyPolynomialEvalSq_analyticAt D z).continuousAt.eventually_ne hDzero
  have hdomain : ∀ᶠ w : ℂ in nhds z, w ∈ completedNativeHeightDomain :=
    isOpen_completedNativeHeightDomain.mem_nhds hzDomain
  have hlogEq : completedNativeOperatorLogDerivative =ᶠ[nhdsWithin z {z}ᶜ]
      (fun w => (2 : ℂ) * w * A.eval (w ^ 2) / D.eval (w ^ 2)) := by
    filter_upwards [hFne, hDne.filter_mono nhdsWithin_le_nhds,
      hdomain.filter_mono nhdsWithin_le_nhds] with w hFw hDw hwDomain
    have hE := hidentity hwDomain
    unfold hardyAnalyticResidual at hE
    have hE' : -(D.eval (w ^ 2)) * deriv completedNativeOperatorCharacteristic w -
        (2 : ℂ) * w * A.eval (w ^ 2) *
          completedNativeOperatorCharacteristic w = 0 := by
      simpa using hE
    unfold completedNativeOperatorLogDerivative
    apply (div_eq_div_iff hFw hDw).2
    linear_combination hE'
  have hlinear : AnalyticAt ℂ (fun w : ℂ => (2 : ℂ) * w) z := by
    fun_prop
  have hA := hardyPolynomialEvalSq_analyticAt A z
  have hD := hardyPolynomialEvalSq_analyticAt D z
  have hrhs : AnalyticAt ℂ
      (fun w => (2 : ℂ) * w * A.eval (w ^ 2) / D.eval (w ^ 2)) z :=
    (hlinear.mul hA).div hD hDzero
  have horder := meromorphicOrderAt_congr hlogEq
  rw [completedNativeOperatorLogDerivative_meromorphicOrderAt_eq_neg_one
    hzDomain (by simpa [z] using hzero)] at horder
  have hnonneg := hrhs.meromorphicOrderAt_nonneg
  rw [← horder] at hnonneg
  exact (not_le_of_gt
    (show ((-1 : ℤ) : WithTop ℤ) < 0 by
      exact_mod_cast (show (-1 : ℤ) < 0 by norm_num))) hnonneg

/-- Infinitely many positive real zeros rule out every finite recurrence of
the native logarithmic derivative moments. -/
theorem canonicalCompletedNativeLogDerivativeMoment_noFiniteMomentRelation_of_infinitePositiveRealNativeZeros
    (hzeros : InfinitePositiveRealNativeZeros) :
    NoFiniteMomentRelation canonicalCompletedNativeLogDerivativeMoment := by
  intro s a haSupport hrel i
  by_contra hai
  have hi : i ∈ s := by
    by_contra hnot
    exact hai (haSupport i hnot)
  have hsne : s.Nonempty := ⟨i, hi⟩
  let d := s.max' hsne
  have hd : ∀ j, j ∈ s → j ≤ d := by
    intro j hj
    exact s.le_max' j hj
  have hrel' : ∀ j : ℕ,
      ∑ k ∈ s, a k * canonicalCompletedNativeLogDerivativeMoment (k + j) = 0 := by
    intro j
    simpa [NoFiniteMomentRelation, Nat.zero_add] using hrel j
  have haNonzero : ∃ j, j ∈ s ∧ a j ≠ 0 := ⟨i, hi, hai⟩
  let D := hardyDenominatorPolynomial s a d
  let A := hardyNumeratorPolynomial
    (hardyConvolutionCoefficient canonicalCompletedNativeLogDerivativeMoment s a d) d
  have hD : D ≠ 0 := by
    exact hardyDenominatorPolynomial_ne_zero s a d hd haNonzero
  have hidentity : Set.EqOn (hardyAnalyticResidual D A) 0
      completedNativeHeightDomain := by
    simpa [D, A] using hardyAnalyticResidual_eq_zero_of_moment_relation
      s a d hrel' hd
  let T : Set ℝ :=
    {t | 0 < t ∧ completedNativeOperatorCharacteristic (t : ℂ) = 0}
  have hDzeros : ∀ t ∈ T, D.eval ((t : ℂ) ^ 2) = 0 := by
    intro t ht
    exact hardyDenominator_vanishes_at_positive_zero D A hidentity ht.1 ht.2
  have hinj : Set.InjOn (fun t : ℝ => (t : ℂ) ^ 2) T := by
    intro x hx y hy hxy
    have hxy' : (x : ℂ) ^ 2 = (y : ℂ) ^ 2 := hxy
    have hsq : x ^ 2 = y ^ 2 := by exact_mod_cast hxy'
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exact heq
    · linarith [hx.1, hy.1]
  have himage : ((fun t : ℝ => (t : ℂ) ^ 2) '' T).Infinite :=
    (Set.infinite_image_iff hinj).2 (by
      simpa [T, InfinitePositiveRealNativeZeros] using hzeros)
  have himageRoots : ((fun t : ℝ => (t : ℂ) ^ 2) '' T) ⊆
      {u : ℂ | Polynomial.IsRoot D u} := by
    rintro u ⟨t, ht, rfl⟩
    change D.eval ((t : ℂ) ^ 2) = 0
    exact hDzeros t ht
  have hfinite : Set.Finite ((fun t : ℝ => (t : ℂ) ^ 2) '' T) :=
    (Polynomial.finite_setOf_isRoot hD).subset himageRoots
  exact himage hfinite

end

end CarrySelfAdjointOperator

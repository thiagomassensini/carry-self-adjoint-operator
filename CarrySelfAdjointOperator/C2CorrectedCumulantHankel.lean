import CarrySelfAdjointOperator.CompletedNativeSixthOrderThetaPositivity
import CarrySelfAdjointOperator.AllOrderLogJetLedger
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Corrected cumulants in the Hankel metric

This file transports signs after the analytic identification of the source
cumulants. Its hypothesis is the pointwise analytic bridge, in exactly the
normalization of the canonical logarithmic moment recurrence.
-/

open Matrix

namespace CarrySelfAdjointOperator

noncomputable section

/-- The corrected even cumulants with the factorial normalization of the
height variable. -/
def correctedCumulantEntry (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (2 * n + 2) / (2 * ((2 * n + 1).factorial : ℝ))

def cumulantSignMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => (-1 : ℝ) ^ (i : ℕ)

/-- In the even coordinate the actual, unit-normalized logarithm gives
the canonical moments at every order. -/
theorem canonicalEvenLogJet_eq_moment (n : ℕ) :
    iteratedDeriv (n + 1)
        (fun u : ℂ => Complex.log
          (completedNativeEvenCharacteristic u / completedNativeEvenCharacteristic 0)) 0 =
      -(n.factorial : ℂ) * (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  let G := completedNativeEvenCharacteristic
  have h0 : G 0 ≠ 0 := completedNativeEvenCharacteristic_zero_ne_zero
  have ha : AnalyticAt ℂ G 0 := completedNativeEvenCharacteristic_analyticAt
  have hu : AnalyticAt ℂ (fun u => G u / G 0) 0 :=
    ha.div analyticAt_const h0
  have hunit : (fun u => G u / G 0) 0 = 1 := div_self h0
  have hl : logDeriv (fun u => G u / G 0) = fun u => -completedNativeLogDerivative u := by
    funext u
    simp only [logDeriv, Pi.div_apply, completedNativeLogDerivative, neg_div, neg_neg]
    change deriv (fun u => G u / G 0) u / (G u / G 0) = deriv G u / G u
    rw [deriv_div_const]
    by_cases hu₀ : G u = 0
    · simp [hu₀]
    · field_simp
  change iteratedDeriv (n + 1) (fun u : ℂ => Complex.log (G u / G 0)) 0 = _
  rw [AllOrderLogJet.unit_logJet_succ hu hunit, hl]
  rw [iteratedDeriv_fun_neg, completedNativeLogDerivative_iteratedDeriv_eq,
    completedNativeLogDerivativeTaylorCoefficient_eq_canonical, neg_mul]

theorem correctedCumulantHankel_congruence {C h : ℕ → ℝ}
    (hbridge : ∀ n, h n = (-1 : ℝ) ^ n * correctedCumulantEntry C n)
    (N : ℕ) :
    cumulantSignMatrix N * hankelGram h N * cumulantSignMatrix N =
      hankelGram (correctedCumulantEntry C) N := by
  ext i j
  simp only [cumulantSignMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    hankelGram_apply, hbridge]
  rw [pow_add]
  have hsq (n : ℕ) : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((-1 : ℝ) ^ (i : ℕ) *
        (((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (j : ℕ)) *
          correctedCumulantEntry C ((i : ℕ) + (j : ℕ)))) *
        (-1 : ℝ) ^ (j : ℕ) =
        ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) *
          ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) *
          correctedCumulantEntry C ((i : ℕ) + (j : ℕ)) := by ring
    _ = _ := by rw [hsq, hsq, one_mul, one_mul]

private theorem cumulantSignMatrix_conjTranspose (N : ℕ) :
    (cumulantSignMatrix N)ᴴ = cumulantSignMatrix N := by
  simp [cumulantSignMatrix]

private theorem cumulantSignMatrix_mulVec_injective (N : ℕ) :
    Function.Injective (cumulantSignMatrix N).mulVec := by
  intro a b hab
  funext i
  have h := congrFun hab i
  simp only [cumulantSignMatrix, Matrix.mulVec_diagonal] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h

theorem correctedCumulantHankel_posDef_iff {C h : ℕ → ℝ}
    (hbridge : ∀ n, h n = (-1 : ℝ) ^ n * correctedCumulantEntry C n)
    (N : ℕ) :
    (hankelGram (correctedCumulantEntry C) N).PosDef ↔ (hankelGram h N).PosDef := by
  let J := cumulantSignMatrix N
  have hJ : Jᴴ = J := cumulantSignMatrix_conjTranspose N
  have hinj : Function.Injective J.mulVec := cumulantSignMatrix_mulVec_injective N
  have hcongr : J * hankelGram h N * J = hankelGram (correctedCumulantEntry C) N :=
    correctedCumulantHankel_congruence hbridge N
  have hJJ : J * J = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← mul_pow]
    norm_num
  constructor
  · intro hpos
    have ht := hpos.conjTranspose_mul_mul_same hinj
    rw [hJ, ← hcongr] at ht
    have hh : J * (J * hankelGram h N * J) * J =
        (J * J) * hankelGram h N * (J * J) := by
      simp only [Matrix.mul_assoc]
    rwa [hh, hJJ, Matrix.one_mul, Matrix.mul_one] at ht
  · intro hpos
    have ht := hpos.conjTranspose_mul_mul_same hinj
    rwa [hJ, hcongr] at ht

theorem correctedCumulant_second_minor {C h : ℕ → ℝ}
    (hbridge : ∀ n, h n = (-1 : ℝ) ^ n * correctedCumulantEntry C n) :
    (hankelGram h 2).det = (3 * C 2 * C 6 - 10 * C 4 ^ 2) / 1440 := by
  rw [Matrix.det_fin_two]
  simp only [hankelGram_apply]
  change h 0 * h 2 - h 1 * h 1 = _
  rw [hbridge 0, hbridge 1, hbridge 2]
  norm_num [correctedCumulantEntry, Nat.factorial_succ]; ring

theorem correctedCumulant_consecutive_minor_pos_iff {C h : ℕ → ℝ}
    (hbridge : ∀ n, h n = (-1 : ℝ) ^ n * correctedCumulantEntry C n)
    (n : ℕ) :
    0 < h n * h (n + 2) - h (n + 1) ^ 2 ↔
    ((2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 5)) /
        ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)) * C (2 * n + 4) ^ 2 <
      C (2 * n + 2) * C (2 * n + 6) := by
  let k := 2 * n + 1
  let d : ℝ := k.factorial
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.factorial_pos k
  have hs (j : ℕ) : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n + 2) = 1 := by
    rw [pow_add, show (-1 : ℝ) ^ (2 : ℕ) = 1 by norm_num, mul_one, hs]
  have h₂ : ((k + 2).factorial : ℝ) = ((k : ℝ) + 1) * ((k : ℝ) + 2) * d := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    change ((↑k + 1 + 1 : ℝ) * ((↑k + 1 : ℝ) * d)) = _
    ring
  have h₄ : ((k + 4).factorial : ℝ) =
      ((k : ℝ) + 3) * ((k : ℝ) + 4) *
        (((k : ℝ) + 1) * ((k : ℝ) + 2)) * d := by
    rw [show k + 4 = ((k + 2) + 1) + 1 by omega, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [h₂]
    ring
  rw [hbridge n, hbridge (n + 1), hbridge (n + 2)]
  rw [show ((-1 : ℝ) ^ n * correctedCumulantEntry C n) *
      ((-1 : ℝ) ^ (n + 2) * correctedCumulantEntry C (n + 2)) =
      correctedCumulantEntry C n * correctedCumulantEntry C (n + 2) by
    calc
      _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ (n + 2)) *
          (correctedCumulantEntry C n * correctedCumulantEntry C (n + 2)) := by ring
      _ = _ := by rw [hsign, one_mul]]
  rw [mul_pow, pow_two ((-1 : ℝ) ^ (n + 1)), hs, one_mul]
  unfold correctedCumulantEntry
  rw [show 2 * (n + 2) + 2 = 2 * n + 6 by omega,
    show 2 * (n + 1) + 2 = 2 * n + 4 by omega,
    show 2 * (n + 2) + 1 = k + 4 by dsimp [k]; omega,
    show 2 * (n + 1) + 1 = k + 2 by dsimp [k]; omega,
    h₂, h₄]
  change 0 < C (2 * n + 2) / (2 * d) *
    (C (2 * n + 6) / (2 * (((k : ℝ) + 3) * ((k : ℝ) + 4) *
      (((k : ℝ) + 1) * ((k : ℝ) + 2)) * d))) -
    (C (2 * n + 4) / (2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * d))) ^ 2 ↔ _
  let a : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2)
  let b : ℝ := ((k : ℝ) + 3) * ((k : ℝ) + 4)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : b / a = ((2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 5)) /
      ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 3)) := by
    dsimp [a, b, k]
    push_cast
    ring
  rw [← hab]
  change 0 < C (2 * n + 2) / (2 * d) * (C (2 * n + 6) / (2 * (b * a * d))) -
    (C (2 * n + 4) / (2 * (a * d))) ^ 2 ↔ _
  have hfactor : 0 < 4 * b * a * d ^ 2 := by positivity
  rw [show C (2 * n + 2) / (2 * d) * (C (2 * n + 6) / (2 * (b * a * d))) -
      (C (2 * n + 4) / (2 * (a * d))) ^ 2 =
      (C (2 * n + 2) * C (2 * n + 6) - b / a * C (2 * n + 4) ^ 2) /
        (4 * b * a * d ^ 2) by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hd]; ring]
  rw [div_pos_iff_of_pos_right hfactor, sub_pos]

/-- Transfer the existing theta certificate through a proved analytic bridge.
This theorem has no assumption about the zero set. -/
theorem canonical_correctedCumulant_second_minor_pos {C : ℕ → ℝ}
    (hbridge : ∀ n, canonicalCompletedNativeLogDerivativeMoment n =
      (-1 : ℝ) ^ n * correctedCumulantEntry C n) :
    10 * C 4 ^ 2 < 3 * C 2 * C 6 := by
  have h := canonicalCompletedNativeHankel_two_det_pos
  rw [correctedCumulant_second_minor hbridge] at h
  linarith [(div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 1440)).mp h]

end

end CarrySelfAdjointOperator

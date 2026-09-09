import CarrySelfAdjointOperator.CompletedNativeAnalyticMomentGrowth
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# All-order finite-factor logarithmic ledger

The finite factors below are arbitrary complex algebraic parameters. They are
not declared to be native spectral data. The characteristic and its moments
are the existing completed-native objects. The quotient remainder is explicit
at every order, and no sign or vanishing condition is imposed on it.
-/

open scoped BigOperators
open Filter Topology

namespace CarrySelfAdjointOperator.AllOrderLogJet

noncomputable section
set_option autoImplicit false

variable {ι : Type*}

/-- The logarithm near a normalized unit has the expected logarithmic jet.
Its branch is controlled near 1 before any iterated differentiation. -/
theorem unit_logJet_succ {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 1) (m : ℕ) :
    iteratedDeriv (m + 1) (fun u => Complex.log (F u)) 0 =
      iteratedDeriv m (logDeriv F) 0 := by
  have hslit : ∀ᶠ u : ℂ in 𝓝 0, F u ∈ Complex.slitPlane :=
    hF.continuousAt.preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds (by simp [hF0]))
  have hd : deriv (fun u => Complex.log (F u)) =ᶠ[𝓝 0] logDeriv F := by
    filter_upwards [hF.eventually_analyticAt, hslit] with u hu hs
    exact (hu.differentiableAt.hasDerivAt.clog hs).deriv
  rw [iteratedDeriv_succ', hd.iteratedDeriv_eq]

/-- The normalized logarithmic jet transports through a product at every
positive order. This applies to analytic wheel/camera factors normalized to 1. -/
theorem unit_logJet_mul {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hF0 : F 0 = 1) (hG0 : G 0 = 1) (m : ℕ) :
    iteratedDeriv (m + 1) (fun u => Complex.log (F u * G u)) 0 =
      iteratedDeriv (m + 1) (fun u => Complex.log (F u)) 0 +
        iteratedDeriv (m + 1) (fun u => Complex.log (G u)) 0 := by
  have hFn : F 0 ≠ 0 := by simp [hF0]
  have hGn : G 0 ≠ 0 := by simp [hG0]
  have heq : logDeriv (fun u => F u * G u) =ᶠ[𝓝 0]
      (logDeriv F + logDeriv G) := by
    filter_upwards [hF.eventually_analyticAt, hG.eventually_analyticAt,
      hF.continuousAt.eventually_ne hFn, hG.continuousAt.eventually_ne hGn]
      with u hFu hGu hFnu hGnu
    exact logDeriv_mul u hFnu hGnu hFu.differentiableAt hGu.differentiableAt
  have hFG : AnalyticAt ℂ (fun u => F u * G u) 0 := by fun_prop
  rw [unit_logJet_succ hFG (by simp [hF0, hG0]),
    unit_logJet_succ hF hF0, unit_logJet_succ hG hG0, heq.iteratedDeriv_eq]
  exact iteratedDeriv_add (hF.deriv.div hF hFn).contDiffAt
    (hG.deriv.div hG hGn).contDiffAt

/-- The finite-factor logarithmic response near the normalized center. -/
theorem finiteFactor_logDeriv_eventually (S : Finset ι) (a : ι → ℂ) :
    logDeriv (fun u : ℂ => ∏ i ∈ S, (1 - a i * u)) =ᶠ[𝓝 0]
      (fun u => ∑ i ∈ S, -a i / (1 - a i * u)) := by
  have hnz : ∀ᶠ u : ℂ in 𝓝 0, ∀ i ∈ S, 1 - a i * u ≠ 0 := by
    apply (Filter.eventually_all_finset S).2
    intro i hi
    exact (by fun_prop : ContinuousAt (fun u : ℂ => 1 - a i * u) 0).eventually_ne
      (by simp)
  filter_upwards [hnz] with u hu
  rw [logDeriv_prod hu (fun i hi => by fun_prop)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [logDeriv_apply]
  congr 1
  simp

/-- Every derivative order is evaluated at once; no list of tested orders is used. -/
theorem finiteFactor_logDeriv_iterated (S : Finset ι) (a : ι → ℂ) (m : ℕ) :
    iteratedDeriv m (logDeriv (fun u : ℂ => ∏ i ∈ S, (1 - a i * u))) 0 =
      -(m.factorial : ℂ) * ∑ i ∈ S, a i ^ (m + 1) := by
  rw [(finiteFactor_logDeriv_eventually S a).iteratedDeriv_eq]
  rw [iteratedDeriv_fun_sum (fun i hi =>
    (by fun_prop (disch := simp) : AnalyticAt ℂ (fun u : ℂ => -a i / (1 - a i * u)) 0).contDiffAt)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have heq : (fun u : ℂ => -a i / (1 - a i * u)) =
      (fun u => -a i * ((-a i) * u + 1)⁻¹) := by
    ext u
    congr 1
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate,
    iter_deriv_inv_linear]
  simp only [mul_zero, zero_add, one_zpow, mul_one]
  rw [neg_pow (a i)]
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]
    simp
  calc
    -a i * ((-1) ^ m * (m.factorial : ℂ) * ((-1) ^ m * a i ^ m)) =
        -(m.factorial : ℂ) * a i ^ (m + 1) * ((-1) ^ m * (-1) ^ m) := by ring
    _ = _ := by rw [hsign, mul_one]

/-- All positive orders of the actual local logarithm of the finite product. -/
theorem finiteFactor_logJet_iterated (S : Finset ι) (a : ι → ℂ) (m : ℕ) :
    iteratedDeriv (m + 1)
        (fun u : ℂ => Complex.log (∏ i ∈ S, (1 - a i * u))) 0 =
      -(m.factorial : ℂ) * ∑ i ∈ S, a i ^ (m + 1) := by
  rw [unit_logJet_succ (by fun_prop) (by simp), finiteFactor_logDeriv_iterated]

/-- Division by a finite factor retains the exact analytic remainder germ. -/
theorem quotient_logDeriv_eventually (S : Finset ι) (a : ι → ℂ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0) :
    logDeriv (fun u => F u / ∏ i ∈ S, (1 - a i * u)) =ᶠ[𝓝 0]
      (fun u => logDeriv F u -
        logDeriv (fun v : ℂ => ∏ i ∈ S, (1 - a i * v)) u) := by
  have hP : AnalyticAt ℂ (fun u : ℂ => ∏ i ∈ S, (1 - a i * u)) 0 := by
    fun_prop
  filter_upwards [hF.eventually_analyticAt,
    hF.continuousAt.eventually_ne hF0, hP.eventually_analyticAt,
    hP.continuousAt.eventually_ne (show (∏ i ∈ S, (1 - a i * (0 : ℂ))) ≠ 0 by simp)] with u hFu hFnu hPu hPnu
  exact logDeriv_div u hFnu hPnu hFu.differentiableAt hPu.differentiableAt

/-- All-order finite-factor extraction with the quotient remainder still present. -/
theorem quotient_logDeriv_iterated (S : Finset ι) (a : ι → ℂ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hF0 : F 0 ≠ 0) (m : ℕ) :
    iteratedDeriv m (logDeriv (fun u => F u / ∏ i ∈ S, (1 - a i * u))) 0 =
      iteratedDeriv m (logDeriv F) 0 +
        (m.factorial : ℂ) * ∑ i ∈ S, a i ^ (m + 1) := by
  have hP : AnalyticAt ℂ (fun u : ℂ => ∏ i ∈ S, (1 - a i * u)) 0 := by
    fun_prop
  have hL : AnalyticAt ℂ (logDeriv F) 0 := hF.deriv.div hF hF0
  have hLP : AnalyticAt ℂ
      (logDeriv (fun u : ℂ => ∏ i ∈ S, (1 - a i * u))) 0 :=
    hP.deriv.div hP (by simp)
  rw [(quotient_logDeriv_eventually S a hF hF0).iteratedDeriv_eq]
  change iteratedDeriv m (logDeriv F - logDeriv (fun u : ℂ => ∏ i ∈ S, (1 - a i * u))) 0 = _
  rw [iteratedDeriv_sub hL.contDiffAt hLP.contDiffAt, finiteFactor_logDeriv_iterated]
  ring

/-- The existing native moments equal a finite power sum plus the exact
logarithmic response of the quotient. The finite parameters need not be real,
positive, or spectral; the formula supplies no positivity by itself. -/
theorem nativeMoment_eq_finiteFactors_add_remainder
    (S : Finset ι) (a : ι → ℂ) (m : ℕ) :
    (canonicalCompletedNativeLogDerivativeMoment m : ℂ) =
      (∑ i ∈ S, a i ^ (m + 1)) -
        iteratedDeriv m
          (logDeriv (fun u => completedNativeEvenCharacteristic u /
            ∏ i ∈ S, (1 - a i * u))) 0 / m.factorial := by
  have h := quotient_logDeriv_iterated S a
    completedNativeEvenCharacteristic_analyticAt
    completedNativeEvenCharacteristic_zero_ne_zero m
  have hresponse : completedNativeLogDerivative =
      -logDeriv completedNativeEvenCharacteristic := by
    ext u
    simp only [completedNativeLogDerivative, logDeriv_apply, Pi.neg_apply, neg_div]
  rw [← completedNativeLogDerivativeTaylorCoefficient_eq_canonical,
    completedNativeLogDerivativeTaylorCoefficient, hresponse, iteratedDeriv_neg, h]
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp
  ring

/-- Selecting direct neighbors must also preserve their reflected terms.
This ledger identity holds for every exponent, including zero. -/
theorem reciprocalLedger_split [DecidableEq ι]
    (S T : Finset ι) (hTS : T ⊆ S) (a : ℂ) (g : ι → ℂ) (m : ℕ) :
    (∑ i ∈ S, ((a - g i)⁻¹ ^ m + (a + g i)⁻¹ ^ m)) =
      (∑ i ∈ T, (a - g i)⁻¹ ^ m) +
        ((∑ i ∈ T, (a + g i)⁻¹ ^ m) +
          ∑ i ∈ S \ T, ((a - g i)⁻¹ ^ m + (a + g i)⁻¹ ^ m)) := by
  rw [← Finset.sum_sdiff hTS]
  simp only [Finset.sum_add_distrib]
  ring

/-- Orientation of the right neighbor is carried by the parity of the order. -/
theorem reciprocalGap_parity (a b : ℂ) (m : ℕ) :
    (a - b)⁻¹ ^ m = (-1 : ℂ) ^ m * (b - a)⁻¹ ^ m := by
  rw [show a - b = -(b - a) by ring, inv_neg, neg_pow]

/-- The two reflected terms omitted by the printed neighbor split have
strictly positive sum for positive real locations, in every order. -/
theorem reflectedNeighborCorrection_pos (a l r : ℝ)
    (ha : 0 < a) (hl : 0 < l) (hr : 0 < r) (m : ℕ) :
    0 < (a + l)⁻¹ ^ m + (a + r)⁻¹ ^ m := by positivity

/-- Exact order-six audit of the missing reflected terms in a finite example. -/
theorem reflectedNeighborCorrection_six :
    ((2 + 1 : ℚ)⁻¹ ^ 6 + (2 + 3 : ℚ)⁻¹ ^ 6) = 16354 / 11390625 := by
  norm_num

/-- Exact order-seven audit of the same ledger correction. -/
theorem reflectedNeighborCorrection_seven :
    ((2 + 1 : ℚ)⁻¹ ^ 7 + (2 + 3 : ℚ)⁻¹ ^ 7) = 80312 / 170859375 := by
  norm_num

end

end CarrySelfAdjointOperator.AllOrderLogJet

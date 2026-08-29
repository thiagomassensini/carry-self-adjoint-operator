import CarrySelfAdjointOperator.CompletedNativeTfvdRawAllOrderJetBridge
import CarrySelfAdjointOperator.CompletedNativeTfvdCoefficientJetHPCarrier
import Mathlib.Tactic

/-!
# All-order completion of the native TFVD Taylor coefficients

This module extends the ordinary and log-jet `l2` estimates to every raw
Taylor order.  The estimate is native: it is applied to the consecutive
slopes of `log(x)^p * x^(-1/2)` and does not use a Gram representation.
-/

open scoped Topology lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open Filter
open CPFormal.Analytic.Cp

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
attribute [local instance 10000] Complex.instNormedAddCommGroup

/-- A logarithmic power is bounded by an arbitrarily small positive power on
`[1, infinity)`.  The explicit constant is retained for later summability. -/
theorem real_log_pow_le_inv_pow_mul_rpow
    (order : ℕ) {x epsilon delta : ℝ}
    (hx : 1 ≤ x) (hepsilon : 0 < epsilon)
    (hexponent : epsilon * order ≤ delta) :
    Real.log x ^ order ≤
      (epsilon ^ order)⁻¹ * x ^ delta := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div hx0 hepsilon
  have hpow := pow_le_pow_left₀ hlog0 hlog order
  calc
    Real.log x ^ order ≤ (x ^ epsilon / epsilon) ^ order := hpow
    _ = (epsilon ^ order)⁻¹ * x ^ (epsilon * order) := by
      rw [div_pow, ← Real.rpow_mul_natCast hx0 epsilon order]
      ring
    _ ≤ (epsilon ^ order)⁻¹ * x ^ delta := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx hexponent)
        (inv_nonneg.mpr (pow_nonneg hepsilon.le order))

/-- Logarithmic power multiplying the native real Dirichlet amplitude. -/
def realLogPowerDirichletPower
    (order : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (Real.log x ^ order) • realDirichletPower s x

/-- Formal derivative of `realLogPowerDirichletPower`. -/
def realLogPowerDirichletPowerDeriv
    (order : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (((order : ℝ) * Real.log x ^ (order - 1) * x⁻¹) •
      realDirichletPower s x) +
    (Real.log x ^ order) • realDirichletPowerDeriv s x

theorem hasDerivAt_realLogPowerDirichletPower
    (order : ℕ) {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realLogPowerDirichletPower order s)
      (realLogPowerDirichletPowerDeriv order s x) x := by
  have hlog : HasDerivAt (fun y : ℝ => Real.log y ^ order)
      ((order : ℝ) * Real.log x ^ (order - 1) * x⁻¹) x := by
    simpa only [Pi.pow_apply, mul_assoc] using!
      (Real.hasDerivAt_log hx.ne').pow order
  simpa only [realLogPowerDirichletPower,
    realLogPowerDirichletPowerDeriv, add_comm] using!
      hlog.smul (hasDerivAt_realDirichletPower hs hx)

/-- Order-dependent exponent used to absorb every fixed logarithmic power. -/
def nativeAllOrderLogEpsilon (order : ℕ) : ℝ :=
  ((4 : ℝ) * (order + 1))⁻¹

theorem nativeAllOrderLogEpsilon_pos (order : ℕ) :
    0 < nativeAllOrderLogEpsilon order := by
  unfold nativeAllOrderLogEpsilon
  positivity

theorem nativeAllOrderLogEpsilon_mul_le_quarter (order : ℕ) :
    nativeAllOrderLogEpsilon order * order ≤ (1 / 4 : ℝ) := by
  unfold nativeAllOrderLogEpsilon
  have hden : 0 < (4 : ℝ) * (order + 1) := by positivity
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hden).2
  nlinarith

theorem nativeAllOrderLogEpsilon_mul_pred_le_quarter (order : ℕ) :
    nativeAllOrderLogEpsilon order * ((order - 1 : ℕ) : ℝ) ≤
      (1 / 4 : ℝ) := by
  have hpred : ((order - 1 : ℕ) : ℝ) ≤ order := by
    exact_mod_cast Nat.sub_le order 1
  exact (mul_le_mul_of_nonneg_left hpred
    (nativeAllOrderLogEpsilon_pos order).le).trans
      (nativeAllOrderLogEpsilon_mul_le_quarter order)

/-- Explicit constant in the all-order derivative majorant. -/
def nativeAllOrderLogDerivativeBound (order : ℕ) : ℝ :=
  (order : ℝ) *
      (nativeAllOrderLogEpsilon order ^ (order - 1))⁻¹ +
    (1 / 2 : ℝ) *
      (nativeAllOrderLogEpsilon order ^ order)⁻¹

theorem nativeAllOrderLogDerivativeBound_nonneg (order : ℕ) :
    0 ≤ nativeAllOrderLogDerivativeBound order := by
  have heps := nativeAllOrderLogEpsilon_pos order
  unfold nativeAllOrderLogDerivativeBound
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg order)
      (inv_nonneg.mpr (pow_nonneg heps.le _)))
    (mul_nonneg (by norm_num)
      (inv_nonneg.mpr (pow_nonneg heps.le _)))

/-- Uniform derivative bound for the order-`p` critical logarithmic
amplitude.  The exponent `-5/4` is independent of `p`. -/
theorem norm_realLogPowerDirichletPowerDeriv_half_le
    (order : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ‖realLogPowerDirichletPowerDeriv order (1 / 2 : ℂ) x‖ ≤
      nativeAllOrderLogDerivativeBound order * x ^ (-5 / 4 : ℝ) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hinv0 : 0 ≤ x⁻¹ := (inv_pos.mpr hxpos).le
  have hlogOrder := real_log_pow_le_inv_pow_mul_rpow order hx
    (nativeAllOrderLogEpsilon_pos order)
    (nativeAllOrderLogEpsilon_mul_le_quarter order)
  have hlogPred := real_log_pow_le_inv_pow_mul_rpow (order - 1) hx
    (nativeAllOrderLogEpsilon_pos order)
    (nativeAllOrderLogEpsilon_mul_pred_le_quarter order)
  have hpower :
      ‖realDirichletPower (1 / 2 : ℂ) x‖ = x ^ (-1 / 2 : ℝ) := by
    rw [norm_realDirichletPower (1 / 2 : ℂ) hxpos]
    norm_num
  have hpowerDeriv :
      ‖realDirichletPowerDeriv (1 / 2 : ℂ) x‖ =
        (1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ) := by
    rw [norm_realDirichletPowerDeriv (1 / 2 : ℂ) hxpos]
    norm_num
  have hnorm :
      ‖realLogPowerDirichletPowerDeriv order (1 / 2 : ℂ) x‖ ≤
        ((order : ℝ) * Real.log x ^ (order - 1) * x⁻¹) *
            x ^ (-1 / 2 : ℝ) +
          Real.log x ^ order *
            ((1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ)) := by
    unfold realLogPowerDirichletPowerDeriv
    calc
      _ ≤ ‖(((order : ℝ) * Real.log x ^ (order - 1) * x⁻¹) •
              realDirichletPower (1 / 2 : ℂ) x)‖ +
            ‖(Real.log x ^ order) •
              realDirichletPowerDeriv (1 / 2 : ℂ) x‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_smul, norm_smul, hpower, hpowerDeriv]
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg, abs_of_nonneg]
        · positivity
        · positivity
  calc
    _ ≤ ((order : ℝ) *
            ((nativeAllOrderLogEpsilon order ^ (order - 1))⁻¹ *
              x ^ (1 / 4 : ℝ)) * x⁻¹) * x ^ (-1 / 2 : ℝ) +
          ((nativeAllOrderLogEpsilon order ^ order)⁻¹ *
            x ^ (1 / 4 : ℝ)) *
              ((1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ)) := by
      exact hnorm.trans (add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogPred (by positivity)) hinv0)
          (Real.rpow_nonneg hxpos.le _))
        (mul_le_mul_of_nonneg_right hlogOrder (by positivity)))
    _ = nativeAllOrderLogDerivativeBound order * x ^ (-5 / 4 : ℝ) := by
      have hinv : x⁻¹ = x ^ (-1 : ℝ) := (Real.rpow_neg_one x).symm
      have hcombine₁ :
          x ^ (1 / 4 : ℝ) * x ^ (-1 : ℝ) * x ^ (-1 / 2 : ℝ) =
            x ^ (-5 / 4 : ℝ) := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        congr 1
        ring
      have hcombine₂ :
          x ^ (1 / 4 : ℝ) * x ^ (-3 / 2 : ℝ) =
            x ^ (-5 / 4 : ℝ) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      rw [hinv]
      calc
        _ = ((order : ℝ) *
              (nativeAllOrderLogEpsilon order ^ (order - 1))⁻¹) *
                (x ^ (1 / 4 : ℝ) * x ^ (-1 : ℝ) *
                  x ^ (-1 / 2 : ℝ)) +
            ((1 / 2 : ℝ) *
              (nativeAllOrderLogEpsilon order ^ order)⁻¹) *
                (x ^ (1 / 4 : ℝ) * x ^ (-3 / 2 : ℝ)) := by ring
        _ = ((order : ℝ) *
              (nativeAllOrderLogEpsilon order ^ (order - 1))⁻¹) *
                x ^ (-5 / 4 : ℝ) +
            ((1 / 2 : ℝ) *
              (nativeAllOrderLogEpsilon order ^ order)⁻¹) *
                x ^ (-5 / 4 : ℝ) := by rw [hcombine₁, hcombine₂]
        _ = _ := by
          unfold nativeAllOrderLogDerivativeBound
          ring

/-- Consecutive critical logarithmic amplitudes have a summable all-order
slope bound. -/
theorem norm_realLogPowerDirichletPower_succ_sub_half_le
    (order n : ℕ) :
    ‖realLogPowerDirichletPower order (1 / 2 : ℂ)
          ((n + 2 : ℕ) : ℝ) -
        realLogPowerDirichletPower order (1 / 2 : ℂ)
          ((n + 1 : ℕ) : ℝ)‖ ≤
      nativeAllOrderLogDerivativeBound order *
        ((n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  let lower : ℝ := ((n + 1 : ℕ) : ℝ)
  let upper : ℝ := ((n + 2 : ℕ) : ℝ)
  have hlower : 1 ≤ lower := by
    dsimp [lower]
    norm_cast
    omega
  have hlowerPos : 0 < lower := zero_lt_one.trans_le hlower
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    norm_cast
    omega
  have hlowerMem : lower ∈ Set.Ici lower := Set.mem_Ici.mpr le_rfl
  have hupperMem : upper ∈ Set.Ici lower := Set.mem_Ici.mpr hlowerUpper
  have hderiv :
      ∀ x, x ∈ Set.Ici lower →
        HasDerivWithinAt (realLogPowerDirichletPower order (1 / 2 : ℂ))
          (realLogPowerDirichletPowerDeriv order (1 / 2 : ℂ) x)
          (Set.Ici lower) x := by
    intro x hx
    exact (hasDerivAt_realLogPowerDirichletPower order (by norm_num)
      (hlowerPos.trans_le hx)).hasDerivWithinAt
  have hbound :
      ∀ x, x ∈ Set.Ici lower →
        ‖realLogPowerDirichletPowerDeriv order (1 / 2 : ℂ) x‖ ≤
          nativeAllOrderLogDerivativeBound order *
            lower ^ (-5 / 4 : ℝ) := by
    intro x hx
    exact (norm_realLogPowerDirichletPowerDeriv_half_le order
      (hlower.trans hx)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hlowerPos hx (by norm_num))
          (nativeAllOrderLogDerivativeBound_nonneg order))
  have hlip :=
    (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound hlowerMem hupperMem
  have hstep : upper - lower = 1 := by
    dsimp [upper, lower]
    norm_num
  change
    ‖realLogPowerDirichletPower order (1 / 2 : ℂ) upper -
        realLogPowerDirichletPower order (1 / 2 : ℂ) lower‖ ≤
      nativeAllOrderLogDerivativeBound order *
        lower ^ (-5 / 4 : ℝ)
  calc
    _ ≤ (nativeAllOrderLogDerivativeBound order *
          lower ^ (-5 / 4 : ℝ)) * ‖upper - lower‖ := hlip
    _ = _ := by rw [hstep, norm_one, mul_one]

/-- The raw Taylor coefficient is exactly the consecutive logarithmic
amplitude slope, with the native orbit factor and factorial normalization. -/
theorem nativeDirichletSlopeTaylorCoefficient_eq_logPowerSlope
    (order n : ℕ) :
    nativeDirichletSlopeTaylorCoefficient order n =
      ((-Complex.I) ^ order / (order.factorial : ℂ)) *
        (realLogPowerDirichletPower order (1 / 2 : ℂ)
            ((n + 2 : ℕ) : ℝ) -
          realLogPowerDirichletPower order (1 / 2 : ℂ)
            ((n + 1 : ℕ) : ℝ)) := by
  unfold nativeDirichletSlopeTaylorCoefficient
    nativeCriticalDirichletAmplitude realLogPowerDirichletPower
    realDirichletPower natDirichletTerm dirichletTerm
  push_cast
  simp only [Complex.real_smul, Complex.ofReal_pow]
  ring

/-- Explicit norm majorant for one raw Taylor slope coefficient. -/
def nativeAllOrderTaylorSlopeBound (order : ℕ) : ℝ :=
  ‖((-Complex.I) ^ order / (order.factorial : ℂ))‖ *
    nativeAllOrderLogDerivativeBound order

theorem nativeAllOrderTaylorSlopeBound_nonneg (order : ℕ) :
    0 ≤ nativeAllOrderTaylorSlopeBound order := by
  exact mul_nonneg (norm_nonneg _)
    (nativeAllOrderLogDerivativeBound_nonneg order)

theorem norm_nativeDirichletSlopeTaylorCoefficient_le
    (order n : ℕ) :
    ‖nativeDirichletSlopeTaylorCoefficient order n‖ ≤
      nativeAllOrderTaylorSlopeBound order *
        ((n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
  rw [nativeDirichletSlopeTaylorCoefficient_eq_logPowerSlope, norm_mul]
  simpa [nativeAllOrderTaylorSlopeBound, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (norm_realLogPowerDirichletPower_succ_sub_half_le order n)
      (show 0 ≤ ‖((-Complex.I) ^ order /
        (order.factorial : ℂ))‖ from norm_nonneg _)

/-- Every raw Taylor slope family is absolutely summable. -/
theorem summable_norm_nativeDirichletSlopeTaylorCoefficient
    (order : ℕ) :
    Summable (fun n : ℕ =>
      ‖nativeDirichletSlopeTaylorCoefficient order n‖) := by
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
    have h := hbase.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [Function.comp_def] using h
  have hmajorant := hshift.mul_left (nativeAllOrderTaylorSlopeBound order)
  exact hmajorant.of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_nativeDirichletSlopeTaylorCoefficient_le order n

/-- Absolute summability promotes every raw Taylor coefficient family to
the common vertical `l2` carrier. -/
theorem nativeDirichletSlopeTaylorCoefficient_memℓp_two
    (order : ℕ) :
    Memℓp (nativeDirichletSlopeTaylorCoefficient order) 2 := by
  have hmemOne :
      Memℓp (nativeDirichletSlopeTaylorCoefficient order) 1 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    simpa using summable_norm_nativeDirichletSlopeTaylorCoefficient order
  exact hmemOne.of_exponent_ge (by norm_num)

/-- Canonical completed raw Taylor vector of order `p`. -/
def canonicalCompletedNativeTfvdTaylorCoefficientState
    (order : ℕ) : CarryVerticalL2 :=
  ⟨nativeDirichletSlopeTaylorCoefficient order,
    nativeDirichletSlopeTaylorCoefficient_memℓp_two order⟩

@[simp] theorem canonicalCompletedNativeTfvdTaylorCoefficientState_apply
    (order n : ℕ) :
    canonicalCompletedNativeTfvdTaylorCoefficientState order n =
      nativeDirichletSlopeTaylorCoefficient order n :=
  rfl

/-- The logarithmic channel at order `p` is the next ordinary raw Taylor
coefficient with the exact native shift factor. -/
theorem nativeLogDirichletSlopeTaylorCoefficient_eq_succ
    (order n : ℕ) :
    nativeLogDirichletSlopeTaylorCoefficient order n =
      Complex.I * (order + 1 : ℕ) *
        nativeDirichletSlopeTaylorCoefficient (order + 1) n := by
  unfold nativeLogDirichletSlopeTaylorCoefficient
    nativeDirichletSlopeTaylorCoefficient
  simp only [mul_pow]
  rw [Nat.factorial_succ]
  simp only [pow_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]
  ring_nf
  all_goals simp [Complex.I_sq, sub_eq_add_neg]

/-- Completed logarithmic-channel Taylor vector, derived from the same raw
ordinary family rather than completed separately. -/
def canonicalCompletedNativeTfvdLogTaylorCoefficientState
    (order : ℕ) : CarryVerticalL2 :=
  (Complex.I * (order + 1 : ℕ)) •
    canonicalCompletedNativeTfvdTaylorCoefficientState (order + 1)

@[simp] theorem canonicalCompletedNativeTfvdLogTaylorCoefficientState_apply
    (order n : ℕ) :
    canonicalCompletedNativeTfvdLogTaylorCoefficientState order n =
      nativeLogDirichletSlopeTaylorCoefficient order n := by
  simp only [canonicalCompletedNativeTfvdLogTaylorCoefficientState,
    lp.coeFn_smul, Pi.smul_apply,
    canonicalCompletedNativeTfvdTaylorCoefficientState_apply]
  exact (nativeLogDirichletSlopeTaylorCoefficient_eq_succ order n).symm

/-- Initial prefix of the completed raw Taylor vector. -/
def canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState
    (order N : ℕ) : CarryVerticalL2 :=
  finiteSlopeCoefficientState
    (fun i : Fin N => nativeDirichletSlopeTaylorCoefficient order i.val)

theorem canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState_eq_sum_single
    (order N : ℕ) :
    canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState order N =
      ∑ n ∈ Finset.range N,
        lp.single 2 n (nativeDirichletSlopeTaylorCoefficient order n) := by
  ext k
  by_cases hk : k < N
  · rw [canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState,
      finiteSlopeCoefficientState_apply_of_lt _ hk]
    simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
    rw [Finset.sum_pi_single]
    simp [hk]
  · rw [canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState,
      finiteSlopeCoefficientState_apply_of_le _ (Nat.le_of_not_gt hk)]
    simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
    rw [Finset.sum_pi_single]
    simp [hk]

/-- The natural raw Taylor prefixes converge in `l2` for every order. -/
theorem canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState_tendsto
    (order : ℕ) :
    Tendsto
      (canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState order)
      atTop
      (nhds (canonicalCompletedNativeTfvdTaylorCoefficientState order)) := by
  let state := canonicalCompletedNativeTfvdTaylorCoefficientState order
  have hsum :
      HasSum (fun n : ℕ => lp.single 2 n (state n)) state :=
    lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) state
  have hpartial := hsum.summable.tendsto_sum_tsum_nat
  have hlimit : (∑' n : ℕ, lp.single 2 n (state n)) = state :=
    hsum.tsum_eq
  rw [hlimit] at hpartial
  have hfunctions :
      canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState order =
        fun N : ℕ => ∑ n ∈ Finset.range N,
          lp.single 2 n (state n) := by
    funext N
    rw [canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState_eq_sum_single]
    rfl
  rw [hfunctions]
  exact hpartial

/-- The geometrically complete camera prefixes converge to the same
all-order Taylor vector. -/
theorem canonicalCompletedC3DirichletGradientTaylorPrefix_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (order : ℕ) :
    Tendsto
      (fun cutoff : ℕ =>
        let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
        finiteSlopeCoefficientSynthesisLinearMap N
          (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
            base cutoff order))
      atTop
      (nhds (canonicalCompletedNativeTfvdTaylorCoefficientState order)) := by
  have hprefix :=
    (canonicalCompletedNativeTfvdTaylorCoefficientNatPrefixState_tendsto order).comp
      (finiteCameraWindow_add_one_tendsto_atTop hbase)
  exact hprefix

@[simp] theorem canonicalCompletedNativeTfvdTaylorCoefficientState_zero :
    canonicalCompletedNativeTfvdTaylorCoefficientState 0 =
      canonicalCompletedC3DirichletGradientState
        (1 / 2 : ℂ) (by norm_num) := by
  ext n
  exact nativeDirichletSlopeTaylorCoefficient_zero n

@[simp] theorem canonicalCompletedNativeTfvdTaylorCoefficientState_one :
    canonicalCompletedNativeTfvdTaylorCoefficientState 1 =
      (-Complex.I) • canonicalCompletedC3LogJetState
        (1 / 2 : ℂ) (by norm_num) := by
  ext n
  simp only [canonicalCompletedNativeTfvdTaylorCoefficientState_apply,
    lp.coeFn_smul, Pi.smul_apply,
    canonicalCompletedC3LogJetState_apply]
  exact nativeDirichletSlopeTaylorCoefficient_one n

/-- At every geometric cutoff, the channel-complete causal factorization
converges in the step variable to the exact Taylor prefix.  The boundary
return is retained in the sequence. -/
theorem canonicalCompletedC3DirichletGradient_response_add_boundary_rawJet_tendsto
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (cutoff order : ℕ) :
    let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    Tendsto
      (fun k : ℕ =>
        completedGreenForwardDifferenceJet
            (fun z => canonicalCompletedC3DirichletGradientBracketGreenResponse
              base cutoff (operatorHeightParameter z))
            (canonicalGreenJetStep k) order +
          finiteWeightedSlopeBoundaryReturnLinearMap
              (canonicalBR2CarryAmplitudeRatio base)
              (canonicalBR2CarryAmplitudeRatio_pos hbase).le
              (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
            (canonicalCompletedC3DirichletGradientCoefficientRawJet
              base cutoff k order))
      atTop
      (nhds (finiteSlopeCoefficientSynthesisLinearMap N
        (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
          base cutoff order))) := by
  dsimp only
  have hprefix :=
    canonicalCompletedC3DirichletGradientPrefix_rawJet_tendsto_taylor
      base cutoff order
  apply hprefix.congr'
  filter_upwards with k
  exact (canonicalCompletedC3DirichletGradient_response_add_boundary_rawJet
    hbase cutoff k order).symm

/-- Complete two-stage all-order TFVD limit: first the finite-difference step
tends to zero with response and boundary together, then the geometric cutoff
tends to the canonical completed Taylor vector. -/
theorem canonicalCompletedNativeTfvdTaylorCoefficient_twoStageLimit
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (order : ℕ) :
    (∀ cutoff : ℕ,
      let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
      Tendsto
        (fun k : ℕ =>
          completedGreenForwardDifferenceJet
              (fun z => canonicalCompletedC3DirichletGradientBracketGreenResponse
                base cutoff (operatorHeightParameter z))
              (canonicalGreenJetStep k) order +
            finiteWeightedSlopeBoundaryReturnLinearMap
                (canonicalBR2CarryAmplitudeRatio base)
                (canonicalBR2CarryAmplitudeRatio_pos hbase).le
                (canonicalBR2CarryAmplitudeRatio_lt_one hbase) N
              (canonicalCompletedC3DirichletGradientCoefficientRawJet
                base cutoff k order))
        atTop
        (nhds (finiteSlopeCoefficientSynthesisLinearMap N
          (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
            base cutoff order)))) ∧
      Tendsto
        (fun cutoff : ℕ =>
          let N := NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
          finiteSlopeCoefficientSynthesisLinearMap N
            (canonicalCompletedC3DirichletGradientTaylorCoefficientPrefix
              base cutoff order))
        atTop
        (nhds (canonicalCompletedNativeTfvdTaylorCoefficientState order)) := by
  exact ⟨fun cutoff =>
    canonicalCompletedC3DirichletGradient_response_add_boundary_rawJet_tendsto
      hbase cutoff order,
    canonicalCompletedC3DirichletGradientTaylorPrefix_tendsto hbase order⟩

/-! ## Enriched all-order carrier and independence -/

/-- Forgetful coordinate readout from the completed vertical `l2` carrier. -/
def carryVerticalL2CoordinateReadout :
    CarryVerticalL2 →ₗ[ℂ] (ℕ → ℂ) where
  toFun state n := state n
  map_add' x y := by
    funext n
    rfl
  map_smul' c x := by
    funext n
    rfl

theorem carryVerticalL2CoordinateReadout_injective :
    Function.Injective carryVerticalL2CoordinateReadout := by
  intro x y hxy
  ext n
  exact congrFun hxy n

theorem carryVerticalL2CoordinateReadout_taylorOdd
    (order : ℕ) :
    carryVerticalL2CoordinateReadout
        (canonicalCompletedNativeTfvdTaylorCoefficientState
          (2 * order + 1)) =
      nativeOrdinaryOddJetScale order • nativeOddLogPowerSlopeJet order := by
  funext n
  change nativeDirichletSlopeTaylorCoefficient (2 * order + 1) n =
    nativeOrdinaryOddJetScale order * nativeOddLogPowerSlopeJet order n
  exact nativeDirichletSlopeTaylorCoefficient_odd_eq order n

theorem carryVerticalL2CoordinateReadout_logTaylorEven
    (order : ℕ) :
    carryVerticalL2CoordinateReadout
        (canonicalCompletedNativeTfvdLogTaylorCoefficientState
          (2 * order)) =
      nativeLogJetEvenScale order • nativeOddLogPowerSlopeJet order := by
  funext n
  change canonicalCompletedNativeTfvdLogTaylorCoefficientState
      (2 * order) n =
    (nativeLogJetEvenScale order • nativeOddLogPowerSlopeJet order) n
  rw [canonicalCompletedNativeTfvdLogTaylorCoefficientState_apply]
  change nativeLogDirichletSlopeTaylorCoefficient (2 * order) n =
    nativeLogJetEvenScale order * nativeOddLogPowerSlopeJet order n
  exact nativeLogDirichletSlopeTaylorCoefficient_even_eq order n

/-- The completed odd ordinary Taylor vectors remain independent.  The proof
uses their exact coordinate Vandermonde image, not convergence of finite
independent families. -/
theorem canonicalCompletedNativeTfvdTaylorOdd_linearIndependent :
    LinearIndependent ℂ (fun order : ℕ =>
      canonicalCompletedNativeTfvdTaylorCoefficientState
        (2 * order + 1)) := by
  let scaleUnit : ℕ → ℂˣ := fun order =>
    Units.mk0 (nativeOrdinaryOddJetScale order)
      (nativeOrdinaryOddJetScale_ne_zero order)
  have hscaled : LinearIndependent ℂ
      (fun order : ℕ => nativeOrdinaryOddJetScale order •
        nativeOddLogPowerSlopeJet order) := by
    have hunit :=
      nativeOddLogPowerSlopeJet_linearIndependent.units_smul scaleUnit
    change LinearIndependent ℂ
      (fun order : ℕ => (scaleUnit order : ℂ) •
        nativeOddLogPowerSlopeJet order) at hunit
    simpa only [scaleUnit, Units.val_mk0] using hunit
  apply LinearIndependent.of_comp carryVerticalL2CoordinateReadout
  have himage :
      carryVerticalL2CoordinateReadout ∘
          (fun order : ℕ =>
            canonicalCompletedNativeTfvdTaylorCoefficientState
              (2 * order + 1)) =
        fun order : ℕ => nativeOrdinaryOddJetScale order •
          nativeOddLogPowerSlopeJet order := by
    funext order
    exact carryVerticalL2CoordinateReadout_taylorOdd order
  rw [himage]
  exact hscaled

/-- The completed even logarithmic Taylor vectors are independent through
the same all-order Vandermonde family. -/
theorem canonicalCompletedNativeTfvdLogTaylorEven_linearIndependent :
    LinearIndependent ℂ (fun order : ℕ =>
      canonicalCompletedNativeTfvdLogTaylorCoefficientState
        (2 * order)) := by
  let scaleUnit : ℕ → ℂˣ := fun order =>
    Units.mk0 (nativeLogJetEvenScale order)
      (nativeLogJetEvenScale_ne_zero order)
  have hscaled : LinearIndependent ℂ
      (fun order : ℕ => nativeLogJetEvenScale order •
        nativeOddLogPowerSlopeJet order) := by
    have hunit :=
      nativeOddLogPowerSlopeJet_linearIndependent.units_smul scaleUnit
    change LinearIndependent ℂ
      (fun order : ℕ => (scaleUnit order : ℂ) •
        nativeOddLogPowerSlopeJet order) at hunit
    simpa only [scaleUnit, Units.val_mk0] using hunit
  apply LinearIndependent.of_comp carryVerticalL2CoordinateReadout
  have himage :
      carryVerticalL2CoordinateReadout ∘
          (fun order : ℕ =>
            canonicalCompletedNativeTfvdLogTaylorCoefficientState
              (2 * order)) =
        fun order : ℕ => nativeLogJetEvenScale order •
          nativeOddLogPowerSlopeJet order := by
    funext order
    exact carryVerticalL2CoordinateReadout_logTaylorEven order
  rw [himage]
  exact hscaled

/-- Ordinary and logarithmic channels retained orthogonally at every raw
Taylor order. -/
abbrev CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
  WithLp 2 (CarryVerticalL2 × CarryVerticalL2)

def canonicalCompletedNativeTfvdEnrichedTaylorRawJet
    (order : ℕ) : CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
  WithLp.toLp 2
    (canonicalCompletedNativeTfvdTaylorCoefficientState order,
      canonicalCompletedNativeTfvdLogTaylorCoefficientState order)

@[simp] theorem canonicalCompletedNativeTfvdEnrichedTaylorRawJet_fst
    (order : ℕ) :
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet order).fst =
      canonicalCompletedNativeTfvdTaylorCoefficientState order :=
  rfl

@[simp] theorem canonicalCompletedNativeTfvdEnrichedTaylorRawJet_snd
    (order : ℕ) :
    (canonicalCompletedNativeTfvdEnrichedTaylorRawJet order).snd =
      canonicalCompletedNativeTfvdLogTaylorCoefficientState order :=
  rfl

/-- Odd independence of the enriched raw family is read from its ordinary
channel. -/
theorem canonicalCompletedNativeTfvdEnrichedTaylorOdd_linearIndependent :
    LinearIndependent ℂ (fun order : ℕ =>
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet
        (2 * order + 1)) := by
  apply LinearIndependent.of_comp
    (WithLp.fstL 2 ℂ CarryVerticalL2 CarryVerticalL2).toLinearMap
  have himage :
      (WithLp.fstL 2 ℂ CarryVerticalL2 CarryVerticalL2).toLinearMap ∘
          (fun order : ℕ =>
            canonicalCompletedNativeTfvdEnrichedTaylorRawJet
              (2 * order + 1)) =
        fun order : ℕ =>
          canonicalCompletedNativeTfvdTaylorCoefficientState
            (2 * order + 1) := by
    funext order
    rfl
  rw [himage]
  exact canonicalCompletedNativeTfvdTaylorOdd_linearIndependent

/-- Even independence of the enriched raw family is read from its retained
logarithmic channel. -/
theorem canonicalCompletedNativeTfvdEnrichedTaylorEven_linearIndependent :
    LinearIndependent ℂ (fun order : ℕ =>
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet
        (2 * order)) := by
  apply LinearIndependent.of_comp
    (WithLp.sndL 2 ℂ CarryVerticalL2 CarryVerticalL2).toLinearMap
  have himage :
      (WithLp.sndL 2 ℂ CarryVerticalL2 CarryVerticalL2).toLinearMap ∘
          (fun order : ℕ =>
            canonicalCompletedNativeTfvdEnrichedTaylorRawJet
              (2 * order)) =
        fun order : ℕ =>
          canonicalCompletedNativeTfvdLogTaylorCoefficientState
            (2 * order) := by
    funext order
    rfl
  rw [himage]
  exact canonicalCompletedNativeTfvdLogTaylorEven_linearIndependent

/-- Once the concrete enriched Taylor Gram satisfies the already proved
division-free coefficient recurrence, no further carrier or independence
premise remains: the real HP certificate is obtained directly. -/
theorem completedNativeRealHPCarrierCertificate_of_enrichedTfvdTaylorEquation
    (hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      canonicalCompletedNativeTfvdEnrichedTaylorRawJet) :
    letI : InnerProductSpace ℝ
        CanonicalCompletedNativeTfvdEnrichedTaylorCarrier :=
      InnerProductSpace.rclikeToReal ℂ
        CanonicalCompletedNativeTfvdEnrichedTaylorCarrier
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet
        canonicalCompletedNativeTfvdEnrichedTaylorRawJet) := by
  exact completedNativeRealHPCarrierCertificate_of_vectorCoefficientEquation
    hcoeff
    canonicalCompletedNativeTfvdEnrichedTaylorEven_linearIndependent
    canonicalCompletedNativeTfvdEnrichedTaylorOdd_linearIndependent

end

end CarrySelfAdjointOperator

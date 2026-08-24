import CPFormal.Analytic.CpTfvdSeededReconstructionBridgeProbe
import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit

/-!
# Completed C3 all-cutoff Hilbert state

The ordinary Dirichlet-gradient and logarithmic companion channels define
separate vectors in `ℓ²(ℕ, ℂ)` whenever `0 < re(s)`. Their native finite C3
prefixes converge in norm to the corresponding completed vectors.

The final product carrier keeps both channels separate. In particular, no
real-part projection or scalar boundary readout is applied here.
-/

open scoped Topology BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal
attribute [local instance 10000] Complex.instNormedAddCommGroup

theorem summable_norm_positiveDirichletGradient
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖positiveDirichletGradient s n‖) := by
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-s.re - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    have h := hbase.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [Function.comp_def] using h
  have hmajorant := hshift.mul_left ‖s‖
  exact hmajorant.of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_positiveDirichletGradient_le hs n

theorem positiveDirichletGradient_memℓp_two
    {s : ℂ} (hs : 0 < s.re) :
    Memℓp (fun n : ℕ => positiveDirichletGradient s n) 2 := by
  have hmemOne :
      Memℓp (fun n : ℕ => positiveDirichletGradient s n) 1 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    simpa using summable_norm_positiveDirichletGradient hs
  exact hmemOne.of_exponent_ge (by norm_num)

def canonicalCompletedC3DirichletGradientState
    (s : ℂ) (hs : 0 < s.re) : CarryVerticalL2 :=
  ⟨fun n : ℕ => positiveDirichletGradient s n,
    positiveDirichletGradient_memℓp_two hs⟩

@[simp] theorem canonicalCompletedC3DirichletGradientState_apply
    (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    canonicalCompletedC3DirichletGradientState s hs n =
      positiveDirichletGradient s n :=
  rfl

def canonicalCompletedC3DirichletGradientPrefixState
    (s : ℂ) (N : ℕ) : CarryVerticalL2 :=
  nativeGpreCanonicalVerticalRealization
    (c2DirichletGradientPrefixCore s N)

@[simp] theorem canonicalCompletedC3DirichletGradientPrefixState_apply
    (s : ℂ) (N n : ℕ) :
    canonicalCompletedC3DirichletGradientPrefixState s N n =
      if n < N then positiveDirichletGradient s n else 0 := by
  simp [canonicalCompletedC3DirichletGradientPrefixState]

theorem canonicalCompletedC3DirichletGradientPrefixState_eq_sum_single
    (s : ℂ) (N : ℕ) :
    canonicalCompletedC3DirichletGradientPrefixState s N =
      ∑ n ∈ Finset.range N,
        lp.single 2 n (positiveDirichletGradient s n) := by
  ext k
  rw [canonicalCompletedC3DirichletGradientPrefixState_apply]
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
  rw [Finset.sum_pi_single]
  by_cases hk : k < N <;> simp [hk]

theorem canonicalCompletedC3DirichletGradientPrefixState_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ => canonicalCompletedC3DirichletGradientPrefixState s N)
      atTop
      (nhds (canonicalCompletedC3DirichletGradientState s hs)) := by
  let f := canonicalCompletedC3DirichletGradientState s hs
  have hsum :
      HasSum (fun n : ℕ => lp.single 2 n (f n)) f :=
    lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
  have hpartial := hsum.summable.tendsto_sum_tsum_nat
  have hlimit : (∑' n : ℕ, lp.single 2 n (f n)) = f := hsum.tsum_eq
  rw [hlimit] at hpartial
  have hfunctions :
      (fun N : ℕ => canonicalCompletedC3DirichletGradientPrefixState s N) =
        (fun N : ℕ => ∑ n ∈ Finset.range N, lp.single 2 n (f n)) := by
    funext N
    rw [canonicalCompletedC3DirichletGradientPrefixState_eq_sum_single]
    rfl
  rw [hfunctions]
  exact hpartial

/-! ## Completed logarithmic companion -/

def realLogDirichletPower (s : ℂ) (x : ℝ) : ℂ :=
  Real.log x • realDirichletPower s x

def realLogDirichletPowerDeriv (s : ℂ) (x : ℝ) : ℂ :=
  Real.log x • realDirichletPowerDeriv s x +
    x⁻¹ • realDirichletPower s x

theorem hasDerivAt_realLogDirichletPower
    {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realLogDirichletPower s)
      (realLogDirichletPowerDeriv s x) x := by
  simpa only [realLogDirichletPower, realLogDirichletPowerDeriv] using!
    (Real.hasDerivAt_log hx.ne').smul
      (hasDerivAt_realDirichletPower hs hx)

theorem norm_realDirichletPower
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖realDirichletPower s x‖ = x ^ (-s.re) := by
  simpa [realDirichletPower] using
    (Complex.norm_cpow_eq_rpow_re_of_pos hx (-s))

theorem norm_realLogDirichletPowerDeriv_le
    {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖realLogDirichletPowerDeriv s x‖ ≤
      (‖s‖ / (s.re / 2) + 1) * x ^ (-s.re / 2 - 1) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heps : 0 < s.re / 2 := by linarith
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog := Real.log_le_rpow_div (le_of_lt hxpos) heps
  have hpownonneg : 0 ≤ x ^ (-s.re - 1) :=
    Real.rpow_nonneg (le_of_lt hxpos) _
  have hfirst :
      Real.log x * (‖s‖ * x ^ (-s.re - 1)) ≤
        (‖s‖ / (s.re / 2)) * x ^ (-s.re / 2 - 1) := by
    calc
      Real.log x * (‖s‖ * x ^ (-s.re - 1)) ≤
          (x ^ (s.re / 2) / (s.re / 2)) *
            (‖s‖ * x ^ (-s.re - 1)) :=
        mul_le_mul_of_nonneg_right hlog
          (mul_nonneg (norm_nonneg _) hpownonneg)
      _ = (‖s‖ / (s.re / 2)) * x ^ (-s.re / 2 - 1) := by
        rw [show -s.re / 2 - 1 = s.re / 2 + (-s.re - 1) by ring,
          Real.rpow_add hxpos]
        ring
  have hsecond :
      x ^ (-s.re - 1) ≤ x ^ (-s.re / 2 - 1) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc
    ‖realLogDirichletPowerDeriv s x‖ ≤
        ‖Real.log x • realDirichletPowerDeriv s x‖ +
          ‖x⁻¹ • realDirichletPower s x‖ := by
      exact norm_add_le _ _
    _ = Real.log x * (‖s‖ * x ^ (-s.re - 1)) +
        x ^ (-s.re - 1) := by
      rw [norm_smul, norm_smul,
        norm_realDirichletPowerDeriv s hxpos,
        norm_realDirichletPower s hxpos]
      rw [Real.norm_eq_abs, abs_of_nonneg hlognonneg,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
      rw [← Real.rpow_neg_one x]
      rw [← Real.rpow_add hxpos]
      ring_nf
    _ ≤ (‖s‖ / (s.re / 2)) * x ^ (-s.re / 2 - 1) +
        x ^ (-s.re / 2 - 1) := add_le_add hfirst hsecond
    _ = (‖s‖ / (s.re / 2) + 1) * x ^ (-s.re / 2 - 1) := by
      ring

theorem norm_realLogDirichletPower_succ_sub_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖realLogDirichletPower s ((n + 2 : ℕ) : ℝ) -
        realLogDirichletPower s ((n + 1 : ℕ) : ℝ)‖ ≤
      (‖s‖ / (s.re / 2) + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1) := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  let lower : ℝ := ((n + 1 : ℕ) : ℝ)
  let upper : ℝ := ((n + 2 : ℕ) : ℝ)
  have hlower : 1 ≤ lower := by
    dsimp [lower]
    norm_cast
    omega
  have hlowerPos : 0 < lower := lt_of_lt_of_le zero_lt_one hlower
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    norm_cast
    omega
  have hlowerMem : lower ∈ Set.Ici lower := Set.mem_Ici.mpr le_rfl
  have hupperMem : upper ∈ Set.Ici lower := Set.mem_Ici.mpr hlowerUpper
  have hcoefficient : 0 ≤ ‖s‖ / (s.re / 2) + 1 := by positivity
  have hderiv :
      ∀ x, x ∈ Set.Ici lower →
        HasDerivWithinAt (realLogDirichletPower s)
          (realLogDirichletPowerDeriv s x) (Set.Ici lower) x := by
    intro x hx
    exact (hasDerivAt_realLogDirichletPower hs0
      (lt_of_lt_of_le hlowerPos hx)).hasDerivWithinAt
  have hbound :
      ∀ x, x ∈ Set.Ici lower →
        ‖realLogDirichletPowerDeriv s x‖ ≤
          (‖s‖ / (s.re / 2) + 1) *
            lower ^ (-s.re / 2 - 1) := by
    intro x hx
    exact (norm_realLogDirichletPowerDeriv_le hs
      (hlower.trans hx)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hlowerPos hx (by linarith))
          hcoefficient)
  have hlip :=
    (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound hlowerMem hupperMem
  have hstep : upper - lower = 1 := by
    dsimp [upper, lower]
    norm_num
  change
    ‖realLogDirichletPower s upper - realLogDirichletPower s lower‖ ≤
      (‖s‖ / (s.re / 2) + 1) *
        lower ^ (-s.re / 2 - 1)
  calc
    ‖realLogDirichletPower s upper - realLogDirichletPower s lower‖ ≤
        ((‖s‖ / (s.re / 2) + 1) *
          lower ^ (-s.re / 2 - 1)) * ‖upper - lower‖ := hlip
    _ = (‖s‖ / (s.re / 2) + 1) *
        lower ^ (-s.re / 2 - 1) := by
      rw [hstep, norm_one, mul_one]

theorem norm_positiveLogDirichletGradient_le
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖positiveLogDirichletGradient s n‖ ≤
      (‖s‖ / (s.re / 2) + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1) := by
  have hn : n + 1 + 1 = n + 2 := by omega
  simpa [positiveLogDirichletGradient, positiveLogDirichletValue,
    positiveDirichletValue, realLogDirichletPower, realDirichletPower,
    hn] using
      (norm_realLogDirichletPower_succ_sub_le hs n)

theorem summable_norm_positiveLogDirichletGradient
    {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖positiveLogDirichletGradient s n‖) := by
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ (-s.re / 2 - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift :
      Summable
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re / 2 - 1)) := by
    have h := hbase.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) by
        intro a b hab
        exact Nat.add_right_cancel hab)
    simpa [Function.comp_def] using h
  have hmajorant :=
    hshift.mul_left (‖s‖ / (s.re / 2) + 1)
  exact hmajorant.of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_positiveLogDirichletGradient_le hs n

theorem positiveLogDirichletGradient_memℓp_two
    {s : ℂ} (hs : 0 < s.re) :
    Memℓp (fun n : ℕ => positiveLogDirichletGradient s n) 2 := by
  have hmemOne :
      Memℓp (fun n : ℕ => positiveLogDirichletGradient s n) 1 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
    simpa using summable_norm_positiveLogDirichletGradient hs
  exact hmemOne.of_exponent_ge (by norm_num)

def canonicalCompletedC3LogJetState
    (s : ℂ) (hs : 0 < s.re) : CarryVerticalL2 :=
  ⟨fun n : ℕ => positiveLogDirichletGradient s n,
    positiveLogDirichletGradient_memℓp_two hs⟩

@[simp] theorem canonicalCompletedC3LogJetState_apply
    (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    canonicalCompletedC3LogJetState s hs n =
      positiveLogDirichletGradient s n :=
  rfl

def canonicalCompletedC3LogJetPrefixState
    (s : ℂ) (N : ℕ) : CarryVerticalL2 :=
  nativeGpreCanonicalVerticalRealization
    (c2LogJetPrefixCore s N)

@[simp] theorem canonicalCompletedC3LogJetPrefixState_apply
    (s : ℂ) (N n : ℕ) :
    canonicalCompletedC3LogJetPrefixState s N n =
      if n < N then positiveLogDirichletGradient s n else 0 := by
  simp [canonicalCompletedC3LogJetPrefixState]

theorem canonicalCompletedC3LogJetPrefixState_eq_sum_single
    (s : ℂ) (N : ℕ) :
    canonicalCompletedC3LogJetPrefixState s N =
      ∑ n ∈ Finset.range N,
        lp.single 2 n (positiveLogDirichletGradient s n) := by
  ext k
  rw [canonicalCompletedC3LogJetPrefixState_apply]
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply]
  rw [Finset.sum_pi_single]
  by_cases hk : k < N <;> simp [hk]

theorem canonicalCompletedC3LogJetPrefixState_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ => canonicalCompletedC3LogJetPrefixState s N)
      atTop
      (nhds (canonicalCompletedC3LogJetState s hs)) := by
  let f := canonicalCompletedC3LogJetState s hs
  have hsum :
      HasSum (fun n : ℕ => lp.single 2 n (f n)) f :=
    lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
  have hpartial := hsum.summable.tendsto_sum_tsum_nat
  have hlimit : (∑' n : ℕ, lp.single 2 n (f n)) = f := hsum.tsum_eq
  rw [hlimit] at hpartial
  have hfunctions :
      (fun N : ℕ => canonicalCompletedC3LogJetPrefixState s N) =
        (fun N : ℕ => ∑ n ∈ Finset.range N, lp.single 2 n (f n)) := by
    funext N
    rw [canonicalCompletedC3LogJetPrefixState_eq_sum_single]
    rfl
  rw [hfunctions]
  exact hpartial

/-- The separated ordinary/log-jet Hilbert carrier. No scalar readout or
real-part projection is applied at this stage. -/
abbrev CanonicalCompletedC3HilbertState :=
  CarryVerticalL2 × CarryVerticalL2

def canonicalCompletedC3HilbertState
    (s : ℂ) (hs : 0 < s.re) : CanonicalCompletedC3HilbertState :=
  (canonicalCompletedC3DirichletGradientState s hs,
    canonicalCompletedC3LogJetState s hs)

def canonicalCompletedC3HilbertPrefixState
    (s : ℂ) (N : ℕ) : CanonicalCompletedC3HilbertState :=
  (canonicalCompletedC3DirichletGradientPrefixState s N,
    canonicalCompletedC3LogJetPrefixState s N)

theorem canonicalCompletedC3HilbertPrefixState_tendsto
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ => canonicalCompletedC3HilbertPrefixState s N)
      atTop
      (nhds (canonicalCompletedC3HilbertState s hs)) := by
  exact (canonicalCompletedC3DirichletGradientPrefixState_tendsto hs).prodMk_nhds
    (canonicalCompletedC3LogJetPrefixState_tendsto hs)

theorem canonicalCompletedC3HilbertPrefixState_norm_sub_tendsto_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto
      (fun N : ℕ =>
        ‖canonicalCompletedC3HilbertPrefixState s N -
          canonicalCompletedC3HilbertState s hs‖)
      atTop
      (nhds 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp
    (canonicalCompletedC3HilbertPrefixState_tendsto hs)

end

end CarrySelfAdjointOperator

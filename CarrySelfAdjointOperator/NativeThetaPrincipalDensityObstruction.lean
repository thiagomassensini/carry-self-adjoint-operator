import CarrySelfAdjointOperator.NativeThetaAdaptiveBudget

/-! A route-specific obstruction on the ACTUAL source: no finite modal
prefix makes the odd principal density pointwise nonnegative. This does not
assert that its integral is negative or rule out integrated coercivity. -/
namespace CarrySelfAdjointOperator
open Filter Set
noncomputable section
set_option autoImplicit false

theorem nativeThetaFirstModeScore_ge_self {u : ℝ} (hu : 1 ≤ u) :
    u ≤ nativeThetaModeScore 0 u := by
  have hu0 : 0 ≤ u := by linarith
  have hp : 4 ≤ nativeThetaModeParameter 0 u := by
    have he := Real.add_one_le_exp (2*u)
    simp only [nativeThetaModeParameter, zero_add, Nat.cast_one, one_pow, mul_one]
    nlinarith [Real.pi_gt_three, mul_nonneg Real.pi_pos.le
      (show 0 ≤ Real.exp (2*u)-3 by linarith)]
  have hd : 6/(2*nativeThetaModeParameter 0 u-3) ≤ 2 :=
    (div_le_iff₀ (by linarith : 0 < 2*nativeThetaModeParameter 0 u-3)).2 (by linarith)
  have hs : 1 ≤ nativeThetaModeSlope (nativeThetaModeParameter 0 u) := by
    unfold nativeThetaModeSlope
    linarith
  exact mul_le_mul_of_nonneg_left hs hu0 |>.trans_eq' (by ring)

theorem nativeThetaPrefixScore_ge_self {K : ℕ} (hK : 0 < K) {u : ℝ} (hu : 1 ≤ u) :
    u ≤ nativeThetaPrefixScore K u :=
  (nativeThetaFirstModeScore_ge_self hu).trans
    (nativeThetaPrefixScore_first_le hK (by linarith))

/-- Even adding any fixed central square/constant cannot remove the eventual
negative sign of this PARTICULAR odd source density. -/
theorem nativeThetaOddPrincipal_eventually_neg (n : ℕ) {K : ℕ} (hK : 0 < K) (C : ℝ) :
    ∀ᶠ u : ℝ in atTop,
      C+nativeThetaPrefixScore K u*(nativeSchurThetaPolynomial 1 n).eval u < 0 := by
  filter_upwards [(nativeSchurThetaPolynomial_odd_tendsto_atBot n).eventually
    (eventually_lt_atBot (-|C|-1)), eventually_ge_atTop (1 : ℝ)] with u hq hu
  have hs : 1 ≤ nativeThetaPrefixScore K u := hu.trans (nativeThetaPrefixScore_ge_self hK hu)
  have hq0 : (nativeSchurThetaPolynomial 1 n).eval u < 0 := by linarith [abs_nonneg C]
  have hm : nativeThetaPrefixScore K u*(nativeSchurThetaPolynomial 1 n).eval u ≤
      (nativeSchurThetaPolynomial 1 n).eval u := by nlinarith
  linarith [le_abs_self C]

theorem nativeThetaOddPrincipal_not_pointwise_nonneg (n : ℕ) {K : ℕ} (hK : 0 < K) (C : ℝ) :
    ¬∀ u : ℝ, 0 ≤ u →
      0 ≤ C+nativeThetaPrefixScore K u*(nativeSchurThetaPolynomial 1 n).eval u := by
  intro h
  obtain ⟨u,hu,hzero⟩ := ((nativeThetaOddPrincipal_eventually_neg n hK C).and
    (eventually_ge_atTop (0 : ℝ))).exists
  exact (not_lt_of_ge (h u hzero)) hu

end
end CarrySelfAdjointOperator

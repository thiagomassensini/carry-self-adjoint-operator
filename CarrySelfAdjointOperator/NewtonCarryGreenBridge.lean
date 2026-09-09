import CarrySelfAdjointOperator.NewtonProjectiveDepthJets
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdIdentity
import CPFormal.Analytic.CpCarryAmplitudeIdentification

/-!
# Newton depth jets in the existing carry Green and boundary realization

Order zero and order one coincide with the already constructed geometric and
affine boundary vectors. Order one is the existing causal Green coefficient.
The existing bracket is the square of the weighted sequence difference in the
interior; its reserved zero coordinate is unchanged.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open PowerSeries CPFormal.Analytic.Cp
open scoped lp ENNReal NNReal

noncomputable section

@[simp] theorem carryWeightedScalarFirstDifference_newtonJet_zero
    {q : ℂ} (hq : q ≠ 0) : carryWeightedScalarFirstDifference q (newtonJet q 0) = 0 := by
  funext k
  simp [carryWeightedScalarFirstDifference, pow_succ, hq, mul_comm]

/-- Pascal's identity is the exact all-order lowering law. -/
theorem carryWeightedScalarFirstDifference_newtonJet_succ
    {q : ℂ} (hq : q ≠ 0) (r : ℕ) :
    carryWeightedScalarFirstDifference q (newtonJet q (r + 1)) = newtonJet q r := by
  funext k
  simp only [carryWeightedScalarFirstDifference, newtonJet, Nat.choose_succ_succ,
    Nat.cast_add, pow_succ]
  field_simp
  ring

/-- Iteration lowers any prescribed number of Newton orders. -/
theorem iterate_carryWeightedScalarFirstDifference_newtonJet
    {q : ℂ} (hq : q ≠ 0) (m r : ℕ) :
    (carryWeightedScalarFirstDifference q)^[m] (newtonJet q (r + m)) = newtonJet q r := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, Nat.add_succ,
        carryWeightedScalarFirstDifference_newtonJet_succ hq, ih]

/-- Every jet is annihilated after one more difference than its order. -/
theorem iterate_carryWeightedScalarFirstDifference_newtonJet_eq_zero
    {q : ℂ} (hq : q ≠ 0) (r : ℕ) :
    (carryWeightedScalarFirstDifference q)^[r + 1] (newtonJet q r) = 0 := by
  rw [Function.iterate_succ_apply']
  have h := iterate_carryWeightedScalarFirstDifference_newtonJet hq r 0
  simp only [Nat.zero_add] at h
  rw [h, carryWeightedScalarFirstDifference_newtonJet_zero hq]

/-- The first Newton jet is the existing vertical Green kernel. -/
theorem newtonJet_one_eq_carryGreenKernel (q : ℝ) (k : ℕ) :
    newtonJet q 1 k = carryWeightedVerticalGreenKernel q k := by
  simp [carryWeightedVerticalGreenKernel]

/-- The native amplitude ratio produces precisely the previously defined
critical carry amplitude at every depth, without a primality assumption. -/
theorem newtonJet_zero_eq_criticalAmplitude (p k : ℕ) :
    newtonJet (primeCarryAmplitudeRatio p) 0 k =
      CPFormal.Carry.Cp.criticalAmplitude p k := by
  rw [newtonJet_zero, primeCarryAmplitudeRatio_eq_criticalAmplitude_one]
  unfold CPFormal.Carry.Cp.criticalAmplitude
  rw [← Real.rpow_mul_natCast (show 0 ≤ (p : ℝ) by positivity)]
  congr 1
  push_cast
  ring

/-- Along the tower `p^k`, multiplying the critical amplitude by the logarithm
is exactly the first Newton mode times `log p`. No division is required. -/
theorem tower_log_criticalAmplitude_eq_newtonJet_one (p k : ℕ) :
    Real.log ((p : ℝ) ^ k) * CPFormal.Carry.Cp.criticalAmplitude p k =
      Real.log (p : ℝ) * newtonJet (primeCarryAmplitudeRatio p) 1 k := by
  rw [Real.log_pow, ← newtonJet_zero_eq_criticalAmplitude]
  simp only [newtonJet_zero, newtonJet_one]
  ring

/-- The existing causal kernel has the dressed projective generating series. -/
theorem mk_carryGreenKernel_eq_weightedProjective (q : ℝ) :
    mk (carryWeightedVerticalGreenKernel q) =
      weightedCoordinate q * (1 + weightedCoordinate q) := by
  have h : carryWeightedVerticalGreenKernel q = newtonJet q 1 := by
    funext k
    exact (newtonJet_one_eq_carryGreenKernel q k).symm
  rw [h, mk_newtonJet_eq_weightedProjective, pow_one]

/-- All Newton orders belong to the same vertical Hilbert space when the
amplitude decays; the polynomial factor is dominated by a geometric series. -/
theorem newtonJet_summable_norm
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℕ) :
    Summable (fun k => ‖newtonJet (q : ℂ) r k‖) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) r
    (show ‖q‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) _ hs
  intro k
  have hc : (k.choose r : ℝ) ≤ (k : ℝ) ^ r := by exact_mod_cast Nat.choose_le_pow k r
  simpa [newtonJet, norm_mul, norm_pow, abs_of_nonneg hq0] using
    mul_le_mul_of_nonneg_right hc (pow_nonneg hq0 k)

/-- Newton jets use the already existing `CarryVerticalL2` carrier. -/
def newtonCarryVector (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℕ) :
    CarryVerticalL2 :=
  ⟨newtonJet (q : ℂ) r, by
    have hmem : Memℓp (newtonJet (q : ℂ) r) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using newtonJet_summable_norm q hq0 hq1 r
    exact hmem.of_exponent_ge (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem newtonCarryVector_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (r k : ℕ) :
    newtonCarryVector q hq0 hq1 r k = newtonJet (q : ℂ) r k := rfl

theorem newtonCarryVector_zero_eq_geometric
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    newtonCarryVector q hq0 hq1 0 = carryGeometricAmplitudeVector q hq0 hq1 := by
  ext k
  simp

theorem newtonCarryVector_one_eq_affineSlope
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    newtonCarryVector q hq0 hq1 1 = carryAffineSlopeAmplitudeVector q hq0 hq1 := by
  ext k
  simp [carryWeightedVerticalGreenKernel]

/-- The complete existing boundary return is the first two Newton modes. -/
theorem carryReturn_eq_newtonModes
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (boundary : ℂ × ℂ) :
    carryWeightedVerticalReturn q hq0 hq1 boundary =
      boundary.1 • newtonCarryVector q hq0 hq1 0 +
      boundary.2 • newtonCarryVector q hq0 hq1 1 := by
  ext k
  simp [carryWeightedVerticalReturn_apply]
  ring

/-- The two trace coordinates are value and first weighted depth difference. -/
theorem carryTrace_eq_depthTrace (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalTrace q x =
      (x 0, carryWeightedScalarFirstDifference (q : ℂ) (fun k => x k) 0) := by
  rw [carryWeightedVerticalTrace_apply]
  rfl

/-- Only the interior is a shifted second difference; coordinate zero remains
the reserved boundary coordinate of the existing bracket. -/
theorem carryBracket_succ_eq_depthDifference_sq
    {q : ℝ} (hq : q ≠ 0) (x : CarryVerticalL2) (k : ℕ) :
    carryWeightedVerticalCenteredBracket q x (k + 1) =
      (q : ℂ) * carryWeightedScalarFirstDifference (q : ℂ)
        (carryWeightedScalarFirstDifference (q : ℂ) (fun n => x n)) k := by
  rw [carryWeightedVerticalCenteredBracket_succ]
  simp only [carryWeightedScalarFirstDifference, Nat.add_assoc]
  have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  field_simp
  ring

/-- The lowering law holds for every order in the same concrete carrier. -/
theorem newtonCarryVector_depthDifference_succ
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (r : ℕ) :
    carryWeightedScalarFirstDifference (q : ℂ)
        (fun k => newtonCarryVector q hqpos.le hq1 (r + 1) k) =
      fun k => newtonCarryVector q hqpos.le hq1 r k :=
  carryWeightedScalarFirstDifference_newtonJet_succ (Complex.ofReal_ne_zero.mpr hqpos.ne') r

/-- The existing bracket lowers two Newton orders in the interior. -/
theorem carryBracket_newtonCarryVector_succ
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (r k : ℕ) :
    carryWeightedVerticalCenteredBracket q
        (newtonCarryVector q hqpos.le hq1 (r + 2)) (k + 1) =
      (q : ℂ) * newtonCarryVector q hqpos.le hq1 r k := by
  rw [carryBracket_succ_eq_depthDifference_sq hqpos.ne']
  change (q : ℂ) * carryWeightedScalarFirstDifference (q : ℂ)
    (carryWeightedScalarFirstDifference (q : ℂ) (newtonJet (q : ℂ) (r + 1 + 1))) k = _
  rw [carryWeightedScalarFirstDifference_newtonJet_succ (Complex.ofReal_ne_zero.mpr hqpos.ne'),
    carryWeightedScalarFirstDifference_newtonJet_succ (Complex.ofReal_ne_zero.mpr hqpos.ne')]
  rfl

/-- Higher Newton orders have exactly zero value and first-difference trace. -/
theorem carryTrace_newtonCarryVector_succ_succ
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℕ) :
    carryWeightedVerticalTrace q (newtonCarryVector q hq0 hq1 (r + 2)) = 0 := by
  rw [carryWeightedVerticalTrace_apply]
  simp [newtonJet, Nat.choose_eq_zero_of_lt (show 1 < r + 2 by omega)]

/-- For all higher Newton orders, the already proved full TFVD reconstructs
the jet from its bracket, because its two boundary coordinates are zero. -/
theorem carryGreen_bracket_newtonCarryVector_succ_succ
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (r : ℕ) :
    carryVerticalL2WeightedGreen q
        (carryWeightedVerticalCenteredBracket q
          (newtonCarryVector q hqpos.le hq1 (r + 2))) =
      newtonCarryVector q hqpos.le hq1 (r + 2) := by
  ext k
  have h := carryWeightedVerticalTfvd_apply q hqpos hq1
    (newtonCarryVector q hqpos.le hq1 (r + 2)) k
  rw [carryTrace_newtonCarryVector_succ_succ, map_zero] at h
  have hz : (0 : CarryVerticalL2) k = 0 := rfl
  rw [hz, add_zero] at h
  exact h

end
end CarrySelfAdjointOperator.ProjectiveDepth

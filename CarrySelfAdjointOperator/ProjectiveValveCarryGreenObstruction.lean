import CarrySelfAdjointOperator.ProjectiveValveCarryEnergyFrontier

/-!
# Translation obstruction for zero-seed weighted C3 responses

The actual carry-weighted Green convolution commutes with unilateral shifts.
The literal C3 source family consists of translates, so its zero-seed response
Gram is stationary. Shift symmetry of the moment coefficients would identify
two distinct response vectors. This only concerns the zero-seed translated
source family; the completed native state has additional boundary and readout
data and is not identified with this family.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp FiniteNativeCarryOperator.Camera NativeCarrySpectralWeyl.Camera
open scoped InnerProductSpace lp

noncomputable section

/-- The concrete unilateral shifts obey the additive composition law. -/
theorem carryVerticalL2UnilateralShift_add_apply (r s : ℕ) (x : CarryVerticalL2) :
    carryVerticalL2UnilateralShift r (carryVerticalL2UnilateralShift s x) =
      carryVerticalL2UnilateralShift (r + s) x := by
  ext n
  by_cases h : r + s ≤ n
  · have hr : r ≤ n := by omega
    have hs : s ≤ n - r := by omega
    simp [carryVerticalL2UnilateralShift_apply, h, hr, hs, Nat.sub_sub]
  · by_cases hr : r ≤ n
    · have hs : ¬ s ≤ n - r := by omega
      simp [carryVerticalL2UnilateralShift_apply, h, hr, hs]
    · simp [carryVerticalL2UnilateralShift_apply, h, hr]

/-- Unilateral shifts preserve the full complex Hilbert pairing. -/
theorem carryVerticalL2UnilateralShift_inner (r : ℕ) (x y : CarryVerticalL2) :
    inner ℂ (carryVerticalL2UnilateralShift r x) (carryVerticalL2UnilateralShift r y) =
      inner ℂ x y := by
  have hback : carryVerticalL2BackwardShift r (carryVerticalL2UnilateralShift r y) = y := by
    ext n
    simp
  change inner ℂ ((ContinuousLinearMap.adjoint (carryVerticalL2BackwardShift r)) x)
    (carryVerticalL2UnilateralShift r y) = _
  rw [ContinuousLinearMap.adjoint_inner_left, hback]

/-- The convergent weighted Green convolution commutes with each shift. -/
theorem carryVerticalL2WeightedGreen_unilateralShift
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (s : ℕ) (x : CarryVerticalL2) :
    carryVerticalL2WeightedGreen q (carryVerticalL2UnilateralShift s x) =
      carryVerticalL2UnilateralShift s (carryVerticalL2WeightedGreen q x) := by
  have hsum := carryWeightedVerticalGreenTerm_summable carryVerticalL2ShiftFamily hq0 hq1
  have hvecsum : Summable (fun r : ℕ =>
      carryVerticalL2OperatorApply x
        (carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r)) :=
    ((carryVerticalL2OperatorApply x).hasSum hsum.hasSum).summable
  change carryVerticalL2OperatorApply (carryVerticalL2UnilateralShift s x)
      (∑' r : ℕ, carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r) =
    carryVerticalL2UnilateralShift s (carryVerticalL2OperatorApply x
      (∑' r : ℕ, carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r))
  rw [(carryVerticalL2OperatorApply (carryVerticalL2UnilateralShift s x)).map_tsum hsum,
    (carryVerticalL2OperatorApply x).map_tsum hsum,
    (carryVerticalL2UnilateralShift s).map_tsum hvecsum]
  apply tsum_congr
  intro r
  simp only [carryVerticalL2OperatorApply_apply, carryWeightedVerticalGreenTerm,
    carryVerticalL2ShiftFamily, map_smul,
    carryVerticalL2UnilateralShift_add_apply]
  rw [Nat.add_comm r s]

/-- Shifting one coordinate vector translates its support. -/
theorem carryVerticalL2UnilateralShift_single_value (r k : ℕ) (z : ℂ) :
    carryVerticalL2UnilateralShift r (lp.single 2 k z) = lp.single 2 (k + r) z := by
  ext n
  by_cases hr : r ≤ n
  · have hiff : n - r = k ↔ n = k + r := by omega
    simp [carryVerticalL2UnilateralShift_apply, hr, lp.single_apply, Pi.single_apply, hiff]
  · have hne : n ≠ k + r := by omega
    simp [carryVerticalL2UnilateralShift_apply, hr, lp.single_apply, hne]

/-- Successive C3 source brackets are literal translates by three cells. -/
theorem br2C3VerticalState_succ_eq_shift (n : ℕ) :
    br2CameraBracketVerticalState 3 1 (n + 1) =
      carryVerticalL2UnilateralShift 3 (br2CameraBracketVerticalState 3 1 n) := by
  simp only [br2CameraBracketVerticalState, map_add,
    carryVerticalL2UnilateralShift_single_value]
  congr 2

/-- The zero-seed weighted responses inherit that same translation law. -/
theorem br2C3CausalResponse_succ_eq_shift
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    br2CameraBracketCausalGreenResponse q 3 1 (n + 1) =
      carryVerticalL2UnilateralShift 3 (br2CameraBracketCausalGreenResponse q 3 1 n) := by
  unfold br2CameraBracketCausalGreenResponse
  rw [br2C3VerticalState_succ_eq_shift, carryVerticalL2WeightedGreen_unilateralShift q hq0 hq1]

/-- The zero-seed weighted C3 response Gram cannot be a polarized moment
coefficient array for any sequence. Translation invariance of its diagonal
would force the distinct responses at indices zero and two to coincide. -/
theorem not_br2C3CausalResponse_coefficientEquation
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) (moments : ℕ → ℝ) :
    ¬ IsPolarizedGreenCoefficientEquation moments
      (fun p r => inner ℂ (br2CameraBracketCausalGreenResponse q 3 1 p)
        (br2CameraBracketCausalGreenResponse q 3 1 r)) := by
  intro hcoeff
  let u := br2CameraBracketCausalGreenResponse q 3 1
  have hstep (n : ℕ) : u (n + 1) = carryVerticalL2UnilateralShift 3 (u n) :=
    br2C3CausalResponse_succ_eq_shift q hqpos.le hq1 n
  have h11 : inner ℂ (u 1) (u 1) = inner ℂ (u 0) (u 0) := by
    rw [hstep 0, carryVerticalL2UnilateralShift_inner]
  have h22 : inner ℂ (u 2) (u 2) = inner ℂ (u 1) (u 1) := by
    rw [hstep 1, carryVerticalL2UnilateralShift_inner]
  have h02 : inner ℂ (u 0) (u 2) = inner ℂ (u 1) (u 1) :=
    polarizedGreenCoefficient_transport hcoeff 0 1
  have h20 : inner ℂ (u 2) (u 0) = inner ℂ (u 1) (u 1) := by
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) h02
  have hzero : inner ℂ (u 0 - u 2) (u 0 - u 2) = 0 := by
    simp only [inner_sub_left, inner_sub_right]
    rw [h20, h02, h22, ← h11]
    ring
  have heq : u 0 = u 2 := sub_eq_zero.mp ((inner_self_eq_zero).mp hzero)
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by norm_num [mem_radiusSet_iff]
  have hind := (br2CameraBracketCausalGreenResponseIncidenceJetTransport
    q hqpos hq1 hbase hradius).even_linearIndependent hbase hradius
  have hindices : (0 : ℕ) = 1 := hind.injective heq
  norm_num at hindices

namespace ProjectiveValve

/-- In particular, selecting the amplitude derived from carry geometry does
not repair the translated zero-seed source family. This theorem does not
address the completed native state's own boundary/jet data. -/
theorem not_canonicalProjectiveCarryGreenMomentEquation (moments : ℕ → ℝ) :
    ¬ ProjectiveIncidenceMomentEquation moments (canonicalProjectiveCarryGreenMap 3) 3 1 := by
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by norm_num [mem_radiusSet_iff]
  intro h
  apply not_br2C3CausalResponse_coefficientEquation
    (canonicalBR2CarryAmplitudeRatio 3)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase) moments
  change IsPolarizedGreenCoefficientEquation moments
    (projectiveIncidenceCoefficient (canonicalProjectiveCarryGreenMap 3) 3 1) at h
  convert h using 1
  funext p r
  simp only [projectiveIncidenceCoefficient,
    projectiveIncidenceRawJet_canonicalCarryGreen hbase hradius]

end ProjectiveValve

end
end CarrySelfAdjointOperator

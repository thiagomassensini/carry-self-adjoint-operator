import CarrySelfAdjointOperator.ProjectiveValveCarryGreenObstruction

/-!
# Exact first shift defect of the existing causal C3 realization

The response vectors are unilateral translates. Their first Hankel shift
defect has strictly negative real part: minus half the squared distance
between responses zero and two. No moment sequence is assumed or introduced.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp FiniteNativeCarryOperator.Camera NativeCarrySpectralWeyl.Camera
open scoped InnerProductSpace lp

noncomputable section
set_option autoImplicit false

/-- The first two even causal responses remain distinct. -/
theorem br2C3CausalResponse_zero_ne_two
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    br2CameraBracketCausalGreenResponse q 3 1 0 ≠
      br2CameraBracketCausalGreenResponse q 3 1 2 := by
  intro heq
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by norm_num [mem_radiusSet_iff]
  have hind := (br2CameraBracketCausalGreenResponseIncidenceJetTransport
    q hqpos hq1 hbase hradius).even_linearIndependent hbase hradius
  have hindices : (0 : ℕ) = 1 := hind.injective heq
  norm_num at hindices

/-- Exact noncancelling term in the first requested shift equality. -/
theorem br2C3CausalResponse_firstShiftDefect_eq
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    let u := br2CameraBracketCausalGreenResponse q 3 1
    (inner ℂ (u 0) (u 2) - inner ℂ (u 1) (u 1)).re =
      -(1 / 2 : ℝ) * ‖u 0 - u 2‖ ^ 2 := by
  dsimp only
  let u := br2CameraBracketCausalGreenResponse q 3 1
  have hstep (n : ℕ) : u (n + 1) = carryVerticalL2UnilateralShift 3 (u n) :=
    br2C3CausalResponse_succ_eq_shift q hq0 hq1 n
  have h11 : inner ℂ (u 1) (u 1) = inner ℂ (u 0) (u 0) := by
    rw [hstep 0, carryVerticalL2UnilateralShift_inner]
  have h22 : inner ℂ (u 2) (u 2) = inner ℂ (u 1) (u 1) := by
    rw [hstep 1, carryVerticalL2UnilateralShift_inner]
  have hn11 := congrArg (RCLike.re : ℂ → ℝ) h11
  have hn22 := congrArg (RCLike.re : ℂ → ℝ) h22
  simp only [inner_self_eq_norm_sq] at hn11 hn22
  have hdist := norm_sub_sq (𝕜 := ℂ) (u 0) (u 2)
  change RCLike.re (inner ℂ (u 0) (u 2)) -
    RCLike.re (inner ℂ (u 1) (u 1)) = -(1 / 2 : ℝ) * ‖u 0 - u 2‖ ^ 2
  rw [inner_self_eq_norm_sq]
  nlinarith

/-- The first shift defect is strictly negative, including the crossed term. -/
theorem br2C3CausalResponse_firstShiftDefect_neg
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    let u := br2CameraBracketCausalGreenResponse q 3 1
    (inner ℂ (u 0) (u 2) - inner ℂ (u 1) (u 1)).re < 0 := by
  dsimp only
  rw [br2C3CausalResponse_firstShiftDefect_eq q hqpos.le hq1]
  have hnorm := norm_pos_iff.mpr
    (sub_ne_zero.mpr (br2C3CausalResponse_zero_ne_two q hqpos hq1))
  nlinarith [sq_pos_of_pos hnorm]

/-- Thus the actual causal response fails the requested equality already at
orders p=0, q=1, independently of any chosen moment sequence. -/
theorem br2C3CausalResponse_firstShift_ne
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    let u := br2CameraBracketCausalGreenResponse q 3 1
    inner ℂ (u 0) (u 2) ≠ inner ℂ (u 1) (u 1) := by
  dsimp only
  intro h
  have hneg := br2C3CausalResponse_firstShiftDefect_neg q hqpos hq1
  dsimp only at h hneg
  rw [h, sub_self] at hneg
  norm_num at hneg

namespace ProjectiveValve

/-- The existing projective/carry realization inherits the same strict
defect, since its chart transport returns the literal causal responses. -/
theorem canonicalProjectiveCarryGreen_firstShiftDefect_neg :
    (projectiveIncidenceCoefficient (canonicalProjectiveCarryGreenMap 3) 3 1 0 2 -
      projectiveIncidenceCoefficient (canonicalProjectiveCarryGreenMap 3) 3 1 1 1).re < 0 := by
  have hbase : IsSupported 3 := by norm_num [IsSupported]
  have hradius : (1 : ℕ) ∈ radiusSet 3 := by norm_num [mem_radiusSet_iff]
  simp only [projectiveIncidenceCoefficient,
    projectiveIncidenceRawJet_canonicalCarryGreen hbase hradius]
  exact br2C3CausalResponse_firstShiftDefect_neg _
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)

end ProjectiveValve
end
end CarrySelfAdjointOperator

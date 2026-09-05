import CPFormal.Analytic.CpCarryWeightedVerticalTfvdIdentity
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# The actual carry TFVD trace metric as a polarized Hilbert kernel

The causal second-difference analysis has two leading coordinates and a
shifted copy of the existing carry bracket. Its full Hilbert product is the
bracket product plus the positive two-trace form from the research notes.
This is an identity on the actual infinite vertical carry space, with no
cutoff or moment-positivity premise. It does not identify this analysis metric
with the completed-native logarithmic response.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open scoped InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

/-- The causal stencil `q⁻¹ I - 2 U + q U²`. For nonzero q this is
`q⁻¹ (I - q U)²`, written without requiring an inverse operator. -/
def carryTfvdCausalSecondDifference (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ((q : ℂ)⁻¹) • ContinuousLinearMap.id ℂ CarryVerticalL2 -
    (2 : ℂ) • carryVerticalL2UnilateralShift 1 +
    (q : ℂ) • carryVerticalL2UnilateralShift 2

@[simp] theorem carryTfvdCausalSecondDifference_zero (q : ℝ) (x : CarryVerticalL2) :
    carryTfvdCausalSecondDifference q x 0 = (q : ℂ)⁻¹ * x 0 := by
  change (q : ℂ)⁻¹ * x 0 - 2 * (carryVerticalL2UnilateralShift 1 x) 0 +
    (q : ℂ) * (carryVerticalL2UnilateralShift 2 x) 0 = _
  simp

@[simp] theorem carryTfvdCausalSecondDifference_one (q : ℝ) (x : CarryVerticalL2) :
    carryTfvdCausalSecondDifference q x 1 = (q : ℂ)⁻¹ * x 1 - 2 * x 0 := by
  change (q : ℂ)⁻¹ * x 1 - 2 * (carryVerticalL2UnilateralShift 1 x) 1 +
    (q : ℂ) * (carryVerticalL2UnilateralShift 2 x) 1 = _
  simp

@[simp] theorem carryTfvdCausalSecondDifference_add_two
    (q : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryTfvdCausalSecondDifference q x (n + 2) =
      carryWeightedVerticalCenteredBracket q x (n + 1) := by
  change (q : ℂ)⁻¹ * x (n + 2) - 2 * (carryVerticalL2UnilateralShift 1 x) (n + 2) +
    (q : ℂ) * (carryVerticalL2UnilateralShift 2 x) (n + 2) = _
  simp

private theorem carryInner_head_tail (x y : CarryVerticalL2) (r : ℕ) :
    inner ℂ x y = (∑ n ∈ Finset.range r, inner ℂ (x n) (y n)) +
      inner ℂ (carryVerticalL2BackwardShift r x) (carryVerticalL2BackwardShift r y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact ((lp.summable_inner (𝕜 := ℂ) x y).sum_add_tsum_nat_add r).symm

theorem carryTfvdCausalSecondDifference_inner (q : ℝ) (x y : CarryVerticalL2) :
    inner ℂ (carryTfvdCausalSecondDifference q x) (carryTfvdCausalSecondDifference q y) =
      inner ℂ (carryWeightedVerticalCenteredBracket q x)
        (carryWeightedVerticalCenteredBracket q y) +
      inner ℂ ((q : ℂ)⁻¹ * x 0) ((q : ℂ)⁻¹ * y 0) +
      inner ℂ ((q : ℂ)⁻¹ * x 1 - 2 * x 0) ((q : ℂ)⁻¹ * y 1 - 2 * y 0) := by
  have htail (v : CarryVerticalL2) :
      carryVerticalL2BackwardShift 2 (carryTfvdCausalSecondDifference q v) =
        carryVerticalL2BackwardShift 1 (carryWeightedVerticalCenteredBracket q v) := by
    ext n
    simp
  have hb := carryInner_head_tail
    (carryWeightedVerticalCenteredBracket q x) (carryWeightedVerticalCenteredBracket q y) 1
  simp only [Finset.sum_range_one, carryWeightedVerticalCenteredBracket_zero,
    inner_zero_left, zero_add] at hb
  rw [carryInner_head_tail _ _ 2, htail x, htail y, ← hb]
  simp [Finset.sum_range_succ]
  ring

/-- The metric acts on the existing trace `(x₀,q⁻¹x₁-x₀)`. -/
def carryTfvdTraceMetric (q : ℝ) (v w : ℂ × ℂ) : ℂ :=
  inner ℂ ((q : ℂ)⁻¹ * v.1) ((q : ℂ)⁻¹ * w.1) +
    inner ℂ (v.2 - v.1) (w.2 - w.1)

theorem carryTfvdTraceMetric_matrix (q : ℝ) (v w : ℂ × ℂ) :
    carryTfvdTraceMetric q v w =
      (((q : ℂ)⁻¹)^2 + 1) * conj v.1 * w.1 - conj v.1 * w.2 -
        conj v.2 * w.1 + conj v.2 * w.2 := by
  simp [carryTfvdTraceMetric, RCLike.inner_apply, map_sub, map_mul, map_inv₀]
  ring

theorem carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace
    (q : ℝ) (x y : CarryVerticalL2) :
    inner ℂ (carryTfvdCausalSecondDifference q x) (carryTfvdCausalSecondDifference q y) =
      inner ℂ (carryWeightedVerticalCenteredBracket q x)
        (carryWeightedVerticalCenteredBracket q y) +
      carryTfvdTraceMetric q (carryWeightedVerticalTrace q x) (carryWeightedVerticalTrace q y) := by
  rw [carryTfvdCausalSecondDifference_inner]
  simp only [carryTfvdTraceMetric, carryWeightedVerticalTrace_apply]
  have hx : (q : ℂ)⁻¹ * x 1 - x 0 - x 0 = (q : ℂ)⁻¹ * x 1 - 2 * x 0 := by ring
  have hy : (q : ℂ)⁻¹ * y 1 - y 0 - y 0 = (q : ℂ)⁻¹ * y 1 - 2 * y 0 := by ring
  rw [hx, hy]
  ring

/-- Bracket and metric-weighted trace form one positive one-point state. -/
def carryTfvdMetricState (q : ℝ) (x : CarryVerticalL2) :
    WithLp 2 (CarryVerticalL2 × WithLp 2 (ℂ × ℂ)) :=
  WithLp.toLp 2 (carryWeightedVerticalCenteredBracket q x,
    WithLp.toLp 2 (((q : ℂ)⁻¹ * (carryWeightedVerticalTrace q x).1),
      (carryWeightedVerticalTrace q x).2 - (carryWeightedVerticalTrace q x).1))

theorem carryTfvdMetricState_inner (q : ℝ) (x y : CarryVerticalL2) :
    inner ℂ (carryTfvdMetricState q x) (carryTfvdMetricState q y) =
      inner ℂ (carryTfvdCausalSecondDifference q x) (carryTfvdCausalSecondDifference q y) := by
  rw [carryTfvdCausalSecondDifference_inner_eq_bracket_add_trace]
  simp only [carryTfvdMetricState, WithLp.prod_inner_apply,
    carryTfvdTraceMetric]

/-- The metric state retains the original carry state: both traces can be
decoded and the existing TFVD reconstruction then applies. -/
theorem carryTfvdMetricState_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    Function.Injective (carryTfvdMetricState q) := by
  intro x y hxy
  have hb : carryWeightedVerticalCenteredBracket q x =
      carryWeightedVerticalCenteredBracket q y :=
    congrArg (fun v => (WithLp.ofLp v).1) hxy
  have hv : (q : ℂ)⁻¹ * (carryWeightedVerticalTrace q x).1 =
      (q : ℂ)⁻¹ * (carryWeightedVerticalTrace q y).1 :=
    congrArg (fun v => (WithLp.ofLp (WithLp.ofLp v).2).1) hxy
  have hf : (carryWeightedVerticalTrace q x).1 =
      (carryWeightedVerticalTrace q y).1 :=
    mul_left_cancel₀ (inv_ne_zero (Complex.ofReal_ne_zero.mpr hqpos.ne')) hv
  have hs : (carryWeightedVerticalTrace q x).2 - (carryWeightedVerticalTrace q x).1 =
      (carryWeightedVerticalTrace q y).2 - (carryWeightedVerticalTrace q y).1 :=
    congrArg (fun v => (WithLp.ofLp (WithLp.ofLp v).2).2) hxy
  rw [hf] at hs
  have ht : carryWeightedVerticalTrace q x = carryWeightedVerticalTrace q y :=
    Prod.ext hf (sub_left_inj.mp hs)
  ext n
  rw [← carryWeightedVerticalTfvd_apply q hqpos hq1 x n,
    ← carryWeightedVerticalTfvd_apply q hqpos hq1 y n, hb, ht]

theorem carryTfvdMetricState_gram_posSemidef
    (q : ℝ) {ι : Type*} [Finite ι] (state : ι → CarryVerticalL2) :
    (Matrix.of fun i j ↦
      inner ℂ (carryTfvdMetricState q (state i)) (carryTfvdMetricState q (state j))).PosSemidef :=
  Matrix.posSemidef_gram ℂ _

end
end CarrySelfAdjointOperator

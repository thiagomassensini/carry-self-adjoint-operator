import CarrySelfAdjointOperator.BR2ProjectiveHilbertIncidenceTransport
import CarrySelfAdjointOperator.CausalBracketStateUniqueness
import CarrySelfAdjointOperator.CompletedTfvdGreenAllOrderIntertwining
import CPFormal.Analytic.CpCarryWeightedVerticalTfvdIdentity
import Mathlib.Tactic

/-!
# BR2 bracket sources and their causal Green responses

The BR2 incidence vector is the source of a weighted causal Green problem,
not the response state itself.  This module constructs the response, proves
the exact source equation `B (G b) = b`, derives injectivity from that left
inverse, and transports the complete parity family through every finite TFVD
analysis.

The coordinate construction is finite before Hilbert completion: each output
coordinate is a triangular finite Green sum, and geometric cutoff completeness
contains both source legs.  The completed response is then identified with
the unique causal double-telescope reconstruction.  No Gram equality,
spectral premise, scalar normalization, or zero condition is used.
-/

open scoped BigOperators lp ENNReal NNReal

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

theorem carryWeightedVerticalGreenKernel_secondDifference
    (q : ℝ) (hq : q ≠ 0) (k : ℕ) :
    (q : ℂ)⁻¹ * (carryWeightedVerticalGreenKernel q (k + 2) : ℂ) -
        2 * (carryWeightedVerticalGreenKernel q (k + 1) : ℂ) +
          (q : ℂ) * (carryWeightedVerticalGreenKernel q k : ℂ) = 0 := by
  simp only [carryWeightedVerticalGreenKernel]
  push_cast
  rw [pow_succ, pow_succ]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  field_simp [hqC]
  ring

theorem carryWeightedVerticalCenteredBracket_weightedGreen_succ
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracket q
        (carryVerticalL2WeightedGreen q x) (n + 1) = x (n + 1) := by
  let y := carryVerticalL2WeightedGreen q x
  have hy2 : y (n + 2) =
      (∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q (n + 2 - j) : ℂ) * x j) +
        (q : ℂ) * x (n + 1) := by
    rw [show y (n + 2) = carryVerticalL2WeightedGreen q x (n + 2) by rfl]
    rw [carryVerticalL2WeightedGreen_apply_reindexed q hqpos.le hq1]
    rw [show n + 2 + 1 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    simp only [Nat.sub_self, carryWeightedVerticalGreenKernel_zero,
      Complex.ofReal_zero, zero_mul, add_zero]
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    simp [carryWeightedVerticalGreenKernel]
  have hy1 : y (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q (n + 1 - j) : ℂ) * x j := by
    rw [show y (n + 1) = carryVerticalL2WeightedGreen q x (n + 1) by rfl]
    rw [carryVerticalL2WeightedGreen_apply_reindexed q hqpos.le hq1]
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    simp
  have hy0 : y n =
      ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j := by
    exact carryVerticalL2WeightedGreen_apply_reindexed q hqpos.le hq1 x n
  rw [show carryWeightedVerticalCenteredBracket q
      (carryVerticalL2WeightedGreen q x) (n + 1) =
      carryWeightedVerticalCenteredBracket q y (n + 1) by rfl]
  rw [carryWeightedVerticalCenteredBracket_succ, hy2, hy1, hy0]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hsum :
      (∑ j ∈ Finset.range (n + 1),
        ((q : ℂ)⁻¹ *
            ((carryWeightedVerticalGreenKernel q (n + 2 - j) : ℂ) * x j) -
          2 * ((carryWeightedVerticalGreenKernel q (n + 1 - j) : ℂ) * x j) +
          ((carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j) * (q : ℂ))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have h1 : n + 1 - j = (n - j) + 1 := by omega
    have h2 : n + 2 - j = (n - j) + 2 := by omega
    rw [h1, h2]
    have hk := carryWeightedVerticalGreenKernel_secondDifference q hqpos.ne' (n - j)
    calc
      _ = (((q : ℂ)⁻¹ *
              (carryWeightedVerticalGreenKernel q (n - j + 2) : ℂ) -
            2 * (carryWeightedVerticalGreenKernel q (n - j + 1) : ℂ) +
            (q : ℂ) * (carryWeightedVerticalGreenKernel q (n - j) : ℂ)) *
          x j) := by ring
      _ = 0 := by rw [hk]; simp
  have hcombine :
      (∑ j ∈ Finset.range (n + 1),
          (q : ℂ)⁻¹ *
            ((carryWeightedVerticalGreenKernel q (n + 2 - j) : ℂ) * x j)) -
        (∑ j ∈ Finset.range (n + 1),
          2 * ((carryWeightedVerticalGreenKernel q (n + 1 - j) : ℂ) * x j)) +
        (∑ j ∈ Finset.range (n + 1),
          (q : ℂ) *
            ((carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j)) = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hsum
  calc
    _ =
        ((∑ j ∈ Finset.range (n + 1),
            (q : ℂ)⁻¹ *
              ((carryWeightedVerticalGreenKernel q (n + 2 - j) : ℂ) * x j)) -
          (∑ j ∈ Finset.range (n + 1),
            2 * ((carryWeightedVerticalGreenKernel q (n + 1 - j) : ℂ) * x j)) +
          (∑ j ∈ Finset.range (n + 1),
            (q : ℂ) *
              ((carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j))) +
          (q : ℂ)⁻¹ * ((q : ℂ) * x (n + 1)) := by ring
    _ = (q : ℂ)⁻¹ * ((q : ℂ) * x (n + 1)) := by rw [hcombine]; simp
    _ = x (n + 1) := by field_simp [Complex.ofReal_ne_zero.mpr hqpos.ne']

/-- The weighted causal Green operator is a right inverse of the interior
bracket.  Coordinate zero is the explicit boundary reservoir. -/
theorem carryWeightedVerticalCenteredBracket_weightedGreen
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) :
    carryWeightedVerticalCenteredBracket q
        (carryVerticalL2WeightedGreen q x) =
      carryVerticalL2ZeroHeadProjection x := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      rw [carryWeightedVerticalCenteredBracket_weightedGreen_succ
        q hqpos hq1 x n]
      simp [carryVerticalL2ZeroHeadProjection_apply]

/-- A supported bracket incidence does not occupy the boundary reservoir. -/
theorem br2CameraBracketVerticalState_zero
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    br2CameraBracketVerticalState base radius index 0 = 0 := by
  have hrlt : radius <
      FiniteNativeCarryOperator.Camera.alignedCenter base index :=
    cameraRadius_lt_alignedCenter hbase hradius index
  have hleft : 0 ≠
      FiniteNativeCarryOperator.Camera.alignedCenter base index - radius := by
    omega
  have hcenter : 0 ≠
      FiniteNativeCarryOperator.Camera.alignedCenter base index := by
    omega
  have hright : 0 ≠
      FiniteNativeCarryOperator.Camera.alignedCenter base index + radius := by
    omega
  simp [br2CameraBracketVerticalState, hleft, hcenter, hright]

/-- A bracket source retained below a geometric cutoff is supported inside
the complete camera window, including both legs of its last cell. -/
theorem br2CameraBracketVerticalState_eq_zero_of_window_lt
    {base radius cutoff index position : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (hindex : index < cutoff)
    (hposition :
      NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff < position) :
    br2CameraBracketVerticalState base radius index position = 0 := by
  have hlegs := NativeCarryC3Crosswalk.included_center_has_both_legs_in_window
    hbase hindex hradius
  have hcenter :
      FiniteNativeCarryOperator.Camera.alignedCenter base index ≤
        NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff := by
    exact le_trans (Nat.le_add_right _ radius) hlegs.2
  have hleft_ne : position ≠
      FiniteNativeCarryOperator.Camera.alignedCenter base index - radius := by
    omega
  have hcenter_ne : position ≠
      FiniteNativeCarryOperator.Camera.alignedCenter base index := by
    omega
  have hright_ne : position ≠
      FiniteNativeCarryOperator.Camera.alignedCenter base index + radius := by
    omega
  simp [br2CameraBracketVerticalState, hleft_ne, hcenter_ne, hright_ne]

/-- Green/causal response generated by one BR2 bracket source. -/
def br2CameraBracketCausalGreenResponse
    (q : ℝ) (base radius index : ℕ) : CarryVerticalL2 :=
  carryVerticalL2WeightedGreen q
    (br2CameraBracketVerticalState base radius index)

/-- Every coordinate of the causal response is already a finite triangular
Green sum.  The completed Hilbert vector adds bounded completion, not a new
coordinate formula. -/
theorem br2CameraBracketCausalGreenResponse_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (base radius index n : ℕ) :
    br2CameraBracketCausalGreenResponse q base radius index n =
      ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q (n - j) : ℂ) *
          br2CameraBracketVerticalState base radius index j := by
  exact carryVerticalL2WeightedGreen_apply_reindexed q hq0 hq1 _ n

/-- The bracket of the Green response is the original incidence source. -/
theorem carryWeightedVerticalCenteredBracket_br2CausalGreenResponse
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    carryWeightedVerticalCenteredBracket q
        (br2CameraBracketCausalGreenResponse q base radius index) =
      br2CameraBracketVerticalState base radius index := by
  rw [br2CameraBracketCausalGreenResponse,
    carryWeightedVerticalCenteredBracket_weightedGreen q hqpos hq1]
  ext n
  by_cases hn : n = 0
  · subst n
    rw [carryVerticalL2ZeroHeadProjection_apply,
      br2CameraBracketVerticalState_zero hbase hradius]
    simp
  · simp [carryVerticalL2ZeroHeadProjection_apply, hn]

/-- Add the exact two-coordinate TFVD boundary return to a source response.
The boundary is an argument because it must come from the state being
identified; no boundary normalization is chosen here. -/
def br2CameraBracketCausalGreenResponseWithBoundary
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (base radius index : ℕ) (boundary : ℂ × ℂ) : CarryVerticalL2 :=
  br2CameraBracketCausalGreenResponse q base radius index +
    carryWeightedVerticalReturn q hq0 hq1 boundary

/-- Adding the boundary return does not change the source equation. -/
theorem carryWeightedVerticalCenteredBracket_br2CausalGreenResponseWithBoundary
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) (boundary : ℂ × ℂ) :
    carryWeightedVerticalCenteredBracket q
        (br2CameraBracketCausalGreenResponseWithBoundary
          q hqpos.le hq1 base radius index boundary) =
      br2CameraBracketVerticalState base radius index := by
  rw [br2CameraBracketCausalGreenResponseWithBoundary, map_add,
    carryWeightedVerticalCenteredBracket_br2CausalGreenResponse
      q hqpos hq1 hbase hradius]
  have hreturn := congrArg
    (fun T : (ℂ × ℂ) →L[ℂ] CarryVerticalL2 => T boundary)
    (carryWeightedVerticalCenteredBracket_comp_return q hqpos hq1)
  simpa using hreturn

/-- Exact commuting-square criterion.  A candidate state is the causal Green
response with its own TFVD boundary precisely when its weighted bracket is
the prescribed BR2 source.  Thus the only non-formal comparison with an
existing completed state is the source identity on the right. -/
theorem eq_br2CausalGreenResponseWithOwnBoundary_iff
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) (x : CarryVerticalL2) :
    x = br2CameraBracketCausalGreenResponseWithBoundary
          q hqpos.le hq1 base radius index
          (carryWeightedVerticalTrace q x) ↔
      carryWeightedVerticalCenteredBracket q x =
        br2CameraBracketVerticalState base radius index := by
  constructor
  · intro hx
    rw [hx]
    exact
      carryWeightedVerticalCenteredBracket_br2CausalGreenResponseWithBoundary
        q hqpos hq1 hbase hradius index (carryWeightedVerticalTrace q x)
  · intro hbracket
    have htfvd :
        carryVerticalL2WeightedGreen q
              (carryWeightedVerticalCenteredBracket q x) +
            carryWeightedVerticalReturn q hqpos.le hq1
              (carryWeightedVerticalTrace q x) = x := by
      ext n
      exact carryWeightedVerticalTfvd_apply q hqpos hq1 x n
    calc
      x = carryVerticalL2WeightedGreen q
            (carryWeightedVerticalCenteredBracket q x) +
          carryWeightedVerticalReturn q hqpos.le hq1
            (carryWeightedVerticalTrace q x) :=
        htfvd.symm
      _ = carryVerticalL2WeightedGreen q
            (br2CameraBracketVerticalState base radius index) +
          carryWeightedVerticalReturn q hqpos.le hq1
            (carryWeightedVerticalTrace q x) := by rw [hbracket]
      _ = br2CameraBracketCausalGreenResponseWithBoundary
          q hqpos.le hq1 base radius index
          (carryWeightedVerticalTrace q x) := rfl

/-- Beyond a complete source window, the response satisfies the homogeneous
weighted bracket equation.  This is the exact finite-cutoff/tail
compatibility, not a truncation of the response vector. -/
theorem carryWeightedVerticalCenteredBracket_br2CausalGreenResponse_eq_zero_of_window_lt
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius cutoff index position : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (hindex : index < cutoff)
    (hposition :
      NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff < position) :
    carryWeightedVerticalCenteredBracket q
        (br2CameraBracketCausalGreenResponse q base radius index) position = 0 := by
  rw [carryWeightedVerticalCenteredBracket_br2CausalGreenResponse
    q hqpos hq1 hbase hradius]
  exact br2CameraBracketVerticalState_eq_zero_of_window_lt
    hbase hradius hindex hposition

/-! ## Canonical carry-amplitude specialization -/

/-- Base-neutral name for the carry amplitude already fixed upstream.  The
upstream implementation uses the historical `primeCarry` prefix, but its
definition and proofs require only `base ≥ 2`. -/
def canonicalBR2CarryAmplitudeRatio (base : ℕ) : ℝ :=
  primeCarryAmplitudeRatio base

theorem canonicalBR2CarryAmplitudeRatio_pos
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    0 < canonicalBR2CarryAmplitudeRatio base := by
  apply primeCarryAmplitudeRatio_pos base
  exact le_trans (by norm_num) hbase

theorem canonicalBR2CarryAmplitudeRatio_lt_one
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base) :
    canonicalBR2CarryAmplitudeRatio base < 1 := by
  exact primeCarryAmplitudeRatio_lt_one base hbase

/-- Source response with the carry amplitude forced by the same camera base. -/
def canonicalBR2CameraBracketCausalGreenResponse
    (base radius index : ℕ) : CarryVerticalL2 :=
  br2CameraBracketCausalGreenResponse
    (canonicalBR2CarryAmplitudeRatio base) base radius index

/-- Canonical base-dressed bracket of the response recovers the source. -/
theorem canonicalBR2WeightedVerticalCenteredBracket_causalGreenResponse
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    carryWeightedVerticalCenteredBracket
        (canonicalBR2CarryAmplitudeRatio base)
        (canonicalBR2CameraBracketCausalGreenResponse base radius index) =
      br2CameraBracketVerticalState base radius index := by
  exact carryWeightedVerticalCenteredBracket_br2CausalGreenResponse
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
    hbase hradius index

/-- First concrete comparison square with the finite TFVD/Green state already
used by the completed all-order construction.  At a geometrically complete
camera cutoff, equality with the causal response is exactly the source
comparison displayed on the right; no Gram or scalar kernel occurs. -/
theorem canonicalCompletedC3DirichletGradientPrefixState_eq_br2Response_iff
    {base radius cutoff index : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (_hindex : index < cutoff)
    (s : ℂ) :
    let q := canonicalBR2CarryAmplitudeRatio base
    let horizon :=
      NativeCarrySpectralWeyl.Limits.finiteCameraWindow base cutoff + 1
    let prefixState := canonicalCompletedC3DirichletGradientPrefixState s horizon
    prefixState = br2CameraBracketCausalGreenResponseWithBoundary
        q (canonicalBR2CarryAmplitudeRatio_pos hbase).le
        (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
        base radius index (carryWeightedVerticalTrace q prefixState) ↔
      carryWeightedVerticalCenteredBracket q prefixState =
        br2CameraBracketVerticalState base radius index := by
  dsimp only
  exact eq_br2CausalGreenResponseWithOwnBoundary_iff
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
    hbase hradius index _

/-- The Green convolution has zero value at the boundary coordinate. -/
@[simp] theorem carryVerticalL2WeightedGreen_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (x : CarryVerticalL2) :
    carryVerticalL2WeightedGreen q x 0 = 0 := by
  rw [carryVerticalL2WeightedGreen_apply_reindexed q hq0 hq1]
  simp

/-- Boundary-completed causal Green transform.  The extra coordinate is the
canonical boundary reservoir; it vanishes on every supported BR2 incidence. -/
def carryWeightedVerticalGreenBoundaryEmbedding (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  carryVerticalL2WeightedGreen q +
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 0 (1 : ℂ)) ∘L
      carryVerticalL2Eval 0)

@[simp] theorem carryWeightedVerticalGreenBoundaryEmbedding_apply
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalGreenBoundaryEmbedding q x =
      carryVerticalL2WeightedGreen q x + x 0 • lp.single 2 0 (1 : ℂ) := by
  rfl

/-- The boundary-completed Green transform is injective because its boundary
coordinate recovers the head and the bracket recovers every positive source
coordinate. -/
theorem carryWeightedVerticalGreenBoundaryEmbedding_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    Function.Injective (carryWeightedVerticalGreenBoundaryEmbedding q) := by
  intro x y hxy
  have h0 : x 0 = y 0 := by
    have h := congrArg (fun z : CarryVerticalL2 ↦ z 0) hxy
    simpa [carryWeightedVerticalGreenBoundaryEmbedding_apply,
      carryVerticalL2WeightedGreen_zero q hqpos.le hq1,
      lp.single_apply] using h
  have hgreen :
      carryVerticalL2WeightedGreen q x =
        carryVerticalL2WeightedGreen q y := by
    rw [carryWeightedVerticalGreenBoundaryEmbedding_apply,
      carryWeightedVerticalGreenBoundaryEmbedding_apply, h0] at hxy
    exact add_right_cancel hxy
  have hprojection :
      carryVerticalL2ZeroHeadProjection x =
        carryVerticalL2ZeroHeadProjection y := by
    have h := congrArg
      (fun z : CarryVerticalL2 ↦ carryWeightedVerticalCenteredBracket q z)
      hgreen
    simpa [carryWeightedVerticalCenteredBracket_weightedGreen q hqpos hq1]
      using h
  ext n
  by_cases hn : n = 0
  · subst n
    exact h0
  · have h := congrArg (fun z : CarryVerticalL2 ↦ z n) hprojection
    simpa [carryVerticalL2ZeroHeadProjection_apply, hn] using h

/-- Real-linear source-to-response map used by the all-order BR2 transport. -/
def br2CameraBracketCausalGreenResponseMap (q : ℝ) :
    (ℕ →₀ ℝ) →ₗ[ℝ] CanonicalCompletedTfvdGreenHilbertCarrier :=
  ((carryWeightedVerticalGreenBoundaryEmbedding q).toLinearMap.restrictScalars ℝ).comp
    br2CameraBracketProjectiveHilbertMap

theorem br2CameraBracketCausalGreenResponseMap_injective
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    Function.Injective (br2CameraBracketCausalGreenResponseMap q) :=
  (carryWeightedVerticalGreenBoundaryEmbedding_injective q hqpos hq1).comp
    br2CameraBracketProjectiveHilbertMap_injective

@[simp] theorem br2CameraBracketCausalGreenResponseMap_cameraBracketIncidence
    (q : ℝ) {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    br2CameraBracketCausalGreenResponseMap q
        (cameraBracketIncidence base radius index) =
      br2CameraBracketCausalGreenResponse q base radius index := by
  rw [br2CameraBracketCausalGreenResponseMap,
    LinearMap.comp_apply,
    br2CameraBracketProjectiveHilbertMap_cameraBracketIncidence]
  change carryWeightedVerticalGreenBoundaryEmbedding q
      (br2CameraBracketVerticalState base radius index) =
    br2CameraBracketCausalGreenResponse q base radius index
  rw [carryWeightedVerticalGreenBoundaryEmbedding_apply,
    br2CameraBracketVerticalState_zero hbase hradius]
  simp [br2CameraBracketCausalGreenResponse]

/-- Parity-interleaved family of actual causal Green responses. -/
def br2CameraBracketCausalGreenResponseParityJet
    (q : ℝ) (base radius : ℕ) :
    (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier
  | Sum.inl n => br2CameraBracketCausalGreenResponse q base radius (2 * n)
  | Sum.inr n => br2CameraBracketCausalGreenResponse q base radius (2 * n + 1)

/-- All-order incidence transport into the response states.  Injectivity comes
from the bracket left inverse plus the explicit boundary reservoir. -/
def br2CameraBracketCausalGreenResponseIncidenceJetTransport
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base) :
    BR2BracketIncidenceJetTransport base radius
      (br2CameraBracketCausalGreenResponseParityJet q base radius) where
  toLinearMap := br2CameraBracketCausalGreenResponseMap q
  injective := br2CameraBracketCausalGreenResponseMap_injective q hqpos hq1
  even_eq n := by
    exact (br2CameraBracketCausalGreenResponseMap_cameraBracketIncidence
      q hbase hradius (2 * n)).symm
  odd_eq n := by
    exact (br2CameraBracketCausalGreenResponseMap_cameraBracketIncidence
      q hbase hradius (2 * n + 1)).symm

/-- Canonically dressed parity family, with no free Green ratio. -/
def canonicalBR2CameraBracketCausalGreenResponseParityJet
    (base radius : ℕ) :
    (ℕ ⊕ ℕ) → CanonicalCompletedTfvdGreenHilbertCarrier :=
  br2CameraBracketCausalGreenResponseParityJet
    (canonicalBR2CarryAmplitudeRatio base) base radius

/-- The all-order source-to-response transport at the carry amplitude fixed by
the camera base.  Its injectivity is inherited from the bracket left inverse. -/
def canonicalBR2CameraBracketCausalGreenResponseIncidenceJetTransport
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base) :
    BR2BracketIncidenceJetTransport base radius
      (canonicalBR2CameraBracketCausalGreenResponseParityJet base radius) :=
  br2CameraBracketCausalGreenResponseIncidenceJetTransport
    (canonicalBR2CarryAmplitudeRatio base)
    (canonicalBR2CarryAmplitudeRatio_pos hbase)
    (canonicalBR2CarryAmplitudeRatio_lt_one hbase)
    hbase hradius

/-! ## Compatibility with every finite enriched TFVD carrier -/

/-- The bracket projection of the finite enriched TFVD analysis of a response
is exactly its original incidence source. -/
theorem nativeGpreFiniteTfvdAnalysisBracketProjection_br2CausalGreenResponse
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    nativeGpreFiniteTfvdAnalysisBracketProjection S
        (nativeGpreFiniteTfvdAnalysis q S
          (br2CameraBracketCausalGreenResponse q base radius index)) =
      br2CameraBracketVerticalState base radius index := by
  change carryWeightedVerticalCenteredBracket q
      (br2CameraBracketCausalGreenResponse q base radius index) =
    br2CameraBracketVerticalState base radius index
  exact carryWeightedVerticalCenteredBracket_br2CausalGreenResponse
    q hqpos hq1 hbase hradius index

/-- Finite TFVD synthesis reconstructs the same response state exactly. -/
theorem nativeGpreFiniteTfvdReconstruction_analysis_br2CausalGreenResponse
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (base radius index : ℕ) :
    nativeGpreFiniteTfvdReconstruction q hqpos.le hq1 S
        (nativeGpreFiniteTfvdAnalysis q S
          (br2CameraBracketCausalGreenResponse q base radius index)) =
      br2CameraBracketCausalGreenResponse q base radius index := by
  exact nativeGpreFiniteTfvdReconstruction_analysis
    q hqpos hq1 S (br2CameraBracketCausalGreenResponse q base radius index)

/-! ## Identification with the abstract causal reconstruction -/

/-- Remove the canonical amplitude weight from a vertical state. -/
def carryWeightedVerticalUndress (q : ℝ) (x : CarryVerticalL2) : ℕ → ℂ :=
  fun n ↦ ((q : ℂ)⁻¹) ^ n * x n

/-- After undressing, the weighted bracket is exactly the causal unit bracket.
The factor is forced by the amplitude coordinate change. -/
theorem causalUnitBracket_carryWeightedVerticalUndress
    (q : ℝ) (hq : q ≠ 0) (x : CarryVerticalL2) (n : ℕ) :
    causalUnitBracket (carryWeightedVerticalUndress q x) n =
      ((q : ℂ)⁻¹) ^ (n + 1) *
        carryWeightedVerticalCenteredBracket q x (n + 1) := by
  rw [causalUnitBracket, carryWeightedVerticalCenteredBracket_succ]
  simp only [carryWeightedVerticalUndress]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  field_simp [hqC]
  rw [pow_succ]
  field_simp [hqC]
  have hsq : (q : ℂ) ^ 2 * (q : ℂ)⁻¹ = (q : ℂ) := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hqC, mul_one]
  ring_nf
  rw [hsq]

/-- Causal data carried by one supported BR2 source after the canonical
amplitude undressing. -/
def br2CameraBracketCausalData
    (q : ℝ) (base radius index : ℕ) : CausalBracketData ℂ where
  leftSeed := 0
  centerSeed := 0
  bracket := fun n ↦
    ((q : ℂ)⁻¹) ^ (n + 1) *
      br2CameraBracketVerticalState base radius index (n + 1)

/-- The Green response realizes the two canonical seeds and every prescribed
causal bracket. -/
theorem br2CameraBracketCausalGreenResponse_realizes
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    RealizesCausalBracketData
      (br2CameraBracketCausalData q base radius index)
      (carryWeightedVerticalUndress q
        (br2CameraBracketCausalGreenResponse q base radius index)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [carryWeightedVerticalUndress,
      br2CameraBracketCausalGreenResponse,
      br2CameraBracketCausalData,
      carryVerticalL2WeightedGreen_zero q hqpos.le hq1]
  · rw [carryWeightedVerticalUndress]
    rw [br2CameraBracketCausalGreenResponse]
    rw [carryVerticalL2WeightedGreen_apply_reindexed q hqpos.le hq1]
    change ((q : ℂ)⁻¹) ^ 1 *
        (∑ j ∈ Finset.range (1 + 1),
          (carryWeightedVerticalGreenKernel q (1 - j) : ℂ) *
            br2CameraBracketVerticalState base radius index j) = 0
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [br2CameraBracketVerticalState_zero hbase hradius]
    simp [carryWeightedVerticalGreenKernel]
  · intro n
    rw [causalUnitBracket_carryWeightedVerticalUndress q hqpos.ne']
    rw [carryWeightedVerticalCenteredBracket_br2CausalGreenResponse
      q hqpos hq1 hbase hradius]
    rfl

/-- Causal uniqueness identifies the undressed Green response with the
canonical double-telescope reconstruction of the same source. -/
theorem br2CameraBracketCausalGreenResponse_eq_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    {base radius : ℕ}
    (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (hradius : radius ∈ FiniteNativeCarryOperator.Camera.radiusSet base)
    (index : ℕ) :
    carryWeightedVerticalUndress q
        (br2CameraBracketCausalGreenResponse q base radius index) =
      causalBracketReconstruction
        (br2CameraBracketCausalData q base radius index) := by
  exact causalBracketReconstruction_unique
    (br2CameraBracketCausalData q base radius index)
    (carryWeightedVerticalUndress q
      (br2CameraBracketCausalGreenResponse q base radius index))
    (br2CameraBracketCausalGreenResponse_realizes
      q hqpos hq1 hbase hradius index)

end

end CarrySelfAdjointOperator

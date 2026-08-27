import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceGramBridge
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
# Vector limit of completed Green forward differences

Entrywise Gram convergence at one common step proves finite Hankel
semidefiniteness, but it does not by itself produce Hilbert vectors at the
limit.  For that construction one must retain the mixed inner products of
two independently varying steps.

This file isolates that exact strengthening.  It defines the two-step scalar
kernel difference, identifies it with the inner product of the corresponding
state differences, and proves that a joint cross-Gram limit makes every jet
sequence Cauchy.  Completeness then gives one concrete limit jet whose real
Gram is exactly the prescribed Green--Wronskian moment kernel.
-/

namespace CarrySelfAdjointOperator

open Filter Topology

noncomputable section

/-- Normalized mixed forward difference with independent steps in the two
kernel variables. -/
def completedGreenKernelTwoStepForwardDifference
    (kernel : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ) : ℂ :=
  (starRingEnd ℂ) (((Nat.factorial p : ℂ) * h ^ p)⁻¹) *
    (((Nat.factorial q : ℂ) * g ^ q)⁻¹) *
      (completedGreenForwardDifference h)^[p]
        (fun w ↦ (completedGreenForwardDifference g)^[q] (kernel w) 0) 0

/-- Mixed scalar forward differences with independent steps are exactly the
inner product of the corresponding state forward differences. -/
theorem completedGreenKernel_twoStepMixedForwardDifference_eq_inner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (h g : ℂ) (p q : ℕ) :
    (completedGreenForwardDifference h)^[p]
        (fun w ↦ (completedGreenForwardDifference g)^[q]
          (fun z ↦ inner ℂ (state w) (state z)) 0) 0 =
      inner ℂ
        ((completedGreenForwardDifference h)^[p] state 0)
        ((completedGreenForwardDifference g)^[q] state 0) := by
  have hright :
      (fun w ↦ (completedGreenForwardDifference g)^[q]
        (fun z ↦ inner ℂ (state w) (state z)) 0) =
      (fun w ↦ inner ℂ (state w)
        ((completedGreenForwardDifference g)^[q] state 0)) := by
    funext w
    exact congrFun
      (completedGreenForwardDifference_iter_inner_right g state (state w) q) 0
  rw [hright]
  exact congrFun
    (completedGreenForwardDifference_iter_inner_left h state
      ((completedGreenForwardDifference g)^[q] state 0) p) 0

/-- The two-step normalized kernel difference is the exact cross inner
product of normalized state jets. -/
theorem inner_completedGreenForwardDifferenceJet_twoStep_eq_kernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E) (h g : ℂ) (p q : ℕ) :
    inner ℂ
        (completedGreenForwardDifferenceJet state h p)
        (completedGreenForwardDifferenceJet state g q) =
      completedGreenKernelTwoStepForwardDifference
        (fun w z ↦ inner ℂ (state w) (state z)) h g p q := by
  unfold completedGreenForwardDifferenceJet
    completedGreenKernelTwoStepForwardDifference
  rw [inner_smul_left, inner_smul_right,
    completedGreenKernel_twoStepMixedForwardDifference_eq_inner]
  ring

/-! ## Joint continuity of the analytic divided difference -/

/-- The total divided difference of an analytic scalar germ converges jointly
to its derivative when both endpoints converge to the center.  This is the
uniform two-point control supplied by strict differentiability; it is
strictly stronger than continuity of either fixed-endpoint `dslope`. -/
theorem completedGreenDslope_tendsto_prod_of_analyticAt
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0) :
    Tendsto
      (fun points : ℂ × ℂ ↦ dslope response points.1 points.2)
      (nhds (0, 0))
      (nhds (deriv response 0)) := by
  have hstrict :
      Tendsto
        (fun points : ℂ × ℂ ↦
          ‖points.1 - points.2‖⁻¹ *
            ‖response points.1 - response points.2 -
              (points.1 - points.2) * deriv response 0‖)
        (nhds (0, 0)) (nhds 0) := by
    simpa only [smul_eq_mul] using
      (hasDerivAtFilter_iff_tendsto.mp hresponse.hasStrictDerivAt)
  have hderiv :
      Tendsto
        (fun points : ℂ × ℂ ↦
          ‖deriv response points.1 - deriv response 0‖)
        (nhds (0, 0)) (nhds 0) := by
    have hfirst : ContinuousAt
        (fun points : ℂ × ℂ ↦ deriv response points.1) (0, 0) :=
      by
        simpa [Function.comp_def] using
          (ContinuousAt.comp
            (f := fun points : ℂ × ℂ ↦ points.1)
            (g := deriv response)
            (x := ((0, 0) : ℂ × ℂ))
            hresponse.deriv.continuousAt
            (continuousAt_fst (p := ((0, 0) : ℂ × ℂ))))
    have hconstant : ContinuousAt
        (fun _ : ℂ × ℂ ↦ deriv response 0) (0, 0) :=
      continuousAt_const
    simpa using (hfirst.sub hconstant).norm.tendsto
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun points ↦ ?_)
    (by simpa using hstrict.add hderiv)
  rcases points with ⟨w, z⟩
  rcases eq_or_ne z w with hsame | hne
  · subst z
    simp [dslope_same]
  · rw [dslope_of_ne _ hne]
    simp only [slope, smul_eq_mul]
    have hsub : w - z ≠ 0 := sub_ne_zero.mpr hne.symm
    calc
      ‖(z - w)⁻¹ *
            (response z - response w) -
          deriv response 0‖ =
          ‖w - z‖⁻¹ *
            ‖response w - response z -
              (w - z) * deriv response 0‖ := by
        rw [← norm_inv, ← norm_mul]
        congr 1
        field_simp [hsub]
        ring
      _ ≤ _ := le_add_of_nonneg_right (norm_nonneg _)

/-- Iterated divided differences with the fixed center `0`. -/
def completedGreenCenteredDslopeIter (response : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (Function.swap dslope 0)^[n] response

/-- Fixed-center `dslope` iteration preserves analyticity at the center. -/
theorem completedGreenCenteredDslopeIter_analyticAt
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0) (n : ℕ) :
    AnalyticAt ℂ (completedGreenCenteredDslopeIter response n) 0 := by
  rcases hresponse with ⟨series, hseries⟩
  exact ⟨(FormalMultilinearSeries.fslope^[n]) series,
    hseries.has_fpower_series_iterate_dslope_fslope n⟩

/-- The total divided difference is symmetric in its two endpoints. -/
theorem completedGreenDslope_comm (response : ℂ → ℂ) (w z : ℂ) :
    dslope response w z = dslope response z w := by
  by_cases h : w = z
  · subst z
    rfl
  · rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h]
    simp only [slope, smul_eq_mul]
    field_simp [h]
    simp only [vsub_eq_sub]
    ring

/-- One centered `dslope` step splits off the constant endpoint term and
leaves one explicit power of the first endpoint. -/
theorem completedGreenDslope_centered_step
    (response : ℂ → ℂ) (w z : ℂ)
    (hdiff : DifferentiableAt ℂ (dslope response 0) w) :
    dslope response w z =
      dslope response 0 z +
        w * dslope (dslope response 0) w z := by
  let shifted := dslope response 0
  change dslope response w z = shifted z + w * dslope shifted w z
  have hfactor (x : ℂ) : response x = response 0 + x * shifted x := by
    have hx := sub_smul_dslope response 0 x
    simpa [shifted, smul_eq_mul] using eq_add_of_sub_eq' hx.symm
  by_cases h : w = z
  · subst z
    rw [dslope_same, dslope_same]
    have hderiv : deriv response w =
        shifted w + w * deriv shifted w := by
      have hproduct : HasDerivAt (fun x : ℂ ↦ x * shifted x)
          (shifted w + w * deriv shifted w) w := by
        let hbase := (hasDerivAt_id w).mul hdiff.hasDerivAt
        have hbase' : HasDerivAt (id * dslope response 0)
            (shifted w + w * deriv shifted w) w := by
          simpa [shifted] using hbase
        apply hbase'.congr_of_eventuallyEq
        filter_upwards with x
        rfl
      have hsum : HasDerivAt (fun x : ℂ ↦ response 0 + x * shifted x)
          (shifted w + w * deriv shifted w) w := by
        let hbase :=
          (hasDerivAt_const (x := w) (c := response 0)).add hproduct
        have hbase' : HasDerivAt
            ((fun _ : ℂ ↦ response 0) + fun x : ℂ ↦ x * shifted x)
            (shifted w + w * deriv shifted w) w := by
          simpa using hbase
        apply hbase'.congr_of_eventuallyEq
        filter_upwards with x
        rfl
      have heq : response = fun x : ℂ ↦ response 0 + x * shifted x :=
        funext hfactor
      calc
        deriv response w =
            deriv (fun x : ℂ ↦ response 0 + x * shifted x) w :=
          congrArg (fun f : ℂ → ℂ ↦ deriv f w) heq
        _ = shifted w + w * deriv shifted w := hsum.deriv
    simp [shifted, hderiv]
  · rw [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ (Ne.symm h)]
    simp only [slope, smul_eq_mul]
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hz := hfactor z
    have hw := hfactor w
    field_simp [hzw]
    simp only [vsub_eq_sub]
    linear_combination hz - hw

/-- Successive fixed-center divided differences are obtained by one more
application of `dslope` at `0`. -/
theorem completedGreenCenteredDslopeIter_succ
    (response : ℂ → ℂ) (n : ℕ) :
    completedGreenCenteredDslopeIter response (n + 1) =
      dslope (completedGreenCenteredDslopeIter response n) 0 := by
  simp [completedGreenCenteredDslopeIter, Function.iterate_succ_apply']

/-- Finite centered expansion of a total divided difference in its first
endpoint.  The remainder retains the full two-endpoint `dslope`; no scalar
channel is discarded. -/
theorem completedGreenDslope_eq_centeredExpansion
    (response : ℂ → ℂ) (order : ℕ) (w z : ℂ)
    (hdiff : ∀ n < order,
      DifferentiableAt ℂ
        (completedGreenCenteredDslopeIter response (n + 1)) w) :
    dslope response w z =
      (∑ n ∈ Finset.range order,
        w ^ n * completedGreenCenteredDslopeIter response (n + 1) z) +
      w ^ order *
        dslope (completedGreenCenteredDslopeIter response order) w z := by
  induction order with
  | zero => simp [completedGreenCenteredDslopeIter]
  | succ order ih =>
      rw [ih (fun n hn ↦ hdiff n (by omega))]
      have hstep := completedGreenDslope_centered_step
        (completedGreenCenteredDslopeIter response order) w z
        (by
          rw [← completedGreenCenteredDslopeIter_succ]
          exact hdiff order (by omega))
      rw [hstep, Finset.sum_range_succ]
      rw [completedGreenCenteredDslopeIter_succ]
      ring

/-- Signed first-axis sum of a total divided difference. -/
def completedGreenDslopeFirstAxisSum
    (response : ℂ → ℂ) (order : ℕ) (h z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (order + 1),
    completedGreenForwardWeight order i *
      dslope response ((i : ℂ) * h) z

/-- The order-`p` signed sum extracts exactly `h^p`; its remainder is a
finite weighted family of the jointly controlled shifted `dslope`. -/
theorem completedGreenDslopeFirstAxisSum_factor
    (response : ℂ → ℂ) (order : ℕ) (h z : ℂ)
    (hdiff : ∀ i ∈ Finset.range (order + 1),
      ∀ n < order,
        DifferentiableAt ℂ
          (completedGreenCenteredDslopeIter response (n + 1))
          ((i : ℂ) * h)) :
    completedGreenDslopeFirstAxisSum response order h z =
      h ^ order *
        ∑ i ∈ Finset.range (order + 1),
          completedGreenForwardWeight order i * (i : ℂ) ^ order *
            dslope (completedGreenCenteredDslopeIter response order)
              ((i : ℂ) * h) z := by
  classical
  unfold completedGreenDslopeFirstAxisSum
  rw [show (∑ i ∈ Finset.range (order + 1),
        completedGreenForwardWeight order i *
          dslope response ((i : ℂ) * h) z) =
      ∑ i ∈ Finset.range (order + 1),
        completedGreenForwardWeight order i *
          ((∑ n ∈ Finset.range order,
              ((i : ℂ) * h) ^ n *
                completedGreenCenteredDslopeIter response (n + 1) z) +
            ((i : ℂ) * h) ^ order *
              dslope (completedGreenCenteredDslopeIter response order)
                ((i : ℂ) * h) z) by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact completedGreenDslope_eq_centeredExpansion response order
      ((i : ℂ) * h) z (hdiff i hi)]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hlower :
      (∑ i ∈ Finset.range (order + 1),
        completedGreenForwardWeight order i *
          ∑ n ∈ Finset.range order,
            ((i : ℂ) * h) ^ n *
              completedGreenCenteredDslopeIter response (n + 1) z) = 0 := by
    calc
      (∑ i ∈ Finset.range (order + 1),
          completedGreenForwardWeight order i *
            ∑ n ∈ Finset.range order,
              ((i : ℂ) * h) ^ n *
                completedGreenCenteredDslopeIter response (n + 1) z) =
          ∑ n ∈ Finset.range order,
            ∑ i ∈ Finset.range (order + 1),
              completedGreenForwardWeight order i *
                (((i : ℂ) * h) ^ n *
                  completedGreenCenteredDslopeIter response (n + 1) z) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hnlt : n < order := Finset.mem_range.mp hn
        rw [show (∑ i ∈ Finset.range (order + 1),
              completedGreenForwardWeight order i *
                (((i : ℂ) * h) ^ n *
                  completedGreenCenteredDslopeIter response (n + 1) z)) =
            h ^ n * completedGreenCenteredDslopeIter response (n + 1) z *
              completedGreenForwardWeightPower order n by
          unfold completedGreenForwardWeightPower
          simp_rw [mul_pow]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring]
        rw [completedGreenForwardWeightPower_eq_zero_of_lt hnlt, mul_zero]
  rw [hlower, zero_add]
  simp_rw [mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Signed second-axis sum of a total divided difference. -/
def completedGreenDslopeSecondAxisSum
    (response : ℂ → ℂ) (order : ℕ) (g w : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (order + 1),
    completedGreenForwardWeight order j *
      dslope response w ((j : ℂ) * g)

/-- The same exact factorization holds in the second endpoint, by symmetry of
the total divided difference. -/
theorem completedGreenDslopeSecondAxisSum_factor
    (response : ℂ → ℂ) (order : ℕ) (g w : ℂ)
    (hdiff : ∀ j ∈ Finset.range (order + 1),
      ∀ n < order,
        DifferentiableAt ℂ
          (completedGreenCenteredDslopeIter response (n + 1))
          ((j : ℂ) * g)) :
    completedGreenDslopeSecondAxisSum response order g w =
      g ^ order *
        ∑ j ∈ Finset.range (order + 1),
          completedGreenForwardWeight order j * (j : ℂ) ^ order *
            dslope (completedGreenCenteredDslopeIter response order)
              w ((j : ℂ) * g) := by
  unfold completedGreenDslopeSecondAxisSum
  rw [show (∑ j ∈ Finset.range (order + 1),
        completedGreenForwardWeight order j *
          dslope response w ((j : ℂ) * g)) =
      completedGreenDslopeFirstAxisSum response order g w by
    unfold completedGreenDslopeFirstAxisSum
    apply Finset.sum_congr rfl
    intro j hj
    rw [completedGreenDslope_comm response w ((j : ℂ) * g)]]
  rw [completedGreenDslopeFirstAxisSum_factor response order g w hdiff]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact completedGreenDslope_comm
    (completedGreenCenteredDslopeIter response order) ((j : ℂ) * g) w

/-- Fixed-center iteration composes by addition of its orders. -/
theorem completedGreenCenteredDslopeIter_comp
    (response : ℂ → ℂ) (p q : ℕ) :
    completedGreenCenteredDslopeIter
        (completedGreenCenteredDslopeIter response p) q =
      completedGreenCenteredDslopeIter response (p + q) := by
  unfold completedGreenCenteredDslopeIter
  rw [← Function.iterate_add_apply]
  congr 1
  omega

/-- Explicit two-step signed sum, with the endpoint channels still separate. -/
def completedGreenDslopeTwoStepSum
    (response : ℂ → ℂ) (p q : ℕ) (h g : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (q + 1),
    completedGreenForwardWeight q j *
      completedGreenDslopeFirstAxisSum response p h ((j : ℂ) * g)

/-- Exact bivariate factorization of the polarized signed sum.  The two
independent powers are extracted before taking any limit. -/
theorem completedGreenDslopeTwoStepSum_factor
    (response : ℂ → ℂ) (p q : ℕ) (h g : ℂ)
    (hdiffFirst : ∀ i ∈ Finset.range (p + 1),
      ∀ n < p,
        DifferentiableAt ℂ
          (completedGreenCenteredDslopeIter response (n + 1))
          ((i : ℂ) * h))
    (hdiffSecond : ∀ j ∈ Finset.range (q + 1),
      ∀ n < q,
        DifferentiableAt ℂ
          (completedGreenCenteredDslopeIter
            (completedGreenCenteredDslopeIter response p) (n + 1))
          ((j : ℂ) * g)) :
    completedGreenDslopeTwoStepSum response p q h g =
      h ^ p * g ^ q *
        ∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ∑ j ∈ Finset.range (q + 1),
              (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
                dslope (completedGreenCenteredDslopeIter response (p + q))
                  ((i : ℂ) * h) ((j : ℂ) * g) := by
  classical
  unfold completedGreenDslopeTwoStepSum
  calc
    (∑ j ∈ Finset.range (q + 1),
        completedGreenForwardWeight q j *
          completedGreenDslopeFirstAxisSum response p h ((j : ℂ) * g)) =
      ∑ j ∈ Finset.range (q + 1),
        completedGreenForwardWeight q j *
          (h ^ p *
            ∑ i ∈ Finset.range (p + 1),
              completedGreenForwardWeight p i * (i : ℂ) ^ p *
                dslope (completedGreenCenteredDslopeIter response p)
                  ((i : ℂ) * h) ((j : ℂ) * g)) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      exact completedGreenDslopeFirstAxisSum_factor
        response p h ((j : ℂ) * g) hdiffFirst
    _ = h ^ p *
        ∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            completedGreenDslopeSecondAxisSum
              (completedGreenCenteredDslopeIter response p) q g
              ((i : ℂ) * h) := by
      unfold completedGreenDslopeSecondAxisSum
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = h ^ p *
        ∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            (g ^ q *
              ∑ j ∈ Finset.range (q + 1),
                completedGreenForwardWeight q j * (j : ℂ) ^ q *
                  dslope
                    (completedGreenCenteredDslopeIter
                      (completedGreenCenteredDslopeIter response p) q)
                    ((i : ℂ) * h) ((j : ℂ) * g)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact completedGreenDslopeSecondAxisSum_factor
        (completedGreenCenteredDslopeIter response p) q g ((i : ℂ) * h)
        hdiffSecond
    _ = h ^ p * g ^ q *
        ∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ∑ j ∈ Finset.range (q + 1),
              (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
                dslope (completedGreenCenteredDslopeIter response (p + q))
                  ((i : ℂ) * h) ((j : ℂ) * g) := by
      rw [completedGreenCenteredDslopeIter_comp]
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The independently stepped iterated forward difference is exactly the
explicit polarized two-step sum. -/
theorem completedGreenDslope_twoStepMixedForwardDifference_eq_sum
    (response : ℂ → ℂ) (h g : ℂ) (p q : ℕ) :
    (completedGreenForwardDifference h)^[p]
        (fun w ↦ (completedGreenForwardDifference g)^[q]
          (fun z ↦ dslope response w z) 0) 0 =
      completedGreenDslopeTwoStepSum response p q h g := by
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  unfold completedGreenDslopeTwoStepSum completedGreenDslopeFirstAxisSum
  calc
    (∑ i ∈ Finset.range (p + 1),
        ((-1 : ℤ) ^ (p - i) * p.choose i) •
          (completedGreenForwardDifference g)^[q]
            (fun z ↦ dslope response (i • h) z) 0) =
      ∑ i ∈ Finset.range (p + 1),
        ∑ j ∈ Finset.range (q + 1),
          completedGreenForwardWeight p i *
            completedGreenForwardWeight q j *
              dslope response ((i : ℂ) * h) ((j : ℂ) * g) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [completedGreenForwardDifference_iter_eq_sum_shift]
      simp only [zero_add]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp [completedGreenForwardWeight, nsmul_eq_mul]
      ring
    _ = ∑ j ∈ Finset.range (q + 1),
        completedGreenForwardWeight q j *
          ∑ i ∈ Finset.range (p + 1),
            completedGreenForwardWeight p i *
              dslope response ((i : ℂ) * h) ((j : ℂ) * g) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Finite weighted sampling functional for a scalar two-variable kernel. -/
def completedGreenTwoStepWeightedSum
    (kernel : ℂ → ℂ → ℂ) (p q : ℕ) (h g : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (p + 1),
    (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
      ∑ j ∈ Finset.range (q + 1),
        (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
          kernel ((i : ℂ) * h) ((j : ℂ) * g)

/-- Finite remainder left after extracting the two independent step powers. -/
def completedGreenDslopeTwoStepRemainder
    (response : ℂ → ℂ) (p q : ℕ) (h g : ℂ) : ℂ :=
  completedGreenTwoStepWeightedSum
    (fun w z ↦ dslope
      (completedGreenCenteredDslopeIter response (p + q)) w z)
    p q h g

/-- Joint convergence of a kernel passes through the finite two-step weighted
sampling functional. -/
theorem completedGreenTwoStepWeightedSum_tendsto
    {kernel : ℂ → ℂ → ℂ} {coefficient : ℂ}
    (hkernel : Tendsto
      (fun points : ℂ × ℂ ↦ kernel points.1 points.2)
      (nhds (0, 0)) (nhds coefficient))
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ ↦
        completedGreenTwoStepWeightedSum kernel p q
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2))
      atTop
      (nhds
        (∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ∑ j ∈ Finset.range (q + 1),
              (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
                coefficient)) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hstepFirst : Tendsto
      (fun steps : ℕ × ℕ ↦ canonicalGreenJetStep steps.1)
      atTop (nhds 0) := canonicalGreenJetStep_tendsto_zero.comp hfst
  have hstepSecond : Tendsto
      (fun steps : ℕ × ℕ ↦ canonicalGreenJetStep steps.2)
      atTop (nhds 0) := canonicalGreenJetStep_tendsto_zero.comp hsnd
  unfold completedGreenTwoStepWeightedSum
  apply tendsto_finsetSum
  intro i hi
  have hinner : Tendsto
      (fun steps : ℕ × ℕ ↦
        ∑ j ∈ Finset.range (q + 1),
          (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
            kernel
              ((i : ℂ) * canonicalGreenJetStep steps.1)
              ((j : ℂ) * canonicalGreenJetStep steps.2))
      atTop
      (nhds (∑ j ∈ Finset.range (q + 1),
        (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
          coefficient)) := by
    apply tendsto_finsetSum
    intro j hj
    have hpoints : Tendsto
        (fun steps : ℕ × ℕ ↦
          ((i : ℂ) * canonicalGreenJetStep steps.1,
            (j : ℂ) * canonicalGreenJetStep steps.2))
        atTop (nhds (0, 0)) := by
      rw [nhds_prod_eq]
      simpa only [mul_zero] using
        (hstepFirst.const_mul (i : ℂ)).prodMk
          (hstepSecond.const_mul (j : ℂ))
    exact Filter.Tendsto.const_mul
      (completedGreenForwardWeight q j * (j : ℂ) ^ q)
      (hkernel.comp hpoints)
  exact Filter.Tendsto.const_mul
    (completedGreenForwardWeight p i * (i : ℂ) ^ p) hinner

/-- Named remainder form of the exact bivariate factorization. -/
theorem completedGreenDslopeTwoStepSum_factor_remainder
    (response : ℂ → ℂ) (p q : ℕ) (h g : ℂ)
    (hdiffFirst : ∀ i ∈ Finset.range (p + 1),
      ∀ n < p,
        DifferentiableAt ℂ
          (completedGreenCenteredDslopeIter response (n + 1))
          ((i : ℂ) * h))
    (hdiffSecond : ∀ j ∈ Finset.range (q + 1),
      ∀ n < q,
        DifferentiableAt ℂ
          (completedGreenCenteredDslopeIter
            (completedGreenCenteredDslopeIter response p) (n + 1))
          ((j : ℂ) * g)) :
    completedGreenDslopeTwoStepSum response p q h g =
      h ^ p * g ^ q *
        completedGreenDslopeTwoStepRemainder response p q h g := by
  simpa [completedGreenDslopeTwoStepRemainder,
    completedGreenTwoStepWeightedSum] using
    completedGreenDslopeTwoStepSum_factor response p q h g
      hdiffFirst hdiffSecond

/-- The derivative of the shifted centered germ is the corresponding next
Taylor coefficient of the original response. -/
theorem deriv_completedGreenCenteredDslopeIter_zero
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0) (n : ℕ) :
    deriv (completedGreenCenteredDslopeIter response n) 0 =
      iteratedDeriv (n + 1) response 0 / ((n + 1).factorial : ℂ) := by
  rcases hresponse with ⟨series, hseries⟩
  have hshifted := hseries.has_fpower_series_iterate_dslope_fslope n
  calc
    deriv (completedGreenCenteredDslopeIter response n) 0 =
        ((FormalMultilinearSeries.fslope^[n]) series).coeff 1 := by
      change deriv ((Function.swap dslope 0)^[n] response) 0 =
        ((FormalMultilinearSeries.fslope^[n]) series) 1 (fun _ ↦ (1 : ℂ))
      exact hshifted.deriv
    _ = series.coeff (n + 1) := by
      rw [FormalMultilinearSeries.coeff_iterate_fslope]
      congr 1
      omega
    _ = iteratedDeriv (n + 1) response 0 /
          ((n + 1).factorial : ℂ) :=
      hasFPowerSeriesAt_coeff_eq_iteratedDeriv_div_factorial
        hseries (n + 1)

/-- The finite bivariate remainder converges jointly to the product of the
two matching binomial moments and the selected response coefficient. -/
theorem completedGreenDslopeTwoStepRemainder_tendsto
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ ↦
        completedGreenDslopeTwoStepRemainder response p q
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2))
      atTop
      (nhds ((p.factorial : ℂ) * (q.factorial : ℂ) *
        (iteratedDeriv (p + q + 1) response 0 /
          ((p + q + 1).factorial : ℂ)))) := by
  let shifted := completedGreenCenteredDslopeIter response (p + q)
  let coefficient := iteratedDeriv (p + q + 1) response 0 /
    ((p + q + 1).factorial : ℂ)
  have hshifted : AnalyticAt ℂ shifted 0 :=
    completedGreenCenteredDslopeIter_analyticAt hresponse (p + q)
  have hkernel : Tendsto
      (fun points : ℂ × ℂ ↦ dslope shifted points.1 points.2)
      (nhds (0, 0)) (nhds coefficient) := by
    have hjoint := completedGreenDslope_tendsto_prod_of_analyticAt hshifted
    have hcoeff : deriv shifted 0 = coefficient := by
      exact deriv_completedGreenCenteredDslopeIter_zero hresponse (p + q)
    rw [hcoeff] at hjoint
    exact hjoint
  have hsum : Tendsto
      (fun steps : ℕ × ℕ ↦
        completedGreenDslopeTwoStepRemainder response p q
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2))
      atTop
      (nhds
        (∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ∑ j ∈ Finset.range (q + 1),
              (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
                coefficient)) := by
    simpa [completedGreenDslopeTwoStepRemainder, shifted] using
      completedGreenTwoStepWeightedSum_tendsto hkernel p q
  have htarget :
      (∑ i ∈ Finset.range (p + 1),
        (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
          ∑ j ∈ Finset.range (q + 1),
            (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
              coefficient) =
        (p.factorial : ℂ) * (q.factorial : ℂ) * coefficient := by
    rw [show (∑ j ∈ Finset.range (q + 1),
          (completedGreenForwardWeight q j * (j : ℂ) ^ q) *
            coefficient) =
        completedGreenForwardWeightPower q q * coefficient by
      unfold completedGreenForwardWeightPower
      rw [Finset.sum_mul]]
    rw [completedGreenForwardWeightPower_self]
    rw [show (∑ i ∈ Finset.range (p + 1),
          (completedGreenForwardWeight p i * (i : ℂ) ^ p) *
            ((q.factorial : ℂ) * coefficient)) =
        completedGreenForwardWeightPower p p *
          ((q.factorial : ℂ) * coefficient) by
      unfold completedGreenForwardWeightPower
      rw [Finset.sum_mul]]
    rw [completedGreenForwardWeightPower_self]
    ring
  rw [htarget] at hsum
  simpa [coefficient] using hsum

/-- Every finite canonical sampling grid eventually lies in the analytic
neighborhood of all centered `dslope` iterates needed by one axis. -/
theorem completedGreenCenteredDslopeIter_grid_eventually_differentiableAt
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (order : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (order + 1),
        ∀ n ∈ Finset.range order,
          DifferentiableAt ℂ
            (completedGreenCenteredDslopeIter response (n + 1))
            ((i : ℂ) * canonicalGreenJetStep k) := by
  rw [eventually_all_finset]
  intro i hi
  rw [eventually_all_finset]
  intro n hn
  have hanalytic :=
    (completedGreenCenteredDslopeIter_analyticAt hresponse (n + 1)).eventually_analyticAt
  have hpoint : Tendsto
      (fun k : ℕ ↦ (i : ℂ) * canonicalGreenJetStep k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      canonicalGreenJetStep_tendsto_zero.const_mul (i : ℂ)
  exact (hpoint.eventually hanalytic).mono fun k hk ↦ hk.differentiableAt

/-- Along the product of canonical step sequences, the exact bivariate
factorization holds eventually with no additional hypothesis. -/
theorem completedGreenDslopeTwoStepSum_eventuallyEq_factor
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    (fun steps : ℕ × ℕ ↦
      completedGreenDslopeTwoStepSum response p q
        (canonicalGreenJetStep steps.1)
        (canonicalGreenJetStep steps.2)) =ᶠ[atTop]
    (fun steps : ℕ × ℕ ↦
      canonicalGreenJetStep steps.1 ^ p *
        canonicalGreenJetStep steps.2 ^ q *
          completedGreenDslopeTwoStepRemainder response p q
            (canonicalGreenJetStep steps.1)
            (canonicalGreenJetStep steps.2)) := by
  have hfirst :=
    completedGreenCenteredDslopeIter_grid_eventually_differentiableAt
      hresponse p
  have hpAnalytic :=
    completedGreenCenteredDslopeIter_analyticAt hresponse p
  have hsecond :=
    completedGreenCenteredDslopeIter_grid_eventually_differentiableAt
      hpAnalytic q
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  filter_upwards [hfst.eventually hfirst, hsnd.eventually hsecond] with
      steps hfirstSteps hsecondSteps
  exact completedGreenDslopeTwoStepSum_factor_remainder response p q
    (canonicalGreenJetStep steps.1) (canonicalGreenJetStep steps.2)
    (fun i hi n hn ↦ hfirstSteps i hi n (Finset.mem_range.mpr hn))
    (fun j hj n hn ↦ hsecondSteps j hj n (Finset.mem_range.mpr hn))

/-- After the exact bivariate factorization, the normalized two-step kernel
difference is eventually just the factorial-scaled finite remainder. -/
theorem completedGreenKernelTwoStepForwardDifference_dslope_eventuallyEq_remainder
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    (fun steps : ℕ × ℕ ↦
      completedGreenKernelTwoStepForwardDifference
        (fun w z ↦ dslope response w z)
        (canonicalGreenJetStep steps.1)
        (canonicalGreenJetStep steps.2) p q) =ᶠ[atTop]
    (fun steps : ℕ × ℕ ↦
      (((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹) *
        completedGreenDslopeTwoStepRemainder response p q
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2)) := by
  have hfactor :=
    completedGreenDslopeTwoStepSum_eventuallyEq_factor hresponse p q
  filter_upwards [hfactor] with steps hfactorSteps
  have hp : (p.factorial : ℂ) ≠ 0 := by
    exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast q.factorial_ne_zero
  have hh : canonicalGreenJetStep steps.1 ≠ 0 := by
    unfold canonicalGreenJetStep
    exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero steps.1)
  have hg : canonicalGreenJetStep steps.2 ≠ 0 := by
    unfold canonicalGreenJetStep
    exact inv_ne_zero (by exact_mod_cast Nat.succ_ne_zero steps.2)
  have hhStar : (starRingEnd ℂ) (canonicalGreenJetStep steps.1) =
      canonicalGreenJetStep steps.1 := by
    simp [canonicalGreenJetStep]
  rw [completedGreenKernelTwoStepForwardDifference,
    completedGreenDslope_twoStepMixedForwardDifference_eq_sum,
    hfactorSteps]
  simp only [map_inv₀, map_mul, map_pow, map_natCast, hhStar]
  field_simp [hp, hq, hh, hg]

/-- General scalar bivariate coefficient extraction for independent canonical
steps. -/
theorem completedGreenKernelTwoStepForwardDifference_dslope_tendsto
    {response : ℂ → ℂ} (hresponse : AnalyticAt ℂ response 0)
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ ↦
        completedGreenKernelTwoStepForwardDifference
          (fun w z ↦ dslope response w z)
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2) p q)
      atTop
      (nhds (iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ))) := by
  let scale : ℂ :=
    (((p.factorial : ℂ) * (q.factorial : ℂ))⁻¹)
  have hremainder :=
    completedGreenDslopeTwoStepRemainder_tendsto hresponse p q
  have hscaled := hremainder.const_mul scale
  have hp : (p.factorial : ℂ) ≠ 0 := by
    exact_mod_cast p.factorial_ne_zero
  have hq : (q.factorial : ℂ) ≠ 0 := by
    exact_mod_cast q.factorial_ne_zero
  have htarget : scale *
        ((p.factorial : ℂ) * (q.factorial : ℂ) *
          (iteratedDeriv (p + q + 1) response 0 /
            ((p + q + 1).factorial : ℂ))) =
      iteratedDeriv (p + q + 1) response 0 /
        ((p + q + 1).factorial : ℂ) := by
    dsimp [scale]
    field_simp [hp, hq]
  rw [htarget] at hscaled
  apply hscaled.congr'
  exact
    (completedGreenKernelTwoStepForwardDifference_dslope_eventuallyEq_remainder
      hresponse p q).symm

/-- Equality of two kernels on the finite rectangle generated by two
independent steps identifies their two-step normalized differences. -/
theorem completedGreenKernelTwoStepForwardDifference_eq_of_eq_on_grid
    (kernel kernel' : ℂ → ℂ → ℂ) (h g : ℂ) (p q : ℕ)
    (hkernel : ∀ i ∈ Finset.range (p + 1),
      ∀ j ∈ Finset.range (q + 1),
        kernel (i • h) (j • g) = kernel' (i • h) (j • g)) :
    completedGreenKernelTwoStepForwardDifference kernel h g p q =
      completedGreenKernelTwoStepForwardDifference kernel' h g p q := by
  unfold completedGreenKernelTwoStepForwardDifference
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  conv_rhs =>
    rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  conv_rhs =>
    rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact hkernel i hi j hj

/-- Joint cross-Gram convergence for independently varying canonical steps.
Unlike diagonal Gram convergence, this controls the distance between two
members of each approximating jet sequence. -/
def HasCompletedGreenForwardDifferenceCrossGramLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (moments : ℕ → ℝ) (state : ℂ → E) : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    Tendsto
      (fun steps : ℕ × ℕ ↦ (inner ℂ
        (completedGreenForwardDifferenceParityJet state steps.1 i)
        (completedGreenForwardDifferenceParityJet state steps.2 j)).re)
      atTop (nhds (greenWronskianMomentKernel moments i j))

/-- Purely scalar two-step coefficient statement for the canonical completed
native `dslope` kernel.  This is the analytic input needed for a vector limit;
it contains no Hilbert state or incidence transport. -/
def HasCompletedNativeGreenKernelTwoStepLimit : Prop :=
  ∀ i j : ℕ ⊕ ℕ,
    Tendsto
      (fun steps : ℕ × ℕ ↦
        (completedGreenKernelTwoStepForwardDifference
          (fun w z ↦ dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) w z)
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re)
      atTop
      (nhds (greenWronskianMomentKernel
        canonicalCompletedNativeLogDerivativeMoment i j))

/-- The completed native response satisfies the complex bivariate coefficient
limit for every pair of derivative orders. -/
theorem completedNativeGreenKernelTwoStepForwardDifference_dslope_tendsto
    (p q : ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ ↦
        completedGreenKernelTwoStepForwardDifference
          (fun w z ↦ dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) w z)
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2) p q)
      atTop
      (nhds (polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have hlimit := completedGreenKernelTwoStepForwardDifference_dslope_tendsto
    completedNativeGreenNormalizedResponse_analyticAt p q
  have hcoefficient :
      iteratedDeriv (p + q + 1)
          (completedGreenNormalizedResponse
            completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion) 0 /
        ((p + q + 1).factorial : ℂ) =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p q :=
    completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized p q
  rw [hcoefficient] at hlimit
  exact hlimit

/-- Real parts of the independent-step limits are the four canonical parity
blocks of the Green--Wronskian moment kernel. -/
theorem completedNativeGreenKernelTwoStepForwardDifference_dslope_re_tendsto
    (i j : ℕ ⊕ ℕ) :
    Tendsto
      (fun steps : ℕ × ℕ ↦
        (completedGreenKernelTwoStepForwardDifference
          (fun w z ↦ dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) w z)
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re)
      atTop
      (nhds (greenWronskianMomentKernel
        canonicalCompletedNativeLogDerivativeMoment i j)) := by
  have hcomplex :=
    completedNativeGreenKernelTwoStepForwardDifference_dslope_tendsto
      (completedGreenParityOrder i) (completedGreenParityOrder j)
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal
      | inr j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal
  | inr i =>
      cases j with
      | inl j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal
      | inr j =>
          simpa [Function.comp_def, completedGreenParityOrder,
            greenWronskianMomentKernel] using hreal

/-- Unconditional inhabitant of the scalar bivariate `dslope` gate. -/
theorem hasCompletedNativeGreenKernelTwoStepLimit :
    HasCompletedNativeGreenKernelTwoStepLimit := by
  intro i j
  exact
    completedNativeGreenKernelTwoStepForwardDifference_dslope_re_tendsto i j

/-- On every fixed finite two-step sampling rectangle, a real-axis normalized
Green state eventually has exactly the scalar completed `dslope` kernel. -/
theorem completedNative_kernelTwoStepForwardDifference_eventuallyEq_dslope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (p q : ℕ) :
    (fun steps : ℕ × ℕ ↦ completedGreenKernelTwoStepForwardDifference
      (fun w z ↦ inner ℂ
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state w)
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state z))
      (canonicalGreenJetStep steps.1)
      (canonicalGreenJetStep steps.2) p q) =ᶠ[atTop]
    (fun steps : ℕ × ℕ ↦ completedGreenKernelTwoStepForwardDifference
      (fun w z ↦ dslope
        (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) w z)
      (canonicalGreenJetStep steps.1)
      (canonicalGreenJetStep steps.2) p q) := by
  have hpOne : ∀ᶠ k : ℕ in atTop,
      ∀ i ∈ Finset.range (p + 1),
        completedNativeOperatorCharacteristic
          (i • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro i hi
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero i
  have hqOne : ∀ᶠ k : ℕ in atTop,
      ∀ j ∈ Finset.range (q + 1),
        completedNativeOperatorCharacteristic
          (j • canonicalGreenJetStep k) ≠ 0 := by
    rw [eventually_all_finset]
    intro j hj
    exact
      completedNativeOperatorCharacteristic_nsmul_canonicalGreenJetStep_eventually_ne_zero j
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  filter_upwards [hfst.eventually hpOne, hsnd.eventually hqOne] with
      steps hp hq
  apply completedGreenKernelTwoStepForwardDifference_eq_of_eq_on_grid
  intro i hi j hj
  rw [nsmul_canonicalGreenJetStep_eq_ofReal,
    nsmul_canonicalGreenJetStep_eq_ofReal]
  exact hkernel
    ((i : ℝ) * ((steps.1 : ℝ) + 1)⁻¹)
    ((j : ℝ) * ((steps.2 : ℝ) + 1)⁻¹)
    (by simpa [canonicalGreenJetStep] using hp i hi)
    (by simpa [canonicalGreenJetStep] using hq j hj)

/-- The scalar two-step limit and the exact real-axis kernel identity give the
joint cross-Gram convergence required by the Hilbert completion. -/
theorem hasCompletedGreenForwardDifferenceCrossGramLimit_of_realAxisKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hscalar : HasCompletedNativeGreenKernelTwoStepLimit) :
    HasCompletedGreenForwardDifferenceCrossGramLimit
      canonicalCompletedNativeLogDerivativeMoment
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state) := by
  intro i j
  let normalizedState := normalizedCompletedGreenState
    completedNativeOperatorCharacteristic state
  have hfinite :=
    completedNative_kernelTwoStepForwardDifference_eventuallyEq_dslope
      state hkernel
      (completedGreenParityOrder i) (completedGreenParityOrder j)
  have hgram :
      (fun steps : ℕ × ℕ ↦ (inner ℂ
        (completedGreenForwardDifferenceParityJet
          normalizedState steps.1 i)
        (completedGreenForwardDifferenceParityJet
          normalizedState steps.2 j)).re) =ᶠ[atTop]
      (fun steps : ℕ × ℕ ↦
        (completedGreenKernelTwoStepForwardDifference
          (fun w z ↦ dslope
            (completedGreenNormalizedResponse
              completedNativeOperatorCharacteristic
              completedNativeOperatorBoundaryCompanion) w z)
          (canonicalGreenJetStep steps.1)
          (canonicalGreenJetStep steps.2)
          (completedGreenParityOrder i)
          (completedGreenParityOrder j)).re) := by
    filter_upwards [hfinite] with steps hsteps
    have hi : completedGreenForwardDifferenceParityJet
        normalizedState steps.1 i =
        completedGreenForwardDifferenceJet normalizedState
          (canonicalGreenJetStep steps.1)
          (completedGreenParityOrder i) := by
      cases i <;> rfl
    have hj : completedGreenForwardDifferenceParityJet
        normalizedState steps.2 j =
        completedGreenForwardDifferenceJet normalizedState
          (canonicalGreenJetStep steps.2)
          (completedGreenParityOrder j) := by
      cases j <;> rfl
    rw [hi, hj,
      inner_completedGreenForwardDifferenceJet_twoStep_eq_kernel]
    exact congrArg Complex.re
      (by simpa [normalizedState] using hsteps)
  exact (hscalar i j).congr' hgram.symm

/-- The joint cross-Gram limit contains the previously used same-step Gram
limit by restriction to the diagonal sequence. -/
theorem HasCompletedGreenForwardDifferenceCrossGramLimit.toGramLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcross :
      HasCompletedGreenForwardDifferenceCrossGramLimit moments state) :
    HasCompletedGreenForwardDifferenceGramLimit moments state := by
  intro i j
  have hdiag := (hcross i j).comp
    (tendsto_atTop_diagonal (α := ℕ))
  change Tendsto
    (fun k ↦ (inner ℂ
      (completedGreenForwardDifferenceParityJet state k i)
      (completedGreenForwardDifferenceParityJet state k j)).re)
    atTop (nhds (greenWronskianMomentKernel moments i j)) at hdiag
  exact hdiag

/-- Cross-Gram convergence forces every fixed parity/order forward-difference
jet to be a Cauchy sequence in the Hilbert norm. -/
theorem cauchySeq_completedGreenForwardDifferenceParityJet_of_crossGramLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcross :
      HasCompletedGreenForwardDifferenceCrossGramLimit moments state)
    (i : ℕ ⊕ ℕ) :
    CauchySeq (fun k ↦ completedGreenForwardDifferenceParityJet state k i) := by
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  let jet : ℕ → E :=
    fun k ↦ completedGreenForwardDifferenceParityJet state k i
  let target : ℝ := greenWronskianMomentKernel moments i i
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hbase : Tendsto (fun steps : ℕ × ℕ ↦
      (inner ℂ (jet steps.1) (jet steps.2)).re)
      atTop (nhds target) := by
    simpa only [jet, target] using hcross i i
  have hdiagFst : Tendsto (fun steps : ℕ × ℕ ↦
      (inner ℂ (jet steps.1) (jet steps.1)).re)
      atTop (nhds target) := by
    have hpair : Tendsto (fun steps : ℕ × ℕ ↦ (steps.1, steps.1))
        atTop (atTop : Filter (ℕ × ℕ)) := by
      exact (tendsto_atTop_diagonal (α := ℕ)).comp hfst
    simpa only [Function.comp_def] using hbase.comp hpair
  have hdiagSnd : Tendsto (fun steps : ℕ × ℕ ↦
      (inner ℂ (jet steps.2) (jet steps.2)).re)
      atTop (nhds target) := by
    have hpair : Tendsto (fun steps : ℕ × ℕ ↦ (steps.2, steps.2))
        atTop (atTop : Filter (ℕ × ℕ)) := by
      exact (tendsto_atTop_diagonal (α := ℕ)).comp hsnd
    simpa only [Function.comp_def] using hbase.comp hpair
  have hmixed : Tendsto (fun steps : ℕ × ℕ ↦
      (inner ℂ (jet steps.1) (jet steps.2)).re)
      atTop (nhds target) := hbase
  have hsquare : Tendsto (fun steps : ℕ × ℕ ↦
      ‖jet steps.1 - jet steps.2‖ ^ 2) atTop (nhds 0) := by
    have hcombination := (hdiagFst.sub (hmixed.const_mul 2)).add hdiagSnd
    convert hcombination using 1
    · funext steps
      rw [norm_sub_sq (𝕜 := ℂ)]
      simp only [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq]
    · dsimp [target]
      ring_nf
  have hnorm : Tendsto (fun steps : ℕ × ℕ ↦
      ‖jet steps.1 - jet steps.2‖) atTop (nhds 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  simpa [jet, dist_eq_norm] using hnorm

/-- Concrete limit jet selected by completeness from the canonical
forward-difference approximants. -/
def completedGreenForwardDifferenceLimitParityJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (moments : ℕ → ℝ) (state : ℂ → E)
    (_hcross :
      HasCompletedGreenForwardDifferenceCrossGramLimit moments state) :
    (ℕ ⊕ ℕ) → E :=
  fun i ↦ limUnder atTop
    (fun k ↦ completedGreenForwardDifferenceParityJet state k i)

/-- Every finite-difference jet sequence converges to the selected completed
limit jet. -/
theorem completedGreenForwardDifferenceParityJet_tendsto_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcross :
      HasCompletedGreenForwardDifferenceCrossGramLimit moments state)
    (i : ℕ ⊕ ℕ) :
    Tendsto
      (fun k ↦ completedGreenForwardDifferenceParityJet state k i)
      atTop
      (nhds (completedGreenForwardDifferenceLimitParityJet
        moments state hcross i)) := by
  exact
    (cauchySeq_completedGreenForwardDifferenceParityJet_of_crossGramLimit
      hcross i).tendsto_limUnder

/-- The vectors obtained by completion realize the exact real
Green--Wronskian moment kernel. -/
theorem completedGreenForwardDifferenceLimitParityJet_momentKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {moments : ℕ → ℝ} {state : ℂ → E}
    (hcross :
      HasCompletedGreenForwardDifferenceCrossGramLimit moments state) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    IsGreenWronskianMomentKernelGramRepresentation moments
      (completedGreenForwardDifferenceLimitParityJet moments state hcross) := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  intro i j
  let limitJet := completedGreenForwardDifferenceLimitParityJet
    moments state hcross
  have hi := completedGreenForwardDifferenceParityJet_tendsto_limit hcross i
  have hj := completedGreenForwardDifferenceParityJet_tendsto_limit hcross j
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hinner : Tendsto (fun steps : ℕ × ℕ ↦
      (inner ℂ
        (completedGreenForwardDifferenceParityJet state steps.1 i)
        (completedGreenForwardDifferenceParityJet state steps.2 j)).re)
      atTop (nhds ((inner ℂ (limitJet i) (limitJet j)).re)) := by
    exact Complex.continuous_re.continuousAt.tendsto.comp
      ((hi.comp hfst).inner (hj.comp hsnd))
  have heq := tendsto_nhds_unique (hcross i j) hinner
  change greenWronskianMomentKernel moments i j =
    (Inner.rclikeToReal ℂ E).inner (limitJet i) (limitJet j)
  simpa only [real_inner_eq_re_inner, RCLike.re_eq_complex_re] using heq

/-- Canonical completed-native vector jet obtained from a concrete real-axis
Green state once the scalar two-step coefficient limit is available. -/
def completedNativeGreenForwardDifferenceLimitParityJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hscalar : HasCompletedNativeGreenKernelTwoStepLimit) :
    (ℕ ⊕ ℕ) → E :=
  completedGreenForwardDifferenceLimitParityJet
    canonicalCompletedNativeLogDerivativeMoment
    (normalizedCompletedGreenState
      completedNativeOperatorCharacteristic state)
    (hasCompletedGreenForwardDifferenceCrossGramLimit_of_realAxisKernel
      state hkernel hscalar)

/-- The preceding concrete limit jet has exactly the canonical completed
native moment Gram. -/
theorem completedNativeGreenForwardDifferenceLimitParityJet_momentKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (hscalar : HasCompletedNativeGreenKernelTwoStepLimit) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (completedNativeGreenForwardDifferenceLimitParityJet
        state hkernel hscalar) := by
  let hcross :=
    hasCompletedGreenForwardDifferenceCrossGramLimit_of_realAxisKernel
      state hkernel hscalar
  exact completedGreenForwardDifferenceLimitParityJet_momentKernel hcross

/-! ## Canonical completed-native specialization -/

/-- Joint cross-Gram convergence after discharging the scalar two-step gate
with its canonical inhabitant. -/
theorem hasCanonicalCompletedNativeGreenForwardDifferenceCrossGramLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    HasCompletedGreenForwardDifferenceCrossGramLimit
      canonicalCompletedNativeLogDerivativeMoment
      (normalizedCompletedGreenState
        completedNativeOperatorCharacteristic state) :=
  hasCompletedGreenForwardDifferenceCrossGramLimit_of_realAxisKernel
    state hkernel hasCompletedNativeGreenKernelTwoStepLimit

/-- Canonical completed-native limit jet.  The bivariate scalar limit is no
longer an argument: it is the proved `dslope` theorem. -/
def canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    (ℕ ⊕ ℕ) → E :=
  completedNativeGreenForwardDifferenceLimitParityJet
    state hkernel hasCompletedNativeGreenKernelTwoStepLimit

/-- Every canonical forward-difference approximant converges to the selected
completed-native limit vector. -/
theorem completedGreenForwardDifferenceParityJet_tendsto_canonicalNativeLimit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state)
    (i : ℕ ⊕ ℕ) :
    Tendsto
      (fun k ↦ completedGreenForwardDifferenceParityJet
        (normalizedCompletedGreenState
          completedNativeOperatorCharacteristic state) k i)
      atTop
      (nhds (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel i)) := by
  exact completedGreenForwardDifferenceParityJet_tendsto_limit
    (hasCanonicalCompletedNativeGreenForwardDifferenceCrossGramLimit
      state hkernel) i

/-- The canonical limit vectors realize the completed-native
Green--Wronskian moment kernel exactly. -/
theorem canonicalCompletedNativeGreenForwardDifferenceLimitParityJet_momentKernel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (state : ℂ → E)
    (hkernel : HasCompletedNativeRealAxisNormalizedGreenKernel state) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
    IsGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (canonicalCompletedNativeGreenForwardDifferenceLimitParityJet
        state hkernel) := by
  exact completedNativeGreenForwardDifferenceLimitParityJet_momentKernel
    state hkernel hasCompletedNativeGreenKernelTwoStepLimit

end

end CarrySelfAdjointOperator

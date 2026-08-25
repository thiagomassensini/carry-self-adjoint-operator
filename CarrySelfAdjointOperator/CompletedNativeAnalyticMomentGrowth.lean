import CarrySelfAdjointOperator.CompletedNativeJacobiCyclicReadout
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic

/-!
# Analytic growth and completed Jacobi resolvent convergence

Analyticity of the concrete completed native characteristic at the centered
origin gives a positive convergence radius for its even Taylor germ.  The
analytic logarithmic derivative of that germ has exactly the canonical real
moment coefficients already used by the completed Green/Jacobi construction.

Consequently the canonical moments and the completed even Green jets satisfy
geometric bounds.  This proves local summability of the cyclic Jacobi
resolvent series and makes its explicit terminal vector tend to zero, without
adding a compact-support, boundedness, zero-set, or spectral-height premise.
-/

open scoped BigOperators
open Filter Topology

namespace CarrySelfAdjointOperator

noncomputable section

private def completedNativeFullCharacteristicTaylorSeries :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n =>
    iteratedDeriv n completedNativeOperatorCharacteristic 0 / n.factorial

private theorem completedNativeFullCharacteristicTaylorSeries_radius_pos :
    0 < completedNativeFullCharacteristicTaylorSeries.radius := by
  exact ((completedNativeOperatorCharacteristic_analyticAt
    zero_mem_completedNativeHeightDomain).hasFPowerSeriesAt).radius_pos

/-- The concrete even Taylor coefficients grow at most geometrically. -/
theorem completedNativeEvenCharacteristicCoefficient_geometricBound :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ n : ℕ, ‖completedNativeEvenCharacteristicCoefficient n‖ ≤ C * r ^ n := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    completedNativeFullCharacteristicTaylorSeries.le_mul_pow_of_radius_pos
      completedNativeFullCharacteristicTaylorSeries_radius_pos
  refine ⟨C, r ^ 2, hC, sq_pos_of_pos hr, fun n => ?_⟩
  have hleft :
      ‖completedNativeEvenCharacteristicCoefficient n‖ =
        ‖completedNativeFullCharacteristicTaylorSeries (2 * n)‖ := by
    simp [completedNativeFullCharacteristicTaylorSeries,
      completedNativeEvenCharacteristicCoefficient, completedGreenTaylorJet,
      div_eq_mul_inv, mul_comm]
  rw [hleft, ← pow_mul]
  exact hbound (2 * n)

/-- Formal even characteristic series in the reduced variable `u = z^2`. -/
def completedNativeEvenCharacteristicSeries :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    completedNativeEvenCharacteristicCoefficient

theorem completedNativeEvenCharacteristicSeries_radius_pos :
    0 < completedNativeEvenCharacteristicSeries.radius := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    completedNativeEvenCharacteristicCoefficient_geometricBound
  let ρ : NNReal := ⟨1 / (2 * r), by positivity⟩
  have hρpos : 0 < ρ := by
    change 0 < 1 / (2 * r)
    positivity
  have hρle : (ρ : ENNReal) ≤ completedNativeEvenCharacteristicSeries.radius := by
    apply completedNativeEvenCharacteristicSeries.le_radius_of_bound C
    intro n
    change
      ‖FormalMultilinearSeries.ofScalars ℂ
          completedNativeEvenCharacteristicCoefficient n‖ * (ρ : ℝ) ^ n ≤ C
    rw [FormalMultilinearSeries.ofScalars_norm]
    calc
      ‖completedNativeEvenCharacteristicCoefficient n‖ * (ρ : ℝ) ^ n ≤
          (C * r ^ n) * (ρ : ℝ) ^ n := by
            exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)
      _ = C * (1 / 2 : ℝ) ^ n := by
            rw [mul_assoc, ← mul_pow]
            congr 2
            change r * (1 / (2 * r)) = (1 / 2 : ℝ)
            field_simp [ne_of_gt hr]
      _ ≤ C := by
            exact mul_le_of_le_one_right hC.le
              (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
                (by norm_num : (1 / 2 : ℝ) ≤ 1))
  exact lt_of_lt_of_le (by exact_mod_cast hρpos) hρle

/-- The analytic even characteristic germ reconstructed from the actual even
Taylor coefficients of the completed native characteristic. -/
def completedNativeEvenCharacteristic (u : ℂ) : ℂ :=
  completedNativeEvenCharacteristicSeries.sum u

theorem completedNativeEvenCharacteristic_hasFPowerSeriesAt :
    HasFPowerSeriesAt completedNativeEvenCharacteristic
      completedNativeEvenCharacteristicSeries 0 :=
  (completedNativeEvenCharacteristicSeries.hasFPowerSeriesOnBall
    completedNativeEvenCharacteristicSeries_radius_pos).hasFPowerSeriesAt

theorem completedNativeEvenCharacteristic_analyticAt :
    AnalyticAt ℂ completedNativeEvenCharacteristic 0 :=
  completedNativeEvenCharacteristic_hasFPowerSeriesAt.analyticAt

@[simp] theorem completedNativeEvenCharacteristic_zero :
    completedNativeEvenCharacteristic 0 =
      completedNativeEvenCharacteristicCoefficient 0 := by
  simpa [completedNativeEvenCharacteristic,
    completedNativeEvenCharacteristicSeries] using
    (completedNativeEvenCharacteristic_hasFPowerSeriesAt.coeff_zero
      (fun _ => 0)).symm

theorem completedNativeEvenCharacteristic_zero_ne_zero :
    completedNativeEvenCharacteristic 0 ≠ 0 := by
  rw [completedNativeEvenCharacteristic_zero]
  exact completedNativeEvenCharacteristicCoefficient_zero_ne_zero

/-- Actual analytic logarithmic derivative of the reconstructed even germ. -/
def completedNativeLogDerivative (u : ℂ) : ℂ :=
  -deriv completedNativeEvenCharacteristic u /
    completedNativeEvenCharacteristic u

theorem completedNativeLogDerivative_analyticAt :
    AnalyticAt ℂ completedNativeLogDerivative 0 := by
  exact completedNativeEvenCharacteristic_analyticAt.deriv.neg.div
    completedNativeEvenCharacteristic_analyticAt
    completedNativeEvenCharacteristic_zero_ne_zero

/-- Taylor coefficients of the analytic logarithmic derivative germ. -/
def completedNativeLogDerivativeTaylorCoefficient (n : ℕ) : ℂ :=
  iteratedDeriv n completedNativeLogDerivative 0 / n.factorial

private def completedNativeLogDerivativeTaylorSeries :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    completedNativeLogDerivativeTaylorCoefficient

private theorem completedNativeLogDerivativeTaylorSeries_radius_pos :
    0 < completedNativeLogDerivativeTaylorSeries.radius := by
  exact completedNativeLogDerivative_analyticAt.hasFPowerSeriesAt.radius_pos

theorem completedNativeLogDerivativeTaylorCoefficient_geometricBound :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ n : ℕ,
        ‖completedNativeLogDerivativeTaylorCoefficient n‖ ≤ C * r ^ n := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    completedNativeLogDerivativeTaylorSeries.le_mul_pow_of_radius_pos
      completedNativeLogDerivativeTaylorSeries_radius_pos
  refine ⟨C, r, hC, hr, fun n => ?_⟩
  simpa [completedNativeLogDerivativeTaylorSeries,
    FormalMultilinearSeries.ofScalars_norm] using hbound n

theorem completedNativeEvenCharacteristic_taylorCoefficient
    (n : ℕ) :
    iteratedDeriv n completedNativeEvenCharacteristic 0 / n.factorial =
      completedNativeEvenCharacteristicCoefficient n := by
  have hseries :=
    completedNativeEvenCharacteristic_hasFPowerSeriesAt.eq_formalMultilinearSeries
      completedNativeEvenCharacteristic_analyticAt.hasFPowerSeriesAt
  have hn := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => 1)) hseries
  simpa [completedNativeEvenCharacteristicSeries,
    FormalMultilinearSeries.ofScalars_apply_eq] using hn.symm

theorem completedNativeLogDerivative_mul_evenCharacteristic_eventually :
    Filter.Eventually
      (fun u => completedNativeLogDerivative u *
          completedNativeEvenCharacteristic u =
        -deriv completedNativeEvenCharacteristic u)
      (nhds (0 : ℂ)) := by
  filter_upwards [completedNativeEvenCharacteristic_analyticAt.continuousAt.eventually_ne
    completedNativeEvenCharacteristic_zero_ne_zero] with u hu
  simp [completedNativeLogDerivative, hu]

theorem completedNativeLogDerivative_rawDerivativeRecurrence
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) *
          iteratedDeriv i completedNativeLogDerivative 0 *
          iteratedDeriv (n - i) completedNativeEvenCharacteristic 0 =
      -iteratedDeriv (n + 1) completedNativeEvenCharacteristic 0 := by
  calc
    _ = iteratedDeriv n
        (fun u => completedNativeLogDerivative u *
          completedNativeEvenCharacteristic u) 0 := by
      change _ = iteratedDeriv n
        (completedNativeLogDerivative *
          completedNativeEvenCharacteristic) 0
      exact (iteratedDeriv_mul
        completedNativeLogDerivative_analyticAt.contDiffAt
        completedNativeEvenCharacteristic_analyticAt.contDiffAt).symm
    _ = iteratedDeriv n
        (fun u => -deriv completedNativeEvenCharacteristic u) 0 :=
      Filter.EventuallyEq.iteratedDeriv_eq n
        completedNativeLogDerivative_mul_evenCharacteristic_eventually
    _ = -iteratedDeriv (n + 1)
        completedNativeEvenCharacteristic 0 := by
      rw [iteratedDeriv_fun_neg, iteratedDeriv_succ']

theorem completedNativeLogDerivative_iteratedDeriv_eq
    (n : ℕ) :
    iteratedDeriv n completedNativeLogDerivative 0 =
      (n.factorial : ℂ) *
        completedNativeLogDerivativeTaylorCoefficient n := by
  rw [completedNativeLogDerivativeTaylorCoefficient]
  field_simp [show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero]

theorem completedNativeEvenCharacteristic_iteratedDeriv_eq
    (n : ℕ) :
    iteratedDeriv n completedNativeEvenCharacteristic 0 =
      (n.factorial : ℂ) *
        completedNativeEvenCharacteristicCoefficient n := by
  have h := completedNativeEvenCharacteristic_taylorCoefficient n
  rw [div_eq_iff] at h
  · rw [h]
    ring
  · exact_mod_cast n.factorial_ne_zero

theorem completedNativeLogDerivative_coefficientRecurrence
    (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        completedNativeLogDerivativeTaylorCoefficient i *
          completedNativeEvenCharacteristicCoefficient (n - i) =
      -(((n + 1 : ℕ) : ℂ) *
        completedNativeEvenCharacteristicCoefficient (n + 1)) := by
  have hraw := completedNativeLogDerivative_rawDerivativeRecurrence n
  have hsum :
      ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i completedNativeLogDerivative 0 *
            iteratedDeriv (n - i)
              completedNativeEvenCharacteristic 0 =
        (n.factorial : ℂ) *
          ∑ i ∈ Finset.range (n + 1),
            completedNativeLogDerivativeTaylorCoefficient i *
              completedNativeEvenCharacteristicCoefficient (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [completedNativeLogDerivative_iteratedDeriv_eq,
      completedNativeEvenCharacteristic_iteratedDeriv_eq]
    have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hfactorial :
        (n.choose i : ℂ) * (i.factorial : ℂ) *
            ((n - i).factorial : ℂ) =
          (n.factorial : ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
    calc
      (n.choose i : ℂ) *
            ((i.factorial : ℂ) *
              completedNativeLogDerivativeTaylorCoefficient i) *
            (((n - i).factorial : ℂ) *
              completedNativeEvenCharacteristicCoefficient (n - i)) =
          ((n.choose i : ℂ) * (i.factorial : ℂ) *
              ((n - i).factorial : ℂ)) *
            (completedNativeLogDerivativeTaylorCoefficient i *
              completedNativeEvenCharacteristicCoefficient (n - i)) := by ring
      _ = (n.factorial : ℂ) *
            (completedNativeLogDerivativeTaylorCoefficient i *
              completedNativeEvenCharacteristicCoefficient (n - i)) := by
          rw [hfactorial]
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)
  calc
    (n.factorial : ℂ) *
          ∑ i ∈ Finset.range (n + 1),
            completedNativeLogDerivativeTaylorCoefficient i *
              completedNativeEvenCharacteristicCoefficient (n - i) =
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) *
            iteratedDeriv i completedNativeLogDerivative 0 *
            iteratedDeriv (n - i)
              completedNativeEvenCharacteristic 0 := hsum.symm
    _ = -iteratedDeriv (n + 1)
          completedNativeEvenCharacteristic 0 := hraw
    _ = (n.factorial : ℂ) *
          (-(((n + 1 : ℕ) : ℂ) *
            completedNativeEvenCharacteristicCoefficient (n + 1))) := by
      rw [completedNativeEvenCharacteristic_iteratedDeriv_eq,
        Nat.factorial_succ]
      push_cast
      ring

/-- The analytic logarithmic-derivative coefficients are exactly the
division-free canonical real moments already used by the Jacobi tower. -/
theorem completedNativeLogDerivativeTaylorCoefficient_eq_canonical
    (n : ℕ) :
    completedNativeLogDerivativeTaylorCoefficient n =
      (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hrest :
          ∑ k ∈ Finset.range n,
              completedNativeLogDerivativeTaylorCoefficient k *
                completedNativeEvenCharacteristicCoefficient (n - k) =
            ∑ k ∈ Finset.range n,
              (canonicalCompletedNativeLogDerivativeMoment k : ℂ) *
                completedNativeEvenCharacteristicCoefficient (n - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ih k (Finset.mem_range.mp hk)]
      have hanalytic :=
        completedNativeLogDerivative_coefficientRecurrence n
      have hcanonical :=
        completedNativeLogDerivativeMoment_fullConvolution
          canonicalCompletedNativeLogDerivativeMoment_isMomentSequence n
      rw [Finset.sum_range_succ] at hanalytic hcanonical
      simp only [Nat.sub_self] at hanalytic hcanonical
      rw [hrest] at hanalytic
      have hproduct :
          completedNativeLogDerivativeTaylorCoefficient n *
              completedNativeEvenCharacteristicCoefficient 0 =
            (canonicalCompletedNativeLogDerivativeMoment n : ℂ) *
              completedNativeEvenCharacteristicCoefficient 0 := by
        apply add_left_cancel
        exact hanalytic.trans hcanonical.symm
      exact mul_right_cancel₀
        completedNativeEvenCharacteristicCoefficient_zero_ne_zero hproduct

/-- The canonical completed-native logarithmic moments have a concrete
geometric growth bound derived from analyticity. -/
theorem canonicalCompletedNativeLogDerivativeMoment_geometricBound :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      ∀ n : ℕ,
        |canonicalCompletedNativeLogDerivativeMoment n| ≤ C * r ^ n := by
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    completedNativeLogDerivativeTaylorCoefficient_geometricBound
  refine ⟨C, r, hC, hr, fun n => ?_⟩
  have hn := hbound n
  rw [completedNativeLogDerivativeTaylorCoefficient_eq_canonical] at hn
  simpa using hn

namespace CompletedNativeGreenWeylHeightCertificate

/-- The completed even Green jet has squared norm equal to its diagonal
canonical moment. -/
theorem completedGreenEvenJet_norm_sq_eq_canonicalMoment
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments)
    (n : ℕ) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ‖greenJetEvenSectorJet jet n‖ ^ 2 =
      canonicalCompletedNativeLogDerivativeMoment (2 * n) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  rw [← real_inner_self_eq_norm_sq,
    inner_greenJetEvenSectorJet_eq_moment
      (completedGreenJet_gramRepresentation certificate.realMomentKernel)]
  rw [completedNativeLogDerivativeMoment_eq_canonical
    certificate.logarithmicMoments]
  congr 1
  omega

/-- Completed even Green jets inherit geometric norm growth from the
canonical moments. -/
theorem completedGreenEvenJet_norm_geometricBound
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ D r : ℝ, 0 < D ∧ 0 < r ∧
      ∀ n : ℕ, ‖greenJetEvenSectorJet jet n‖ ≤ D * r ^ n := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  obtain ⟨C, r, hC, hr, hbound⟩ :=
    canonicalCompletedNativeLogDerivativeMoment_geometricBound
  refine ⟨Real.sqrt C, r, Real.sqrt_pos.2 hC, hr, fun n => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hr.le _))).mp
  calc
    ‖greenJetEvenSectorJet
        (completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)) n‖ ^ 2 =
        canonicalCompletedNativeLogDerivativeMoment (2 * n) :=
      certificate.completedGreenEvenJet_norm_sq_eq_canonicalMoment n
    _ ≤ |canonicalCompletedNativeLogDerivativeMoment (2 * n)| :=
      le_abs_self _
    _ ≤ C * r ^ (2 * n) := hbound (2 * n)
    _ = (Real.sqrt C * r ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC.le, ← pow_mul]
      congr 2
      omega

set_option synthInstance.maxHeartbeats 200000 in
/-- The local cyclic Jacobi resolvent series is summable in the actual
completed Green Hilbert carrier. -/
theorem completedJacobiResolventSeries_summable
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      Summable (fun n : ℕ => u ^ n • greenJetEvenSectorJet jet n) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨D, r, hD, hr, hbound⟩ :=
    certificate.completedGreenEvenJet_norm_geometricBound
  refine ⟨r, hr, fun u hu => ?_⟩
  refine ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg u) hr.le) hu).mul_left D).of_norm_bounded
      (fun n => ?_)
  calc
    ‖u ^ n • greenJetEvenSectorJet
        (completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)) n‖ =
        |u| ^ n *
          ‖greenJetEvenSectorJet
            (completedGreenJet
              (canonicalCompletedNativeGreenParityJet xiState)) n‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_pow]
    _ ≤ |u| ^ n * (D * r ^ n) := by
          exact mul_le_mul_of_nonneg_left (hbound n) (pow_nonneg (abs_nonneg u) _)
    _ = D * (|u| * r) ^ n := by
          rw [mul_pow]
          ring

set_option synthInstance.maxHeartbeats 200000 in
/-- Finite cyclic resolvent prefixes converge to their vector-valued sum. -/
theorem completedJacobiResolventPrefix_tendsto_tsum
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      Tendsto
        (fun N : ℕ =>
          (greenJetJacobiCoreResolventPrefix (jet := jet) u N :
            greenJetEvenHilbertSubspace jet))
        atTop
        (nhds (∑' n : ℕ,
          u ^ n • greenJetEvenSectorJet jet n)) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨r, hr, hsummable⟩ :=
    certificate.completedJacobiResolventSeries_summable
  refine ⟨r, hr, fun u hu => ?_⟩
  have hsum := (hsummable u hu).hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_add_atTop_nat 1)
  convert hsum using 1
  funext N
  simp [greenJetJacobiCoreResolventPrefix,
    greenJetEvenCoreJet]

/-- The cyclic endomorphism sends each finite resolvent prefix to the
corresponding finite shifted-jet sum. -/
theorem greenJetJacobiCoreEndomorphism_resolventPrefix_eq_shiftedSum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {jet : (ℕ ⊕ ℕ) → E}
    (heven : LinearIndependent ℝ (fun n : ℕ => jet (Sum.inl n)))
    (u : ℝ) (N : ℕ) :
    (((greenJetJacobiCoreEndomorphism heven
        (greenJetJacobiCoreResolventPrefix (jet := jet) u N) :
          greenJetEvenOperatorCore jet) :
      greenJetEvenHilbertSubspace jet)) =
      ∑ k ∈ Finset.range (N + 1),
        u ^ k • greenJetEvenSectorJet jet (k + 1) := by
  rw [greenJetJacobiCoreEndomorphism_coe]
  unfold greenJetJacobiCoreResolventPrefix
  rw [map_sum]
  simp [greenJetJacobiCoreMap_jet]

set_option synthInstance.maxHeartbeats 200000 in
/-- The image series obtained by advancing every completed Green jet once is
summable on the same kind of nontrivial neighborhood as the resolvent
series. -/
theorem completedJacobiShiftedSeries_summable
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      Summable (fun n : ℕ =>
        u ^ n • greenJetEvenSectorJet jet (n + 1)) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨D, r, hD, hr, hbound⟩ :=
    certificate.completedGreenEvenJet_norm_geometricBound
  refine ⟨r, hr, fun u hu => ?_⟩
  refine ((summable_geometric_of_lt_one
    (mul_nonneg (abs_nonneg u) hr.le) hu).mul_left (D * r)).of_norm_bounded
      (fun n => ?_)
  calc
    ‖u ^ n • greenJetEvenSectorJet
        (completedGreenJet
          (canonicalCompletedNativeGreenParityJet xiState)) (n + 1)‖ =
        |u| ^ n *
          ‖greenJetEvenSectorJet
            (completedGreenJet
              (canonicalCompletedNativeGreenParityJet xiState)) (n + 1)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_pow]
    _ ≤ |u| ^ n * (D * r ^ (n + 1)) := by
          exact mul_le_mul_of_nonneg_left (hbound (n + 1))
            (pow_nonneg (abs_nonneg u) _)
    _ = (D * r) * (|u| * r) ^ n := by
          rw [pow_succ, mul_pow]
          ring

/-- Finite shifted-jet sums converge to the image-series sum. -/
theorem completedJacobiShiftedPrefix_tendsto_tsum
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range (N + 1),
            u ^ k • greenJetEvenSectorJet jet (k + 1))
        atTop
        (nhds (∑' n : ℕ,
          u ^ n • greenJetEvenSectorJet jet (n + 1))) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨r, hr, hsummable⟩ :=
    certificate.completedJacobiShiftedSeries_summable
  refine ⟨r, hr, fun u hu => ?_⟩
  have hsum := (hsummable u hu).hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_add_atTop_nat 1)
  convert hsum using 1
  funext N
  simp

set_option maxHeartbeats 800000 in
/-- The completed resolvent series and its shifted series form a point of the
closed graph of the actual Green maximal-adjoint square.  Thus the formal
Jacobi shift survives completion as the action of the global operator. -/
theorem completedJacobiResolventTsum_mem_closedAdjointSquareGraph
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    let hrep := completedGreenJet_gramRepresentation
      certificate.realMomentKernel
    let heven := completedGreenJet_even_linearIndependent
      certificate.evenIndependent
    let hodd := completedGreenJet_odd_linearIndependent
      certificate.oddIndependent
    let A := closedGreenJetEnergyAdjointSquare hrep heven hodd
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      ((∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n),
          (∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet (n + 1))) ∈
        A.graph := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  let hrep := completedGreenJet_gramRepresentation
    certificate.realMomentKernel
  let heven := completedGreenJet_even_linearIndependent
    certificate.evenIndependent
  let hodd := completedGreenJet_odd_linearIndependent
    certificate.oddIndependent
  let A := closedGreenJetEnergyAdjointSquare hrep heven hodd
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨rx, hrx, hxPrefix⟩ :=
    certificate.completedJacobiResolventPrefix_tendsto_tsum
  obtain ⟨ry, hry, hyPrefix⟩ :=
    certificate.completedJacobiShiftedPrefix_tendsto_tsum
  refine ⟨max rx ry, lt_of_lt_of_le hrx (le_max_left _ _), fun u hu => ?_⟩
  have hux : |u| * rx < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (le_max_left rx ry) (abs_nonneg u)) hu
  have huy : |u| * ry < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (le_max_right rx ry) (abs_nonneg u)) hu
  have hx := hxPrefix u hux
  have hy := hyPrefix u huy
  have hpairs := hx.prodMk_nhds hy
  apply (closedGreenJetEnergyAdjointSquare_isClosed hrep heven hodd).mem_of_tendsto
    hpairs
  filter_upwards [] with N
  let xN := greenJetJacobiCoreResolventPrefix (jet := jet) u N
  let dxN := greenJetEvenCoreInClosedAdjointSquareDomain
    hrep heven hodd xN
  change
    (((greenJetJacobiCoreResolventPrefix (jet := jet) u N :
        greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet),
      ∑ k ∈ Finset.range (N + 1),
        u ^ k • greenJetEvenSectorJet jet (k + 1)) ∈ A.graph
  rw [LinearPMap.mem_graph_iff]
  refine ⟨dxN, ?_, ?_⟩
  · rfl
  · rw [certificate.completedEnergyAdjointSquare_apply_core_eq_cyclicEndomorphism]
    exact greenJetJacobiCoreEndomorphism_resolventPrefix_eq_shiftedSum
      heven u N

/-- The explicit terminal term in the finite cyclic resolvent identity tends
to zero throughout a nontrivial neighborhood of the centered origin. -/
theorem completedJacobiResolventTerminal_tendsto_zero
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      Tendsto
        (fun N : ℕ =>
          u ^ (N + 1) • greenJetEvenSectorJet jet (N + 1))
        atTop (nhds 0) := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  obtain ⟨D, r, hD, hr, hbound⟩ :=
    certificate.completedGreenEvenJet_norm_geometricBound
  refine ⟨r, hr, fun u hu => ?_⟩
  refine squeeze_zero_norm
    (a := fun N : ℕ => D * (|u| * r) ^ (N + 1))
    (fun N => ?_) ?_
  · calc
      ‖u ^ (N + 1) •
          greenJetEvenSectorJet
            (completedGreenJet
              (canonicalCompletedNativeGreenParityJet xiState)) (N + 1)‖ =
          |u| ^ (N + 1) *
            ‖greenJetEvenSectorJet
              (completedGreenJet
                (canonicalCompletedNativeGreenParityJet xiState)) (N + 1)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_pow]
      _ ≤ |u| ^ (N + 1) * (D * r ^ (N + 1)) := by
            gcongr
            exact hbound (N + 1)
      _ = D * (|u| * r) ^ (N + 1) := by
            rw [mul_pow]
            ring
  · simpa only [Function.comp_apply, mul_zero] using
      (tendsto_const_nhds.mul
        ((tendsto_pow_atTop_nhds_zero_of_lt_one
          (mul_nonneg (abs_nonneg u) hr.le) hu).comp
            (Filter.tendsto_add_atTop_nat 1)) :
        Tendsto (fun N : ℕ => D * (|u| * r) ^ (N + 1))
          atTop (nhds (D * 0)))

set_option maxHeartbeats 4000000 in
/-- Local completed resolvent certificate for the global positive operator.
The domain vector is the sum of the actual completed Green jets, its operator
image is the shifted sum, and the exact resolvent equation holds without a
remaining terminal defect. -/
theorem completedJacobiResolventTsum_closedAdjointSquareCertificate
    {Hxi : Type*}
    [NormedAddCommGroup Hxi] [InnerProductSpace ℂ Hxi]
    {xiState : ℂ → Hxi} {moments : ℕ → ℝ}
    (certificate :
      CompletedNativeGreenWeylHeightCertificate xiState moments) :
    letI : InnerProductSpace ℝ
        (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
      InnerProductSpace.rclikeToReal ℂ _
    let jet := completedGreenJet
      (canonicalCompletedNativeGreenParityJet xiState)
    let hrep := completedGreenJet_gramRepresentation
      certificate.realMomentKernel
    let heven := completedGreenJet_even_linearIndependent
      certificate.evenIndependent
    let hodd := completedGreenJet_odd_linearIndependent
      certificate.oddIndependent
    let A := closedGreenJetEnergyAdjointSquare hrep heven hodd
    ∃ r : ℝ, 0 < r ∧ ∀ u : ℝ, |u| * r < 1 →
      ∃ xu : A.domain,
        (xu : greenJetEvenHilbertSubspace jet) =
            ∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n ∧
        A xu =
            ∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet (n + 1) ∧
        (xu : greenJetEvenHilbertSubspace jet) - u • A xu =
            greenJetEvenSectorJet jet 0 := by
  letI : InnerProductSpace ℝ
      (BinaryHilbertSum Hxi CanonicalCompletedC3HilbertCarrier) :=
    InnerProductSpace.rclikeToReal ℂ _
  dsimp only
  let jet := completedGreenJet
    (canonicalCompletedNativeGreenParityJet xiState)
  let hrep := completedGreenJet_gramRepresentation
    certificate.realMomentKernel
  let heven := completedGreenJet_even_linearIndependent
    certificate.evenIndependent
  let hodd := completedGreenJet_odd_linearIndependent
    certificate.oddIndependent
  let A := closedGreenJetEnergyAdjointSquare hrep heven hodd
  letI : CompleteSpace (greenJetEvenHilbertSubspace jet) :=
    (greenJetEvenHilbertSubspace_isClosed jet).completeSpace_coe
  obtain ⟨rg, hrg, hgraph⟩ :=
    certificate.completedJacobiResolventTsum_mem_closedAdjointSquareGraph
  obtain ⟨rx, hrx, hxPrefix⟩ :=
    certificate.completedJacobiResolventPrefix_tendsto_tsum
  obtain ⟨ry, hry, hyPrefix⟩ :=
    certificate.completedJacobiShiftedPrefix_tendsto_tsum
  obtain ⟨rt, hrt, hterminal⟩ :=
    certificate.completedJacobiResolventTerminal_tendsto_zero
  let r := max rg (max rx (max ry rt))
  have hr : 0 < r := lt_of_lt_of_le hrg (le_max_left _ _)
  refine ⟨r, hr, fun u hu => ?_⟩
  have hrg_le : rg ≤ r := le_max_left _ _
  have hrx_le : rx ≤ r := by
    exact (le_max_left rx (max ry rt)).trans (le_max_right rg _)
  have hry_le : ry ≤ r := by
    exact (le_max_left ry rt).trans
      ((le_max_right rx _).trans (le_max_right rg _))
  have hrt_le : rt ≤ r := by
    exact (le_max_right ry rt).trans
      ((le_max_right rx _).trans (le_max_right rg _))
  have hu_of_le {q : ℝ} (hq : q ≤ r) : |u| * q < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hq (abs_nonneg u)) hu
  have hgraphu := hgraph u (hu_of_le hrg_le)
  rw [LinearPMap.mem_graph_iff] at hgraphu
  rcases hgraphu with ⟨xu, hxu, hAxu⟩
  have hx := hxPrefix u (hu_of_le hrx_le)
  have hy := hyPrefix u (hu_of_le hry_le)
  have ht := hterminal u (hu_of_le hrt_le)
  have hfinite : ∀ N : ℕ,
      ((greenJetJacobiCoreResolventPrefix (jet := jet) u N :
          greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet) -
          u • (∑ k ∈ Finset.range (N + 1),
            u ^ k • greenJetEvenSectorJet jet (k + 1)) =
        greenJetEvenSectorJet jet 0 -
          u ^ (N + 1) • greenJetEvenSectorJet jet (N + 1) := by
    intro N
    have hcore := greenJetJacobiCoreResolventPrefix_sub_smul_shift
      heven u N
    have hshift :=
      greenJetJacobiCoreEndomorphism_resolventPrefix_eq_shiftedSum
        heven u N
    calc
      ((greenJetJacobiCoreResolventPrefix (jet := jet) u N :
            greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet) -
          u • (∑ k ∈ Finset.range (N + 1),
            u ^ k • greenJetEvenSectorJet jet (k + 1)) =
        ((greenJetJacobiCoreResolventPrefix (jet := jet) u N :
            greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet) -
          u • (((greenJetJacobiCoreEndomorphism heven
            (greenJetJacobiCoreResolventPrefix (jet := jet) u N) :
              greenJetEvenOperatorCore jet) :
            greenJetEvenHilbertSubspace jet)) := by rw [hshift]
      _ = ((greenJetJacobiCoreResolventPrefix (jet := jet) u N -
          u • greenJetJacobiCoreEndomorphism heven
            (greenJetJacobiCoreResolventPrefix (jet := jet) u N) :
          greenJetEvenOperatorCore jet) :
          greenJetEvenHilbertSubspace jet) := rfl
      _ = ((greenJetEvenCoreJet jet 0 -
          u ^ (N + 1) • greenJetEvenCoreJet jet (N + 1) :
          greenJetEvenOperatorCore jet) :
          greenJetEvenHilbertSubspace jet) := congrArg
            (greenJetEvenOperatorCore jet).subtype hcore
      _ = greenJetEvenSectorJet jet 0 -
          u ^ (N + 1) • greenJetEvenSectorJet jet (N + 1) := rfl
  have hleft : Tendsto
      (fun N : ℕ =>
        ((greenJetJacobiCoreResolventPrefix (jet := jet) u N :
            greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet) -
          u • (∑ k ∈ Finset.range (N + 1),
            u ^ k • greenJetEvenSectorJet jet (k + 1)))
      atTop
      (nhds ((∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n) -
        u • (∑' n : ℕ,
          u ^ n • greenJetEvenSectorJet jet (n + 1)))) :=
    hx.sub (tendsto_const_nhds.smul hy)
  have hright : Tendsto
      (fun N : ℕ => greenJetEvenSectorJet jet 0 -
        u ^ (N + 1) • greenJetEvenSectorJet jet (N + 1))
      atTop (nhds (greenJetEvenSectorJet jet 0 - 0)) :=
    tendsto_const_nhds.sub ht
  have hright' : Tendsto
      (fun N : ℕ =>
        ((greenJetJacobiCoreResolventPrefix (jet := jet) u N :
            greenJetEvenOperatorCore jet) : greenJetEvenHilbertSubspace jet) -
          u • (∑ k ∈ Finset.range (N + 1),
            u ^ k • greenJetEvenSectorJet jet (k + 1)))
      atTop (nhds (greenJetEvenSectorJet jet 0 - 0)) := by
    exact hright.congr' (Filter.Eventually.of_forall
      (fun N => (hfinite N).symm))
  have hresolvent :
      (∑' n : ℕ, u ^ n • greenJetEvenSectorJet jet n) -
          u • (∑' n : ℕ,
            u ^ n • greenJetEvenSectorJet jet (n + 1)) =
        greenJetEvenSectorJet jet 0 := by
    simpa using tendsto_nhds_unique hleft hright'
  refine ⟨xu, hxu, hAxu, ?_⟩
  rw [hxu, hAxu]
  exact hresolvent

end CompletedNativeGreenWeylHeightCertificate

end

end CarrySelfAdjointOperator

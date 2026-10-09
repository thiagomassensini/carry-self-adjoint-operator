import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenSourceRemainderParity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Which finite-step terms change the seven-boundary margin?

The boundary defect and the analytic source remainder are kept separately.
The first reconstructed higher coordinate is B_7 = 28 h x_6 + O(h^2).
This creates a signed even/odd cross; no coordinate is discarded or fitted.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The actual finite-prefix correction relative to its own limiting face. -/
def radialSevenBoundaryMarginLoss (h : ℝ) (x : Fin 7 → ℂ) : ℝ :=
  radialSevenRegularizedBoundaryEnergy h x - nativeSourceSevenBoundaryEnergy x

/-- Exact two-term correction of the complete storage chart. -/
theorem radialSevenRegularizedStorage_margin_decomposition (R : ℂ → ℂ) (h : ℝ)
    (x : Fin 7 → ℂ) :
    radialSevenRegularizedStorage R h x = nativeSourceSevenBoundaryEnergy x +
      radialSevenBoundaryMarginLoss h x + radialSevenRegularizedRemainderEnergy R h x := by
  unfold radialSevenRegularizedStorage radialSevenBoundaryMarginLoss
  ring

/-- 28 is fixed by the seven original node multipliers, not by source values. -/
theorem radialSevenHigherBoundaryCoefficient_seven_six :
    radialSevenHigherBoundaryCoefficient 7 (6 : Fin 7) = 28 := by
  norm_num [radialSevenHigherBoundaryCoefficient, radialSevenBoundaryInverseCoefficients,
    Fin.sum_univ_succ]
  change 1/720 + (128*(-(1/120)) + (2187*(1/48) + (16384*(-(1/36)) +
    (78125*(1/48) + (279936*(-(1/120)) + 823543*(1/720)))))) = (28 : ℝ)
  norm_num

/-- Only the first higher coordinate has a nonzero first-order jet. -/
theorem radialSevenRegularizedBoundary_hasDerivAt_zero (x : Fin 7 → ℂ) (m : ℕ) :
    HasDerivAt (fun h : ℝ => radialSevenRegularizedBoundary h x m)
      (if m = 7 then (28 : ℂ)*x 6 else 0) 0 := by
  by_cases hm : m < 7
  · have hne : m ≠ 7 := by omega
    simpa only [radialSevenRegularizedBoundary, dif_pos hm, hne, if_false] using
      hasDerivAt_const (0 : ℝ) (x ⟨m,hm⟩)
  · simp only [radialSevenRegularizedBoundary, dif_neg hm]
    have ht (a : Fin 7) : HasDerivAt
        (fun h : ℝ => ((h^(m-(a : ℕ))*radialSevenHigherBoundaryCoefficient m a : ℝ) : ℂ)*x a)
        (((((m-(a : ℕ) : ℕ) : ℝ)*0^(m-(a : ℕ)-1)*
          radialSevenHigherBoundaryCoefficient m a : ℝ) : ℂ)*x a) 0 := by
      simpa only [Pi.pow_apply, id_eq, mul_one] using
        ((((hasDerivAt_id (0 : ℝ)).pow (m-(a : ℕ))).mul_const
          (radialSevenHigherBoundaryCoefficient m a)).ofReal_comp).mul_const (x a)
    have hs := HasDerivAt.fun_sum (fun a (_ha : a ∈ (Finset.univ : Finset (Fin 7))) => ht a)
    by_cases he : m = 7
    · subst m
      convert! hs using 1
      norm_num [Fin.sum_univ_succ, radialSevenHigherBoundaryCoefficient_seven_six]
      all_goals
        change 28*x 6 = (radialSevenHigherBoundaryCoefficient 7 (6 : Fin 7) : ℂ)*x 6
        rw [radialSevenHigherBoundaryCoefficient_seven_six]
        norm_num
    · have hz (a : Fin 7) : 0^(m-(a : ℕ)-1 : ℕ) = (0 : ℝ) := by
        apply zero_pow
        omega
      convert! hs using 1
      simp only [he, if_false, hz, mul_zero, zero_mul, Complex.ofReal_zero,
        Finset.sum_const_zero]

/-- The first-order finite-step cross, with its exact geometric coefficient. -/
def radialSevenBoundaryFirstCorrection (x : Fin 7 → ℂ) : ℝ :=
  112 * (-(nativeSourceOddBoundaryCoefficient 4)*(conj (x 1)*x 6).re +
    nativeSourceOddBoundaryCoefficient 5*(conj (x 3)*x 6).re -
    nativeSourceOddBoundaryCoefficient 6*(conj (x 5)*x 6).re)

/-- Differentiate the SAME complete signed tower; all summands remain. -/
theorem radialSevenRegularizedBoundaryEnergy_hasDerivAt_zero (x : Fin 7 → ℂ) :
    HasDerivAt (fun h : ℝ => radialSevenRegularizedBoundaryEnergy h x)
      (radialSevenBoundaryFirstCorrection x) 0 := by
  let b := fun m : ℕ => if m = 7 then (28 : ℂ)*x 6 else 0
  have hp (a d : ℕ) : HasDerivAt
      (fun h : ℝ => (conj (radialSevenRegularizedBoundary h x a)*
        radialSevenRegularizedBoundary h x d).re)
      (conj (b a)*radialSevenRegularizedBoundary 0 x d +
        conj (radialSevenRegularizedBoundary 0 x a)*b d).re 0 := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      ((radialSevenRegularizedBoundary_hasDerivAt_zero x a).star.mul
        (radialSevenRegularizedBoundary_hasDerivAt_zero x d))
  have hj (j : ℕ) : HasDerivAt
      (fun h : ℝ => (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
        (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (radialSevenRegularizedBoundary h x a)*
            radialSevenRegularizedBoundary h x (2*j-a)).re))
      ((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
        (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
          (conj (b a)*radialSevenRegularizedBoundary 0 x (2*j-a) +
            conj (radialSevenRegularizedBoundary 0 x a)*b (2*j-a)).re)) 0 := by
    simpa only [Finset.sum_apply] using (HasDerivAt.fun_sum (fun a (_ha : a ∈ Finset.range (2*j+1)) =>
      (hp a (2*j-a)).const_mul ((-1 : ℝ)^a))).const_mul
        ((-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j)
  have hs := (HasDerivAt.fun_sum (fun j (_hj : j ∈ Finset.range 7) => hj j)).const_mul 2
  have he : 2 * (∑ j ∈ Finset.range 7, (-1 : ℝ)^j * nativeSourceOddBoundaryCoefficient j *
      (∑ a ∈ Finset.range (2*j+1), (-1 : ℝ)^a *
        (conj (b a)*radialSevenRegularizedBoundary 0 x (2*j-a) +
          conj (radialSevenRegularizedBoundary 0 x a)*b (2*j-a)).re)) =
      radialSevenBoundaryFirstCorrection x := by
    simp_rw [radialSevenRegularizedBoundary_zero]
    norm_num [b, Finset.sum_range_succ, nativeSourceSevenBoundaryExtension,
      radialSevenBoundaryFirstCorrection, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
    rfl
  rw [he] at hs
  change HasDerivAt (fun h => radialSevenRegularizedBoundaryEnergy h x) _ 0 at hs
  exact hs

/-- This derivative is a loss of the finite-prefix face, not a diagonal energy. -/
theorem radialSevenBoundaryMarginLoss_hasDerivAt_zero (x : Fin 7 → ℂ) :
    HasDerivAt (fun h : ℝ => radialSevenBoundaryMarginLoss h x)
      (radialSevenBoundaryFirstCorrection x) 0 := by
  convert! (radialSevenRegularizedBoundaryEnergy_hasDerivAt_zero x).sub_const
    (nativeSourceSevenBoundaryEnergy x) using 1

/-- Two original boundary coordinates suffice to test the signed loss. -/
def radialSevenMarginLossDirection (s : ℝ) : Fin 7 → ℂ :=
  fun a => if a = 1 then (s : ℂ) else if a = 6 then 1 else 0

theorem radialSevenBoundaryFirstCorrection_direction (s : ℝ) :
    radialSevenBoundaryFirstCorrection (radialSevenMarginLossDirection s) =
      -112 * nativeSourceOddBoundaryCoefficient 4 * s := by
  simp [radialSevenBoundaryFirstCorrection, radialSevenMarginLossDirection]
  ring

/-- This coefficient sign is inherited from the already-certified raw
five-face source energy, not from canonical moments. -/
theorem nativeSourceOddBoundaryCoefficient_four_pos_from_face :
    0 < nativeSourceOddBoundaryCoefficient 4 := by
  have hp := nativeSourceFiveEvenBoundaryEnergy_pos_iff.mpr
    nativeSourceFiveEvenDiscriminant_pos (0 : ℂ) 0 1
      (Or.inr (Or.inr one_ne_zero))
  simpa [nativeSourceFiveEvenBoundaryEnergy] using hp

theorem radialSevenBoundaryFirstCorrection_loss_direction_neg :
    radialSevenBoundaryFirstCorrection (radialSevenMarginLossDirection 1) < 0 := by
  rw [radialSevenBoundaryFirstCorrection_direction]
  nlinarith [nativeSourceOddBoundaryCoefficient_four_pos_from_face]

theorem radialSevenBoundaryFirstCorrection_gain_direction_pos :
    0 < radialSevenBoundaryFirstCorrection (radialSevenMarginLossDirection (-1)) := by
  rw [radialSevenBoundaryFirstCorrection_direction]
  nlinarith [nativeSourceOddBoundaryCoefficient_four_pos_from_face]

/-- The analytic source remainder has zero first derivative in the storage
chart when its certified constant term vanishes. -/
theorem radialSevenRegularizedRemainderEnergy_hasDerivAt_zero
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) (hR0 : R 0 = 0) (x : Fin 7 → ℂ) :
    HasDerivAt (fun h : ℝ => radialSevenRegularizedRemainderEnergy R h x) 0 0 := by
  have hq0 : radialSevenRemainderQuadraticReadout R 0 x = 0 := by
    simp [radialSevenRemainderQuadraticReadout, hR0]
  have hq : Tendsto (fun h : ℝ => 4 * radialSevenRemainderQuadraticReadout R h x)
      (nhds 0) (nhds 0) := by
    have hi : ContinuousAt (fun h : ℝ => (h,x)) 0 := by fun_prop
    have hc := (radialSevenRemainderQuadraticReadout_continuousAt R hR x).comp_of_eq hi rfl
    simpa only [Function.comp_apply, hq0, mul_zero] using hc.tendsto.const_mul 4
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hq.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  simp only [slope, sub_zero, smul_eq_mul]
  change 4 * radialSevenRemainderQuadraticReadout R h x =
    h⁻¹ * (radialSevenRegularizedRemainderEnergy R h x -
      radialSevenRegularizedRemainderEnergy R 0 x)
  unfold radialSevenRegularizedRemainderEnergy radialSevenRemainderQuadraticReadout
  field_simp
  ring

/-- The FULL storage has the same signed first correction; the source
remainder does not repair or cancel it at first order. -/
theorem radialSevenRegularizedStorage_hasDerivAt_zero
    (R : ℂ → ℂ) (hR : ContinuousAt R 0) (hR0 : R 0 = 0) (x : Fin 7 → ℂ) :
    HasDerivAt (fun h : ℝ => radialSevenRegularizedStorage R h x)
      (radialSevenBoundaryFirstCorrection x) 0 := by
  convert! (radialSevenRegularizedBoundaryEnergy_hasDerivAt_zero x).fun_add
    (radialSevenRegularizedRemainderEnergy_hasDerivAt_zero R hR hR0 x) using 1
  simp only [add_zero]

/-- Exact full original storage after completed value/companion synthesis. -/
theorem storage_one_sevenSample_eventually_regularized_zero :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0 = 0 ∧ ∀ᶠ k : ℕ in atTop, ∀ x : Fin 7 → ℂ,
      (storage k (radialCompletedInputCoefficients k
        (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re =
          radialSevenRegularizedStorage R (radialFourSourceStep k) x := by
  obtain ⟨R, hRa, hR0, hR⟩ := radialSevenOddSourceTemplate_eventually_eq_slopes_zero
  refine ⟨R, hRa, hR0, ?_⟩
  filter_upwards [hR, canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 7]
    with k hk hreg
  intro x
  have hh := (radialFourSourceStep_pos k).ne'
  have hkh : ((k : ℝ)+1)*radialFourSourceStep k = 1 := by
    unfold radialFourSourceStep
    exact mul_inv_cancel₀ (by positivity)
  rw [storage_one_eq_complete_slope_pairing k 7 _
    (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)]
  simp_rw [hk]
  exact radialSevenOddSourceTemplate_energy k _ hh hkh R x


/-- Exact first signed correction of the ACTUAL completed seven-source storage. -/
theorem storage_one_sevenSample_first_correction_tendsto (x : Fin 7 → ℂ) :
    Tendsto (fun k : ℕ =>
      ((storage k (radialCompletedInputCoefficients k
        (radialSevenNormalizedBoundaryInput (radialFourSourceStep k) x)) 1).re -
          nativeSourceSevenBoundaryEnergy x) / radialFourSourceStep k)
      atTop (nhds (radialSevenBoundaryFirstCorrection x)) := by
  obtain ⟨R, hRa, hR0, hE⟩ := storage_one_sevenSample_eventually_regularized_zero
  have ht : Tendsto radialFourSourceStep atTop (nhdsWithin 0 {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨radialFourSourceStep_tendsto_zero, ?_⟩
    exact Filter.Eventually.of_forall (fun k => by simp [(radialFourSourceStep_pos k).ne'])
  have hd := (radialSevenRegularizedStorage_hasDerivAt_zero R hRa.continuousAt hR0 x).tendsto_slope.comp ht
  have hd' : Tendsto (fun k : ℕ =>
      (radialSevenRegularizedStorage R (radialFourSourceStep k) x -
        nativeSourceSevenBoundaryEnergy x) / radialFourSourceStep k)
      atTop (nhds (radialSevenBoundaryFirstCorrection x)) := by
    convert! hd using 1
    funext k
    rw [Function.comp_apply, slope_def_field, sub_zero, radialSevenRegularizedStorage_zero]
  apply hd'.congr'
  filter_upwards [hE] with k hk
  rw [hk]

/-- The original storage really decreases relative to its boundary face in
this direction; positivity survives with a smaller uniform margin. -/
theorem storage_one_sevenSample_eventually_below_boundary :
    ∀ᶠ k : ℕ in atTop,
      (storage k (radialCompletedInputCoefficients k
        (radialSevenNormalizedBoundaryInput (radialFourSourceStep k)
          (radialSevenMarginLossDirection 1))) 1).re <
            nativeSourceSevenBoundaryEnergy (radialSevenMarginLossDirection 1) := by
  have hl := (storage_one_sevenSample_first_correction_tendsto
    (radialSevenMarginLossDirection 1)).eventually_lt_const
      radialSevenBoundaryFirstCorrection_loss_direction_neg
  filter_upwards [hl] with k hk
  have hs := (div_lt_iff₀ (radialFourSourceStep_pos k)).mp hk
  simp only [zero_mul] at hs
  exact sub_neg.mp hs

/-- Opposite sign is present as well; the correction is not a nonnegative
norm-square that can simply be discarded. -/
theorem storage_one_sevenSample_eventually_above_boundary :
    ∀ᶠ k : ℕ in atTop,
      nativeSourceSevenBoundaryEnergy (radialSevenMarginLossDirection (-1)) <
        (storage k (radialCompletedInputCoefficients k
          (radialSevenNormalizedBoundaryInput (radialFourSourceStep k)
            (radialSevenMarginLossDirection (-1)))) 1).re := by
  have hl := (storage_one_sevenSample_first_correction_tendsto
    (radialSevenMarginLossDirection (-1))).eventually_const_lt
      radialSevenBoundaryFirstCorrection_gain_direction_pos
  filter_upwards [hl] with k hk
  have hs := (div_pos_iff_of_pos_right (radialFourSourceStep_pos k)).mp hk
  exact sub_pos.mp hs

end
end CarrySelfAdjointOperator

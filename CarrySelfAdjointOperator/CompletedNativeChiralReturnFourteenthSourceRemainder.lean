import CarrySelfAdjointOperator.CompletedNativeChiralReturnSevenBoundaryReconstruction
import Mathlib.Analysis.Analytic.Order

/-!
# Order-fourteen remainder of the actual completed transverse source

All Taylor coordinates through degree thirteen are retained, without a sign
or parity simplification. The analytic remainder is supplied by the original
completed logarithmic source. Complete synthesis precedes the mixed readout.
-/
namespace CarrySelfAdjointOperator
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology ChiralReturn
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The original source Taylor polynomial at the unchanged radial node
multiplier. No coefficient of a canonical moment sequence enters it. -/
def radialSevenSourceTaylorPrefix (h : ℂ) (i : ℕ) : ℂ :=
  ∑ m ∈ Finset.range 14,
    (((((i+1 : ℕ) : ℂ)*h)^m) / (m.factorial : ℂ)) *
      iteratedDeriv m (fun y : ℂ =>
        -Complex.I * completedNativeOperatorLogDerivative (Complex.I*y)) 0

/-- Source prefix AND its entire analytic remainder. -/
def radialSevenSourceTaylorTemplate (R : ℂ → ℂ) (h : ℂ) (i : ℕ) : ℂ :=
  radialSevenSourceTaylorPrefix h i + (((i+1 : ℕ) : ℂ)*h)^14 *
    R (((i+1 : ℕ) : ℂ)*h)

/-- One remainder from the actual analytic source works at all seven original
nodes and every sufficiently small radial step; no sign is assumed. -/
theorem radialSevenSourceTaylorTemplate_eventually_eq_slopes :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ i : Fin 7, radialCompletedSlope k i =
        radialSevenSourceTaylorTemplate R (canonicalGreenJetStep k) i := by
  have ha : AnalyticAt ℂ (fun y : ℂ =>
      -Complex.I * completedNativeOperatorLogDerivative (Complex.I*y)) 0 := by
    have hc : AnalyticAt ℂ (fun y : ℂ =>
        completedNativeOperatorLogDerivative (Complex.I*y)) 0 :=
      nativeSourceLogSlope_analyticAt.fun_comp_of_eq (by fun_prop) (by simp)
    exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => -Complex.I) 0).fun_mul hc
  obtain ⟨R, hRa, hR⟩ := ha.exists_eventuallyEq_sum_add_pow_mul 14
  refine ⟨R, hRa, ?_⟩
  have ht (i : Fin 7) : Tendsto
      (fun k : ℕ => (((i+1 : ℕ) : ℂ)*canonicalGreenJetStep k)) atTop (nhds 0) := by
    simpa only [mul_zero] using canonicalGreenJetStep_tendsto_zero.const_mul
      (((i+1 : ℕ) : ℂ))
  filter_upwards [Filter.eventually_all.mpr (fun i : Fin 7 => (ht i).eventually hR)] with k hk
  intro i
  calc
    radialCompletedSlope k i = -Complex.I * completedNativeOperatorLogDerivative
        (Complex.I*(((i+1 : ℕ) : ℂ)*canonicalGreenJetStep k)) := by
      unfold radialCompletedSlope canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep
      congr 1
      congr 1
      ring
    _ = radialSevenSourceTaylorTemplate R (canonicalGreenJetStep k) i := by
      simpa only [radialSevenSourceTaylorTemplate, radialSevenSourceTaylorPrefix, smul_eq_mul] using hk i

/-- Exact higher vector after subtracting only the source's own prefix.
The Cauchy carrier, completed slope and normalized input are unchanged. -/
def radialSevenSourceTaylorRemainderSynthesis (k : ℕ) (h : ℝ) (x : Fin 7 → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  radialIncidentSynthesis k 7 (fun i => radialSevenNormalizedBoundaryInput h x i *
    radialCompletedSlope k i) -
  radialIncidentSynthesis k 7 (fun i => radialSevenNormalizedBoundaryInput h x i *
    radialSevenSourceTaylorPrefix (h : ℂ) i)

/-- Every i/j cross of the FULL higher vector, in polynomial boundary
coordinates. The factor h is forced by h^14, two factors h^-6, and the h^-1
Cauchy metric; it is not a new weight or a chosen norm. -/
def radialSevenRegularizedRemainderEnergy (R : ℂ → ℂ) (h : ℝ) (x : Fin 7 → ℂ) : ℝ :=
  4*h * (∑ i : Fin 7, ∑ j : Fin 7,
    conj (radialSevenRegularizedInput h x i) * radialSevenRegularizedInput h x j *
      (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)) /
        (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)).re

/-- Complete prefix/remainder vector splitting, before scalar compression. -/
theorem radialSevenSourceTaylorTemplate_synthesis
    (k : ℕ) (h : ℝ) (R : ℂ → ℂ) (d : Fin 7 → ℂ) :
    radialIncidentSynthesis k 7 (fun i => d i * radialSevenSourceTaylorTemplate R (h : ℂ) i) =
      radialIncidentSynthesis k 7 (fun i => d i * radialSevenSourceTaylorPrefix (h : ℂ) i) +
      radialIncidentSynthesis k 7 (fun i => d i *
        (((h^14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) * R (((((i+1 : ℕ) : ℝ)*h : ℝ) : ℂ)))) := by
  rw [← map_add]
  congr 1
  funext i
  simp only [radialSevenSourceTaylorTemplate, Pi.add_apply]
  push_cast
  rw [mul_pow]
  ring

/-- Exact conversion of the fully synthesized remainder to the continuous
boundary-chart expression. Only the original radial scale relation is used. -/
theorem radialSevenSourceRemainder_energy
    (k : ℕ) (h : ℝ) (hh : h ≠ 0) (hkh : ((k : ℝ)+1)*h = 1)
    (R : ℂ → ℂ) (x : Fin 7 → ℂ) :
    4 * (inner ℂ (radialIncidentSynthesis k 7 (radialSevenNormalizedBoundaryInput h x))
      (radialIncidentSynthesis k 7 (fun i => radialSevenNormalizedBoundaryInput h x i *
        (((h^14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) * R (((((i+1 : ℕ) : ℝ)*h : ℝ) : ℂ)))))).re =
      radialSevenRegularizedRemainderEnergy R h x := by
  have hg := radialEulerPower_inner k 7 0 0 (radialSevenNormalizedBoundaryInput h x)
    (fun i => radialSevenNormalizedBoundaryInput h x i *
      (((h^14 : ℝ) : ℂ) * (((i+1 : ℕ) : ℂ)^14) * R (((((i+1 : ℕ) : ℝ)*h : ℝ) : ℂ))))
  simp only [radialEulerPowerSynthesis_zero, pow_zero, mul_one] at hg
  rw [hg]
  unfold radialSevenRegularizedRemainderEnergy
  have hs : (∑ i : Fin 7, ∑ j : Fin 7,
      conj (radialSevenNormalizedBoundaryInput h x i) *
        (radialSevenNormalizedBoundaryInput h x j *
          (((h^14 : ℝ) : ℂ) * (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)))) *
          ((((k : ℝ)+1 : ℝ) : ℂ) / (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ))) =
      (h : ℂ) * (∑ i : Fin 7, ∑ j : Fin 7,
        conj (radialSevenRegularizedInput h x i) * radialSevenRegularizedInput h x j *
          (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)) /
            (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [radialSevenRegularizedInput_eq h hh x i, radialSevenRegularizedInput_eq h hh x j]
    have hp : ((k : ℝ)+1)*h^14 = h^13 := by
      have ht := congrArg (fun t : ℝ => t*h^13) hkh
      convert ht using 1 <;> ring
    have hpC := congrArg Complex.ofReal hp
    push_cast at hpC ⊢
    simp only [map_mul, map_pow, Complex.conj_ofReal]
    have he := congrArg (fun t : ℂ =>
      conj (radialSevenNormalizedBoundaryInput h x i) * radialSevenNormalizedBoundaryInput h x j *
        (((j+1 : ℕ) : ℂ)^14) * R (((((j+1 : ℕ) : ℝ)*h : ℝ) : ℂ)) /
          (((i : ℕ)+(j : ℕ)+2 : ℕ) : ℂ) * t) hpC
    push_cast at he
    linear_combination he
  rw [hs, Complex.re_ofReal_mul]
  ring

end
end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeChiralReturnJordanEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Quantitative leakage of the original negative source channel

The trace uses the original source chart, before any scalar moment readout.
Its bound controls every coefficient vector and every crossing. Convergence
of this trace is a sufficient open target; no such all-order estimate is
assumed as a new axiom or claimed proved here. Relative channel dominance is
a weaker alternative, also kept as an explicit hypothesis.
-/
namespace CarrySelfAdjointOperator.ChiralReturn
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
noncomputable section
set_option autoImplicit false

/-- Total negative energy of the original chart's coordinate columns. -/
def nativeSourceNegativeLeakageTrace (n k : ℕ) : ℝ :=
  ∑ i : Fin (2*n), ‖nativeSourceJordanNegativeState n k (Pi.single i 1)‖^2

theorem nativeSourceNegativeLeakageTrace_nonneg (n k : ℕ) :
    0 ≤ nativeSourceNegativeLeakageTrace n k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- A finite Hilbert-space Cauchy-Schwarz estimate retains all mixed terms. -/
theorem finite_synthesis_norm_sq_le_energy_product
    {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x : Fin N → ℂ) (w : Fin N → H) :
    ‖∑ i, x i • w i‖^2 ≤ (∑ i, ‖x i‖^2) * ∑ i, ‖w i‖^2 := by
  have hnorm : ‖∑ i, x i • w i‖ ≤ ∑ i, ‖x i‖ * ‖w i‖ := by
    simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => x i • w i)
  have hnonneg : 0 ≤ ∑ i, ‖x i‖ * ‖w i‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact ((sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hnorm).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖x i‖) (fun i => ‖w i‖))

/-- Uniform in every ORIGINAL input x; the coefficient sum is explicit.
The physical Hilbert norm and source features are unchanged. -/
theorem nativeSourceJordanNegativeState_norm_sq_le_trace
    (n k : ℕ) (x : Fin (2*n) → ℂ) :
    ‖nativeSourceJordanNegativeState n k x‖^2 ≤
      (∑ i, ‖x i‖^2) * nativeSourceNegativeLeakageTrace n k := by
  rw [nativeSourceJordanNegativeState_basis]
  exact finite_synthesis_norm_sq_le_energy_product x _

/-- A proved trace envelope supplies the quantitative all-input estimate. -/
theorem nativeSourceJordanNegativeState_norm_sq_le_of_trace_le
    (n k : ℕ) (ε : ℝ) (htrace : nativeSourceNegativeLeakageTrace n k ≤ ε)
    (x : Fin (2*n) → ℂ) :
    ‖nativeSourceJordanNegativeState n k x‖^2 ≤ ε * (∑ i, ‖x i‖^2) := by
  calc
    _ ≤ (∑ i, ‖x i‖^2) * nativeSourceNegativeLeakageTrace n k :=
      nativeSourceJordanNegativeState_norm_sq_le_trace n k x
    _ ≤ (∑ i, ‖x i‖^2) * ε :=
      mul_le_mul_of_nonneg_left htrace (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

/-- Vanishing trace controls all source vectors, without positive-vector limits. -/
theorem nativeSourceJordanNegativeState_norm_tendsto_zero_of_trace
    (n : ℕ) (htrace : Tendsto (nativeSourceNegativeLeakageTrace n) atTop (nhds 0))
    (x : Fin (2*n) → ℂ) :
    Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖) atTop (nhds 0) := by
  have hbound : Tendsto (fun k => (∑ i, ‖x i‖^2) * nativeSourceNegativeLeakageTrace n k)
      atTop (nhds 0) := by simpa using htrace.const_mul (∑ i, ‖x i‖^2)
  have hs : Tendsto (fun k => ‖nativeSourceJordanNegativeState n k x‖^2)
      atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _)
      (fun k => nativeSourceJordanNegativeState_norm_sq_le_trace n k x) hbound
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

/-- At fixed finite order, the trace criterion is exactly columnwise no-leak.
The quantitative estimate above is what also controls all mixed inputs. -/
theorem nativeSourceNegativeLeakageTrace_tendsto_zero_iff_columns (n : ℕ) :
    Tendsto (nativeSourceNegativeLeakageTrace n) atTop (nhds 0) ↔
      ∀ i : Fin (2*n), Tendsto
        (fun k => ‖nativeSourceJordanNegativeState n k (Pi.single i 1)‖) atTop (nhds 0) := by
  constructor
  · intro ht i
    exact nativeSourceJordanNegativeState_norm_tendsto_zero_of_trace n ht _
  · intro hc
    have h := tendsto_finsetSum Finset.univ (fun i _ => (hc i).pow 2)
    change Tendsto (fun k => ∑ i : Fin (2*n),
      ‖nativeSourceJordanNegativeState n k (Pi.single i 1)‖^2) atTop (nhds 0)
    simpa only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using h

/-- The sufficient sign target needs no strong limit of the positive channel. -/
theorem nativeSourceBoundary_nonneg_of_leakageTrace_tendsto_zero
    (n : ℕ) (htrace : Tendsto (nativeSourceNegativeLeakageTrace n) atTop (nhds 0))
    (x : Fin (2*n) → ℂ) : 0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x :=
  nativeSourceBoundary_nonneg_of_no_negative_leak n x
    (nativeSourceJordanNegativeState_norm_tendsto_zero_of_trace n htrace x)

/-- Explicit scalar envelopes are sufficient; proving one is the source task. -/
theorem nativeSourceBoundary_nonneg_of_trace_envelope
    (n : ℕ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (hbound : ∀ k, nativeSourceNegativeLeakageTrace n k ≤ ε k)
    (x : Fin (2*n) → ℂ) : 0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
  apply nativeSourceBoundary_nonneg_of_leakageTrace_tendsto_zero n ?_ x
  exact squeeze_zero (nativeSourceNegativeLeakageTrace_nonneg n) hbound hε

/-- Source traces are sufficient at all finite N, including odd N by zero padding.
The family of trace limits is an OPEN premise, not an existence theorem. -/
theorem nativeSourceBoundary_nonneg_all_N_of_leakageTrace
    (htrace : ∀ n, Tendsto (nativeSourceNegativeLeakageTrace n) atTop (nhds 0))
    (N : ℕ) (x : Fin N → ℂ) : 0 ≤ nativeSourceFiniteBoundaryEnergy N x := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' N
  · exact nativeSourceBoundary_nonneg_of_leakageTrace_tendsto_zero n (htrace n) x
  · have h := nativeSourceBoundary_nonneg_of_leakageTrace_tendsto_zero (n+1) (htrace (n+1))
    have he : 2*(n+1) = (2*n+1)+1 := by omega
    rw [he] at h
    have hp := h (Fin.snoc x 0)
    rwa [nativeSourceFiniteBoundaryEnergy_snoc_zero] at hp

/-- The negative channel need not vanish if its energy is asymptotically
bounded by the positive one. The estimate still has to come from the source. -/
theorem nativeSourceBoundary_nonneg_of_asymptotic_channel_dominance
    (n : ℕ) (x : Fin (2*n) → ℂ) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hbound : ∀ᶠ k in atTop,
      ‖nativeSourceJordanNegativeState n k x‖^2 ≤
        ‖nativeSourceJordanPositiveState n k x‖^2 + ε k * (∑ i, ‖x i‖^2)) :
    0 ≤ nativeSourceFiniteBoundaryEnergy (2*n) x := by
  have he : Tendsto (fun k => 2 * (ε k * (∑ i, ‖x i‖^2))) atTop (nhds 0) := by
    simpa using (hε.mul_const (∑ i, ‖x i‖^2)).const_mul (2 : ℝ)
  have ht := (nativeSourceJordan_signed_energy_tendsto n x).add he
  have hh : Tendsto (fun k =>
      2 * (‖nativeSourceJordanPositiveState n k x‖^2 -
        ‖nativeSourceJordanNegativeState n k x‖^2) +
        2 * (ε k * (∑ i, ‖x i‖^2))) atTop (nhds (nativeSourceFiniteBoundaryEnergy (2*n) x)) := by
    simpa only [add_zero] using ht
  apply ge_of_tendsto hh
  filter_upwards [hbound] with k hk
  linarith

end
end CarrySelfAdjointOperator.ChiralReturn

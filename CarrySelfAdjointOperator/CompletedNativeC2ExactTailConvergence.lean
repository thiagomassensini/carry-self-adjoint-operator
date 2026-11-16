import CarrySelfAdjointOperator.CompletedNativeC2ExactTailTransport
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-!
# Operator-norm convergence of the exact C2 tail in the original carrier

For fixed Hankel order `n` and radial index `k`, the Cauchy carrier has only
finitely many nodes.  The proofs below use the original source matrix,
Hermite--Biehler denominators, and radial state vectors to turn the scalar
local-uniform value/derivative convergence into uniform bounds over every
input vector.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open CPFormal.Analytic.Cp
open CarrySelfAdjointOperator.ChiralReturn
open NativeCarrySpectralWeyl.Camera

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Coefficient of the exact value tail at one original radial Cauchy node,
excluding the input coordinate. -/
def nativeSourceC2ValueTailNodeCoefficient (n k M : ℕ)
    (i : Fin (2 * n)) : ℂ :=
  (c2CompletionDressing (canonicalCompletedC3RadialTiltPoint k i) *
    nativeC2ExactCenterTail M
      (operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i))) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)

/-- Coefficient of the exact companion tail at the same original node. -/
def nativeSourceC2CompanionTailNodeCoefficient (n k M : ℕ)
    (i : Fin (2 * n)) : ℂ :=
  (-(c2CompletionDressingDerivative
      (canonicalCompletedC3RadialTiltPoint k i) *
      nativeC2ExactCenterTail M
        (c2SpectralLine (canonicalCompletedC3RadialTiltPoint k i)) +
    c2CompletionDressing (canonicalCompletedC3RadialTiltPoint k i) *
      Complex.I * deriv (nativeC2ExactCenterTail M)
        (c2SpectralLine (canonicalCompletedC3RadialTiltPoint k i)))) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)

/-- Complete value-channel coefficient at an original radial node. -/
def nativeSourceC2CompleteValueNodeCoefficient (k : ℕ)
    (i : ℕ) : ℂ :=
  completedNativeOperatorCharacteristic
      (canonicalCompletedC3RadialTiltPoint k i) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)

/-- Complete companion-channel coefficient at an original radial node. -/
def nativeSourceC2CompleteCompanionNodeCoefficient (k : ℕ)
    (i : ℕ) : ℂ :=
  completedNativeOperatorBoundaryCompanion
      (canonicalCompletedC3RadialTiltPoint k i) /
    completedNativePositiveHermiteBiehlerCoordinate
      (canonicalCompletedC3RadialTiltPoint k i)

/-- Absolute row sum of the existing finite source-coordinate matrix. -/
def nativeSourceC2InputRowBound (n k : ℕ) (i : Fin (2 * n)) : ℝ :=
  ∑ a : Fin (2 * n), ‖nativeSourceChiralJetInputMatrix n k i a‖

/-- Finite coefficient bounds for the two exact tail operators. -/
def nativeSourceC2ValueTailSensitivity (n k M : ℕ) : ℝ :=
  ∑ i : Fin (2 * n),
    nativeSourceC2InputRowBound n k i *
      ‖nativeSourceC2ValueTailNodeCoefficient n k M i‖ *
      ‖completedNativeRadialChiralCauchyState k i‖

def nativeSourceC2CompanionTailSensitivity (n k M : ℕ) : ℝ :=
  ∑ i : Fin (2 * n),
    nativeSourceC2InputRowBound n k i *
      ‖nativeSourceC2CompanionTailNodeCoefficient n k M i‖ *
      ‖completedNativeRadialChiralCauchyState k i‖

/-- Finite operator bounds for the complete value and companion channels. -/
def nativeSourceC2CompleteValueSensitivity (n k : ℕ) : ℝ :=
  ∑ i : Fin (2 * n),
    nativeSourceC2InputRowBound n k i *
      ‖nativeSourceC2CompleteValueNodeCoefficient k i‖ *
      ‖completedNativeRadialChiralCauchyState k i‖

def nativeSourceC2CompleteCompanionSensitivity (n k : ℕ) : ℝ :=
  ∑ i : Fin (2 * n),
    nativeSourceC2InputRowBound n k i *
      ‖nativeSourceC2CompleteCompanionNodeCoefficient k i‖ *
      ‖completedNativeRadialChiralCauchyState k i‖

/-- Each output coordinate of the original source matrix is bounded by its
absolute row sum times the sup norm of the input vector. -/
theorem nativeSourceChiralJetInput_coordinate_norm_le
    (n k : ℕ) (x : Fin (2 * n) → ℂ) (i : Fin (2 * n)) :
    ‖nativeSourceChiralJetInput n k x i‖ ≤
      nativeSourceC2InputRowBound n k i * ‖x‖ := by
  change ‖∑ a : Fin (2 * n),
      nativeSourceChiralJetInputMatrix n k i a * x a‖ ≤ _
  calc
    ‖∑ a : Fin (2 * n),
        nativeSourceChiralJetInputMatrix n k i a * x a‖ ≤
        ∑ a : Fin (2 * n),
          ‖nativeSourceChiralJetInputMatrix n k i a * x a‖ := norm_sum_le _ _
    _ = ∑ a : Fin (2 * n),
        ‖nativeSourceChiralJetInputMatrix n k i a‖ * ‖x a‖ := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [norm_mul]
    _ ≤ ∑ a : Fin (2 * n),
        ‖nativeSourceChiralJetInputMatrix n k i a‖ * ‖x‖ := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x a)
            (norm_nonneg _)
    _ = nativeSourceC2InputRowBound n k i * ‖x‖ := by
          rw [nativeSourceC2InputRowBound, Finset.sum_mul]

/-- The exact value-tail synthesis is a finite sum in the same original
carrier, with the exact scalar node coefficient factored out. -/
theorem nativeSourceC2ValueTail_eq_nodeSynthesis
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2ValueTail n k M x =
      ∑ i : Fin (2 * n),
        (nativeSourceChiralJetInput n k x i *
          nativeSourceC2ValueTailNodeCoefficient n k M i) •
          completedNativeRadialChiralCauchyState k i := by
  rw [nativeSourceC2ValueTail_eq_exactCenterTailSynthesis n k M x hstrip]
  unfold nativeSourceC2ExactValueTailSynthesis c2CauchySynthesis
    nativeSourceC2SourceWeight nativeSourceC2ValueTailNodeCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- The exact companion-tail synthesis uses those same source coordinates,
weights, radial nodes, and Cauchy state vectors. -/
theorem nativeSourceC2CompanionTail_eq_nodeSynthesis
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2CompanionTail n k M x =
      ∑ i : Fin (2 * n),
        (nativeSourceChiralJetInput n k x i *
          nativeSourceC2CompanionTailNodeCoefficient n k M i) •
          completedNativeRadialChiralCauchyState k i := by
  rw [nativeSourceC2CompanionTail_eq_exactCenterTailSynthesis n k M x hstrip]
  unfold nativeSourceC2ExactCompanionTailSynthesis c2CauchySynthesis
    nativeSourceC2SourceWeight nativeSourceC2CompanionTailNodeCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- The complete value channel uses the same finite source matrix and
Hermite--Biehler denominator. -/
theorem sourceValue_one_eq_completeNodeSynthesis
    (n k : ℕ) (x : Fin (2 * n) → ℂ) :
    sourceValue k (nativeSourceChiralJetInput n k x) 1 =
      ∑ i : Fin (2 * n),
        (nativeSourceChiralJetInput n k x i *
          nativeSourceC2CompleteValueNodeCoefficient k i) •
          completedNativeRadialChiralCauchyState k i := by
  rw [sourceValue_one_eq_nativeSourceC2SourceSynthesis]
  unfold c2CauchyValueSynthesis c2CauchySynthesis
    nativeSourceC2SourceWeight nativeSourceC2CompleteValueNodeCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- The complete negative-derivative companion is in the same source
carrier and uses the same coefficient matrix. -/
theorem sourceCompanion_one_eq_completeNodeSynthesis
    (n k : ℕ) (x : Fin (2 * n) → ℂ) :
    sourceCompanion k (nativeSourceChiralJetInput n k x) 1 =
      ∑ i : Fin (2 * n),
        (nativeSourceChiralJetInput n k x i *
          nativeSourceC2CompleteCompanionNodeCoefficient k i) •
          completedNativeRadialChiralCauchyState k i := by
  rw [sourceCompanion_one_eq_nativeSourceC2CompanionSynthesis]
  unfold c2CauchyCompanionSynthesis c2CauchySynthesis
    nativeSourceC2SourceWeight nativeSourceC2CompleteCompanionNodeCoefficient
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- Generic finite-node operator bound.  Its constant is the sum of the
original source-row norms times the node coefficient and the original state
norm. -/
theorem nativeSourceC2_nodeSynthesis_norm_le
    (n k : ℕ) (x : Fin (2 * n) → ℂ) (c : Fin (2 * n) → ℂ) :
    ‖∑ i : Fin (2 * n),
        (nativeSourceChiralJetInput n k x i * c i) •
          completedNativeRadialChiralCauchyState k i‖ ≤
      (∑ i : Fin (2 * n),
        nativeSourceC2InputRowBound n k i * ‖c i‖ *
          ‖completedNativeRadialChiralCauchyState k i‖) * ‖x‖ := by
  calc
    ‖∑ i : Fin (2 * n),
        (nativeSourceChiralJetInput n k x i * c i) •
          completedNativeRadialChiralCauchyState k i‖ ≤
        ∑ i : Fin (2 * n),
          ‖(nativeSourceChiralJetInput n k x i * c i) •
            completedNativeRadialChiralCauchyState k i‖ := norm_sum_le _ _
    _ = ∑ i : Fin (2 * n),
        ‖nativeSourceChiralJetInput n k x i‖ * ‖c i‖ *
          ‖completedNativeRadialChiralCauchyState k i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [norm_smul, mul_assoc]
    _ ≤ ∑ i : Fin (2 * n),
        (nativeSourceC2InputRowBound n k i * ‖c i‖ *
          ‖completedNativeRadialChiralCauchyState k i‖) * ‖x‖ := by
          apply Finset.sum_le_sum
          intro i hi
          have hcoord := nativeSourceChiralJetInput_coordinate_norm_le n k x i
          calc
            ‖nativeSourceChiralJetInput n k x i‖ * ‖c i‖ *
                ‖completedNativeRadialChiralCauchyState k i‖ ≤
              (nativeSourceC2InputRowBound n k i * ‖x‖) * ‖c i‖ *
                ‖completedNativeRadialChiralCauchyState k i‖ := by
                  gcongr
            _ = (nativeSourceC2InputRowBound n k i * ‖c i‖ *
                ‖completedNativeRadialChiralCauchyState k i‖) * ‖x‖ := by ring
    _ = (∑ i : Fin (2 * n),
        nativeSourceC2InputRowBound n k i * ‖c i‖ *
          ‖completedNativeRadialChiralCauchyState k i‖) * ‖x‖ := by
          rw [Finset.sum_mul]

/-- The value tail converges to zero in operator norm on the original input
space, for each fixed admissible radial grid. -/
theorem nativeSourceC2ValueTail_norm_le_sensitivity
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    ‖nativeSourceC2ValueTail n k M x‖ ≤
      nativeSourceC2ValueTailSensitivity n k M * ‖x‖ := by
  rw [nativeSourceC2ValueTail_eq_nodeSynthesis n k M x hstrip]
  simpa [nativeSourceC2ValueTailSensitivity] using
    nativeSourceC2_nodeSynthesis_norm_le n k x
      (nativeSourceC2ValueTailNodeCoefficient n k M)

/-- The companion tail has the same operator-norm control, using the exact
negative derivative coefficients. -/
theorem nativeSourceC2CompanionTail_norm_le_sensitivity
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    ‖nativeSourceC2CompanionTail n k M x‖ ≤
      nativeSourceC2CompanionTailSensitivity n k M * ‖x‖ := by
  rw [nativeSourceC2CompanionTail_eq_nodeSynthesis n k M x hstrip]
  simpa [nativeSourceC2CompanionTailSensitivity] using
    nativeSourceC2_nodeSynthesis_norm_le n k x
      (nativeSourceC2CompanionTailNodeCoefficient n k M)

/-- Finite operator-norm bounds for the complete source value and
companion channels at a fixed radial index. -/
theorem sourceValue_one_norm_le_sensitivity
    (n k : ℕ) (x : Fin (2 * n) → ℂ) :
    ‖sourceValue k (nativeSourceChiralJetInput n k x) 1‖ ≤
      nativeSourceC2CompleteValueSensitivity n k * ‖x‖ := by
  rw [sourceValue_one_eq_completeNodeSynthesis]
  simpa [nativeSourceC2CompleteValueSensitivity,
    nativeSourceC2CompleteValueNodeCoefficient] using
    nativeSourceC2_nodeSynthesis_norm_le n k x
      (fun i : Fin (2 * n) => nativeSourceC2CompleteValueNodeCoefficient k i.val)

theorem sourceCompanion_one_norm_le_sensitivity
    (n k : ℕ) (x : Fin (2 * n) → ℂ) :
    ‖sourceCompanion k (nativeSourceChiralJetInput n k x) 1‖ ≤
      nativeSourceC2CompleteCompanionSensitivity n k * ‖x‖ := by
  rw [sourceCompanion_one_eq_completeNodeSynthesis]
  simpa [nativeSourceC2CompleteCompanionSensitivity,
    nativeSourceC2CompleteCompanionNodeCoefficient] using
    nativeSourceC2_nodeSynthesis_norm_le n k x
      (fun i : Fin (2 * n) => nativeSourceC2CompleteCompanionNodeCoefficient k i.val)

/-- A strip point is in the scalar domain of the exact C2 head--tail
identity. -/
private theorem genuineCriticalStrip_mem_nativeScalarDomain
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) : s ∈ nativeScalarDomain := by
  rcases hs with ⟨hlo, hhi⟩
  change -1 < s.re ∧ s.re < 1
  constructor <;> linarith

/-- The exact value-tail coefficient tends to zero at any fixed strip node. -/
theorem nativeSourceC2ValueTailNodeCoefficient_tendsto_zero
    (n k : ℕ) (i : Fin (2 * n))
    (hstrip : operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ => nativeSourceC2ValueTailNodeCoefficient n k M i)
      atTop (nhds 0) := by
  let z := canonicalCompletedC3RadialTiltPoint k i
  have hs := genuineCriticalStrip_mem_nativeScalarDomain hstrip
  have htail := nativeC2ExactCenterTail_tendsto_zero
    (s := operatorHeightParameter z) hs
  have hL : Tendsto (fun M : ℕ => c2CompletionDressing z *
      nativeC2ExactCenterTail M (operatorHeightParameter z))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  have hInv : Tendsto (fun _ : ℕ =>
      (completedNativePositiveHermiteBiehlerCoordinate z)⁻¹)
      atTop (nhds
        ((completedNativePositiveHermiteBiehlerCoordinate z)⁻¹)) :=
    tendsto_const_nhds
  have h := hL.mul hInv
  simpa [nativeSourceC2ValueTailNodeCoefficient, z, div_eq_mul_inv] using h

/-- The exact derivative-tail coefficient also tends to zero. This combines
local-uniform convergence of both the C2 characteristic and its derivative;
the product-rule factors remain the original `L`, `L'`, and `i`. -/
theorem nativeSourceC2CompanionTailNodeCoefficient_tendsto_zero
    (n k : ℕ) (i : Fin (2 * n))
    (hstrip : operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ => nativeSourceC2CompanionTailNodeCoefficient n k M i)
      atTop (nhds 0) := by
  let z := canonicalCompletedC3RadialTiltPoint k i
  have hs := genuineCriticalStrip_mem_nativeScalarDomain hstrip
  have hsLine : c2SpectralLine z ∈ nativeScalarDomain := by
    simpa [c2SpectralLine_eq_operatorHeightParameter] using hs
  have htail := nativeC2ExactCenterTail_tendsto_zero
    (s := c2SpectralLine z) hsLine
  have hderiv := deriv_nativeC2ExactCenterTail_tendsto_zero
    (s := c2SpectralLine z) hsLine
  have hfirst : Tendsto (fun M : ℕ =>
      c2CompletionDressingDerivative z *
        nativeC2ExactCenterTail M (c2SpectralLine z))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail)
  have hsecond : Tendsto (fun M : ℕ =>
      (c2CompletionDressing z * Complex.I) *
        deriv (nativeC2ExactCenterTail M) (c2SpectralLine z))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => c2CompletionDressing z * Complex.I)
        atTop (nhds (c2CompletionDressing z * Complex.I)) := tendsto_const_nhds
    simpa [mul_assoc] using hconst.mul hderiv
  have hsum : Tendsto (fun M : ℕ =>
      c2CompletionDressingDerivative z *
          nativeC2ExactCenterTail M (c2SpectralLine z) +
        (c2CompletionDressing z * Complex.I) *
          deriv (nativeC2ExactCenterTail M) (c2SpectralLine z))
      atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hneg : Tendsto (fun M : ℕ =>
      -(c2CompletionDressingDerivative z *
          nativeC2ExactCenterTail M (c2SpectralLine z) +
        (c2CompletionDressing z * Complex.I) *
          deriv (nativeC2ExactCenterTail M) (c2SpectralLine z)))
      atTop (nhds 0) := by
    simpa using hsum.neg
  have hInv : Tendsto (fun _ : ℕ =>
      (completedNativePositiveHermiteBiehlerCoordinate z)⁻¹)
      atTop (nhds
        ((completedNativePositiveHermiteBiehlerCoordinate z)⁻¹)) :=
    tendsto_const_nhds
  have h := hneg.mul hInv
  simpa [nativeSourceC2CompanionTailNodeCoefficient, z, div_eq_mul_inv,
    mul_assoc] using h

/-- Fixed-node finite sums turn scalar tail convergence into convergence of
both finite operator-norm sensitivities. -/
theorem nativeSourceC2ValueTailSensitivity_tendsto_zero
    (n k : ℕ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ => nativeSourceC2ValueTailSensitivity n k M)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun M : ℕ => ∑ i : Fin (2 * n),
      nativeSourceC2InputRowBound n k i *
        ‖nativeSourceC2ValueTailNodeCoefficient n k M i‖ *
        ‖completedNativeRadialChiralCauchyState k i‖)
      atTop (nhds (∑ _i : Fin (2 * n), (0 : ℝ))) := by
    refine tendsto_finsetSum (Finset.univ : Finset (Fin (2 * n))) ?_
    intro i hi
    have hc := nativeSourceC2ValueTailNodeCoefficient_tendsto_zero n k i
      (hstrip i)
    have hn : Tendsto
        (fun M : ℕ => ‖nativeSourceC2ValueTailNodeCoefficient n k M i‖)
        atTop (nhds 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (continuous_norm.tendsto (0 : ℂ)).comp hc
    have hfirst : Tendsto (fun M : ℕ =>
        nativeSourceC2InputRowBound n k i *
          ‖nativeSourceC2ValueTailNodeCoefficient n k M i‖)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hn
    have hstate : Tendsto
        (fun _ : ℕ => ‖completedNativeRadialChiralCauchyState k i‖)
        atTop (nhds ‖completedNativeRadialChiralCauchyState k i‖) :=
      tendsto_const_nhds
    have hterm := hfirst.mul hstate
    simpa using hterm
  simpa [nativeSourceC2ValueTailSensitivity] using hsum

theorem nativeSourceC2CompanionTailSensitivity_tendsto_zero
    (n k : ℕ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ => nativeSourceC2CompanionTailSensitivity n k M)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun M : ℕ => ∑ i : Fin (2 * n),
      nativeSourceC2InputRowBound n k i *
        ‖nativeSourceC2CompanionTailNodeCoefficient n k M i‖ *
        ‖completedNativeRadialChiralCauchyState k i‖)
      atTop (nhds (∑ _i : Fin (2 * n), (0 : ℝ))) := by
    refine tendsto_finsetSum (Finset.univ : Finset (Fin (2 * n))) ?_
    intro i hi
    have hc := nativeSourceC2CompanionTailNodeCoefficient_tendsto_zero n k i
      (hstrip i)
    have hn : Tendsto
        (fun M : ℕ => ‖nativeSourceC2CompanionTailNodeCoefficient n k M i‖)
        atTop (nhds 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (continuous_norm.tendsto (0 : ℂ)).comp hc
    have hfirst : Tendsto (fun M : ℕ =>
        nativeSourceC2InputRowBound n k i *
          ‖nativeSourceC2CompanionTailNodeCoefficient n k M i‖)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hn
    have hstate : Tendsto
        (fun _ : ℕ => ‖completedNativeRadialChiralCauchyState k i‖)
        atTop (nhds ‖completedNativeRadialChiralCauchyState k i‖) :=
      tendsto_const_nhds
    have hterm := hfirst.mul hstate
    simpa using hterm
  simpa [nativeSourceC2CompanionTailSensitivity] using hsum

/-- Uniform convergence over the closed unit ball of the finite Hankel input
space, stated directly as an epsilon formulation of operator-norm decay. -/
theorem nativeSourceC2ValueTail_uniform_on_unit_ball
    (n k : ℕ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    ∀ ε > 0, ∀ᶠ M : ℕ in atTop, ∀ x : Fin (2 * n) → ℂ,
      ‖x‖ ≤ 1 → ‖nativeSourceC2ValueTail n k M x‖ < ε := by
  intro ε hε
  have hsmall :=
    (nativeSourceC2ValueTailSensitivity_tendsto_zero n k hstrip).eventually
      (Iio_mem_nhds hε)
  filter_upwards [hsmall] with M hM
  intro x hx
  have hsens : 0 ≤ nativeSourceC2ValueTailSensitivity n k M := by
    unfold nativeSourceC2ValueTailSensitivity
    apply Finset.sum_nonneg
    intro i hi
    have hr : 0 ≤ nativeSourceC2InputRowBound n k i := by
      unfold nativeSourceC2InputRowBound
      exact Finset.sum_nonneg fun a _ => norm_nonneg _
    exact mul_nonneg (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _)
  calc
    ‖nativeSourceC2ValueTail n k M x‖ ≤
      nativeSourceC2ValueTailSensitivity n k M * ‖x‖ :=
      nativeSourceC2ValueTail_norm_le_sensitivity n k M x hstrip
    _ ≤ nativeSourceC2ValueTailSensitivity n k M :=
      (mul_le_mul_of_nonneg_left hx hsens).trans_eq (by simp)
    _ < ε := hM

theorem nativeSourceC2CompanionTail_uniform_on_unit_ball
    (n k : ℕ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    ∀ ε > 0, ∀ᶠ M : ℕ in atTop, ∀ x : Fin (2 * n) → ℂ,
      ‖x‖ ≤ 1 → ‖nativeSourceC2CompanionTail n k M x‖ < ε := by
  intro ε hε
  have hsmall :=
    (nativeSourceC2CompanionTailSensitivity_tendsto_zero n k hstrip).eventually
      (Iio_mem_nhds hε)
  filter_upwards [hsmall] with M hM
  intro x hx
  have hsens : 0 ≤ nativeSourceC2CompanionTailSensitivity n k M := by
    unfold nativeSourceC2CompanionTailSensitivity
    apply Finset.sum_nonneg
    intro i hi
    have hr : 0 ≤ nativeSourceC2InputRowBound n k i := by
      unfold nativeSourceC2InputRowBound
      exact Finset.sum_nonneg fun a _ => norm_nonneg _
    exact mul_nonneg (mul_nonneg hr (norm_nonneg _)) (norm_nonneg _)
  calc
    ‖nativeSourceC2CompanionTail n k M x‖ ≤
      nativeSourceC2CompanionTailSensitivity n k M * ‖x‖ :=
      nativeSourceC2CompanionTail_norm_le_sensitivity n k M x hstrip
    _ ≤ nativeSourceC2CompanionTailSensitivity n k M :=
      (mul_le_mul_of_nonneg_left hx hsens).trans_eq (by simp)
    _ < ε := hM

/-- E2 coefficient obtained solely from the two exact-tail operator norms
and the complete value/companion operator bounds. -/
def nativeSourceC2TailErrorSensitivityBound (n k M : ℕ) : ℝ :=
  2 * (nativeSourceC2ValueTailSensitivity n k M *
        (nativeSourceC2CompleteCompanionSensitivity n k +
          nativeSourceC2CompanionTailSensitivity n k M) +
      (nativeSourceC2CompleteValueSensitivity n k +
        nativeSourceC2ValueTailSensitivity n k M) *
        nativeSourceC2CompanionTailSensitivity n k M +
      nativeSourceC2ValueTailSensitivity n k M *
        nativeSourceC2CompanionTailSensitivity n k M)

theorem nativeSourceC2InputRowBound_nonneg
    (n k : ℕ) (i : Fin (2 * n)) : 0 ≤ nativeSourceC2InputRowBound n k i := by
  unfold nativeSourceC2InputRowBound
  exact Finset.sum_nonneg fun a _ => norm_nonneg _

theorem nativeSourceC2ValueTailSensitivity_nonneg
    (n k M : ℕ) : 0 ≤ nativeSourceC2ValueTailSensitivity n k M := by
  unfold nativeSourceC2ValueTailSensitivity
  apply Finset.sum_nonneg
  intro i hi
  positivity [nativeSourceC2InputRowBound_nonneg n k i]

theorem nativeSourceC2CompanionTailSensitivity_nonneg
    (n k M : ℕ) : 0 ≤ nativeSourceC2CompanionTailSensitivity n k M := by
  unfold nativeSourceC2CompanionTailSensitivity
  apply Finset.sum_nonneg
  intro i hi
  positivity [nativeSourceC2InputRowBound_nonneg n k i]

theorem nativeSourceC2CompleteValueSensitivity_nonneg (n k : ℕ) :
    0 ≤ nativeSourceC2CompleteValueSensitivity n k := by
  unfold nativeSourceC2CompleteValueSensitivity
  apply Finset.sum_nonneg
  intro i hi
  positivity [nativeSourceC2InputRowBound_nonneg n k i]

theorem nativeSourceC2CompleteCompanionSensitivity_nonneg (n k : ℕ) :
    0 ≤ nativeSourceC2CompleteCompanionSensitivity n k := by
  unfold nativeSourceC2CompleteCompanionSensitivity
  apply Finset.sum_nonneg
  intro i hi
  positivity [nativeSourceC2InputRowBound_nonneg n k i]

private theorem nativeSourceC2ApproxValue_eq_complete_sub_tail
    (n k M : ℕ) (x : Fin (2 * n) → ℂ) :
    nativeSourceC2ApproxValue n k M x =
      sourceValue k (nativeSourceChiralJetInput n k x) 1 -
        nativeSourceC2ValueTail n k M x := by
  rw [nativeSourceC2ValueTail]
  abel

private theorem nativeSourceC2ApproxCompanion_eq_complete_sub_tail
    (n k M : ℕ) (x : Fin (2 * n) → ℂ) :
    nativeSourceC2ApproxCompanion n k M x =
      sourceCompanion k (nativeSourceChiralJetInput n k x) 1 -
        nativeSourceC2CompanionTail n k M x := by
  rw [nativeSourceC2CompanionTail]
  abel

theorem nativeSourceC2ApproxValue_norm_le_sensitivity
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    ‖nativeSourceC2ApproxValue n k M x‖ ≤
      (nativeSourceC2CompleteValueSensitivity n k +
        nativeSourceC2ValueTailSensitivity n k M) * ‖x‖ := by
  rw [nativeSourceC2ApproxValue_eq_complete_sub_tail]
  calc
    ‖sourceValue k (nativeSourceChiralJetInput n k x) 1 -
        nativeSourceC2ValueTail n k M x‖ ≤
      ‖sourceValue k (nativeSourceChiralJetInput n k x) 1‖ +
        ‖nativeSourceC2ValueTail n k M x‖ := norm_sub_le _ _
    _ ≤ nativeSourceC2CompleteValueSensitivity n k * ‖x‖ +
        nativeSourceC2ValueTailSensitivity n k M * ‖x‖ :=
      add_le_add (sourceValue_one_norm_le_sensitivity n k x)
        (nativeSourceC2ValueTail_norm_le_sensitivity n k M x hstrip)
    _ = (nativeSourceC2CompleteValueSensitivity n k +
        nativeSourceC2ValueTailSensitivity n k M) * ‖x‖ := by ring

theorem nativeSourceC2ApproxCompanion_norm_le_sensitivity
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    ‖nativeSourceC2ApproxCompanion n k M x‖ ≤
      (nativeSourceC2CompleteCompanionSensitivity n k +
        nativeSourceC2CompanionTailSensitivity n k M) * ‖x‖ := by
  rw [nativeSourceC2ApproxCompanion_eq_complete_sub_tail]
  calc
    ‖sourceCompanion k (nativeSourceChiralJetInput n k x) 1 -
        nativeSourceC2CompanionTail n k M x‖ ≤
      ‖sourceCompanion k (nativeSourceChiralJetInput n k x) 1‖ +
        ‖nativeSourceC2CompanionTail n k M x‖ := norm_sub_le _ _
    _ ≤ nativeSourceC2CompleteCompanionSensitivity n k * ‖x‖ +
        nativeSourceC2CompanionTailSensitivity n k M * ‖x‖ :=
      add_le_add (sourceCompanion_one_norm_le_sensitivity n k x)
        (nativeSourceC2CompanionTail_norm_le_sensitivity n k M x hstrip)
    _ = (nativeSourceC2CompleteCompanionSensitivity n k +
        nativeSourceC2CompanionTailSensitivity n k M) * ‖x‖ := by ring

/-- The explicit E2 tail error is bounded by the finite sensitivity
coefficient times `‖x‖²`, uniformly for all source vectors. -/
theorem nativeSourceC2TailError_le_sensitivity_bound
    (n k M : ℕ) (x : Fin (2 * n) → ℂ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    nativeSourceC2TailError n k M x ≤
      nativeSourceC2TailErrorSensitivityBound n k M * ‖x‖ ^ 2 := by
  let r := ‖x‖
  have hU := nativeSourceC2ValueTail_norm_le_sensitivity n k M x hstrip
  have hC := nativeSourceC2CompanionTail_norm_le_sensitivity n k M x hstrip
  have hUA := nativeSourceC2ApproxValue_norm_le_sensitivity n k M x hstrip
  have hCA := nativeSourceC2ApproxCompanion_norm_le_sensitivity n k M x hstrip
  have heU := nativeSourceC2ValueTailSensitivity_nonneg n k M
  have heC := nativeSourceC2CompanionTailSensitivity_nonneg n k M
  have hKU := nativeSourceC2CompleteValueSensitivity_nonneg n k
  have hKC := nativeSourceC2CompleteCompanionSensitivity_nonneg n k
  have hterm1 :
      ‖nativeSourceC2ValueTail n k M x‖ *
          ‖nativeSourceC2ApproxCompanion n k M x‖ ≤
        (nativeSourceC2ValueTailSensitivity n k M * r) *
          ((nativeSourceC2CompleteCompanionSensitivity n k +
            nativeSourceC2CompanionTailSensitivity n k M) * r) :=
    mul_le_mul hU hCA (norm_nonneg _) (by positivity)
  have hterm2 :
      ‖nativeSourceC2ApproxValue n k M x‖ *
          ‖nativeSourceC2CompanionTail n k M x‖ ≤
        ((nativeSourceC2CompleteValueSensitivity n k +
          nativeSourceC2ValueTailSensitivity n k M) * r) *
          (nativeSourceC2CompanionTailSensitivity n k M * r) :=
    mul_le_mul hUA hC (norm_nonneg _) (by positivity)
  have hterm3 :
      ‖nativeSourceC2ValueTail n k M x‖ *
          ‖nativeSourceC2CompanionTail n k M x‖ ≤
        (nativeSourceC2ValueTailSensitivity n k M * r) *
          (nativeSourceC2CompanionTailSensitivity n k M * r) :=
    mul_le_mul hU hC (norm_nonneg _) (by positivity)
  unfold nativeSourceC2TailError nativeSourceC2TailErrorSensitivityBound
  calc
    2 * (‖nativeSourceC2ValueTail n k M x‖ *
          ‖nativeSourceC2ApproxCompanion n k M x‖ +
        ‖nativeSourceC2ApproxValue n k M x‖ *
          ‖nativeSourceC2CompanionTail n k M x‖ +
        ‖nativeSourceC2ValueTail n k M x‖ *
          ‖nativeSourceC2CompanionTail n k M x‖) ≤
      2 * ((nativeSourceC2ValueTailSensitivity n k M * r) *
          ((nativeSourceC2CompleteCompanionSensitivity n k +
            nativeSourceC2CompanionTailSensitivity n k M) * r) +
        ((nativeSourceC2CompleteValueSensitivity n k +
          nativeSourceC2ValueTailSensitivity n k M) * r) *
          (nativeSourceC2CompanionTailSensitivity n k M * r) +
        (nativeSourceC2ValueTailSensitivity n k M * r) *
          (nativeSourceC2CompanionTailSensitivity n k M * r)) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add (add_le_add hterm1 hterm2) hterm3) (by norm_num)
    _ = 2 * (nativeSourceC2ValueTailSensitivity n k M *
          (nativeSourceC2CompleteCompanionSensitivity n k +
            nativeSourceC2CompanionTailSensitivity n k M) +
        (nativeSourceC2CompleteValueSensitivity n k +
          nativeSourceC2ValueTailSensitivity n k M) *
          nativeSourceC2CompanionTailSensitivity n k M +
        nativeSourceC2ValueTailSensitivity n k M *
          nativeSourceC2CompanionTailSensitivity n k M) * r ^ 2 := by
            dsimp [r]
            ring

/-- For fixed order and radial index in the strip, the uniform E2 error
coefficient tends to zero as the original C2 cell cutoff tends to infinity. -/
theorem nativeSourceC2TailErrorSensitivityBound_tendsto_zero
    (n k : ℕ)
    (hstrip : ∀ i : Fin (2 * n), operatorHeightParameter
      (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ => nativeSourceC2TailErrorSensitivityBound n k M)
      atTop (nhds 0) := by
  have hU := nativeSourceC2ValueTailSensitivity_tendsto_zero n k hstrip
  have hC := nativeSourceC2CompanionTailSensitivity_tendsto_zero n k hstrip
  have hKC : Tendsto (fun M : ℕ =>
      nativeSourceC2CompleteCompanionSensitivity n k +
        nativeSourceC2CompanionTailSensitivity n k M)
      atTop (nhds (nativeSourceC2CompleteCompanionSensitivity n k)) := by
    simpa using tendsto_const_nhds.add hC
  have hKU : Tendsto (fun M : ℕ =>
      nativeSourceC2CompleteValueSensitivity n k +
        nativeSourceC2ValueTailSensitivity n k M)
      atTop (nhds (nativeSourceC2CompleteValueSensitivity n k)) := by
    simpa using tendsto_const_nhds.add hU
  have h1 : Tendsto (fun M : ℕ =>
      nativeSourceC2ValueTailSensitivity n k M *
        (nativeSourceC2CompleteCompanionSensitivity n k +
          nativeSourceC2CompanionTailSensitivity n k M))
      atTop (nhds 0) := by
    simpa using hU.mul hKC
  have h2 : Tendsto (fun M : ℕ =>
      (nativeSourceC2CompleteValueSensitivity n k +
        nativeSourceC2ValueTailSensitivity n k M) *
        nativeSourceC2CompanionTailSensitivity n k M)
      atTop (nhds 0) := by
    simpa using hKU.mul hC
  have h3 : Tendsto (fun M : ℕ =>
      nativeSourceC2ValueTailSensitivity n k M *
        nativeSourceC2CompanionTailSensitivity n k M)
      atTop (nhds 0) := by
    simpa using hU.mul hC
  have hsum : Tendsto (fun M : ℕ =>
      nativeSourceC2ValueTailSensitivity n k M *
          (nativeSourceC2CompleteCompanionSensitivity n k +
            nativeSourceC2CompanionTailSensitivity n k M) +
        (nativeSourceC2CompleteValueSensitivity n k +
          nativeSourceC2ValueTailSensitivity n k M) *
          nativeSourceC2CompanionTailSensitivity n k M +
        nativeSourceC2ValueTailSensitivity n k M *
          nativeSourceC2CompanionTailSensitivity n k M)
      atTop (nhds 0) := by
    simpa using (h1.add h2).add h3
  have htwoConst : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have htwo := htwoConst.mul hsum
  simpa [nativeSourceC2TailErrorSensitivityBound] using htwo

/-- Eventual regularity for every fixed finite radial Cauchy grid. Here `n`
is fixed and the finitely many radial nodes all eventually enter the open
strip where the exact C2 identity and derivative transport apply. -/
def nativeSourceC2NodesInStrip (n k : ℕ) : Prop :=
  ∀ i : Fin (2 * n), operatorHeightParameter
    (canonicalCompletedC3RadialTiltPoint k i) ∈ genuineCriticalStrip

theorem nativeSourceC2NodesEventuallyInStrip (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, nativeSourceC2NodesInStrip n k := by
  change ∀ᶠ k : ℕ in atTop, ∀ i : Fin (2 * n),
    operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈
      genuineCriticalStrip
  rw [Filter.eventually_all]
  intro i
  filter_upwards [canonicalCompletedC3RadialTiltPoint_eventually_admissible
    (i : ℕ)] with k hregular
  simpa [completedNativeHeightDomain] using hregular.1

/-- An explicit positive budget, independent of the Hankel order. -/
def nativeSourceC2TailBudget (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 1)

theorem nativeSourceC2TailBudget_tendsto_zero :
    Tendsto nativeSourceC2TailBudget atTop (nhds 0) := by
  change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0)
  simpa [div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- For every regular fixed radial grid, a sufficiently large exact C2
cutoff achieves the prescribed budget. -/
theorem exists_nativeSourceC2TailCutoff_for_budget
    (n k : ℕ) (hstrip : nativeSourceC2NodesInStrip n k) :
    ∃ M : ℕ,
      nativeSourceC2TailErrorSensitivityBound n k M <
        nativeSourceC2TailBudget k := by
  have hsmall :=
    (nativeSourceC2TailErrorSensitivityBound_tendsto_zero n k hstrip).eventually
      (Iio_mem_nhds (by
        change 0 < 1 / ((k : ℝ) + 1)
        positivity))
  rcases hsmall.exists with ⟨M, hM⟩
  exact ⟨M, by simpa [nativeSourceC2TailBudget] using hM⟩

/-- The diagonal cutoff is selected independently for each `(n,k)` and only
depends on that fixed radial grid's finite error sensitivity. -/
noncomputable def nativeSourceC2TailCutoff (n k : ℕ) : ℕ :=
  by
    classical
    exact if hstrip : nativeSourceC2NodesInStrip n k then
      Classical.choose (exists_nativeSourceC2TailCutoff_for_budget n k hstrip)
    else 0

theorem nativeSourceC2TailCutoff_meets_budget
    (n k : ℕ) (hstrip : nativeSourceC2NodesInStrip n k) :
    nativeSourceC2TailErrorSensitivityBound n k
        (nativeSourceC2TailCutoff n k) < nativeSourceC2TailBudget k := by
  classical
  unfold nativeSourceC2TailCutoff
  rw [dif_pos hstrip]
  exact Classical.choose_spec
    (exists_nativeSourceC2TailCutoff_for_budget n k hstrip)

/-- The second half of E4 now follows from the original C2 source and its
existing local-uniform value/derivative convergence. It is uniform in every
input vector and uses the same selected cutoff at each radial index. -/
theorem nativeSourceC2TailError_eventually_bounded_by_budget (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2 * n) → ℂ,
      nativeSourceC2TailError n k (nativeSourceC2TailCutoff n k) x ≤
        nativeSourceC2TailBudget k * ‖x‖ ^ 2 := by
  filter_upwards [nativeSourceC2NodesEventuallyInStrip n] with k hstrip
  have hcut := nativeSourceC2TailCutoff_meets_budget n k hstrip
  intro x
  calc
    nativeSourceC2TailError n k (nativeSourceC2TailCutoff n k) x ≤
      nativeSourceC2TailErrorSensitivityBound n k
          (nativeSourceC2TailCutoff n k) * ‖x‖ ^ 2 :=
      nativeSourceC2TailError_le_sensitivity_bound n k
        (nativeSourceC2TailCutoff n k) x hstrip
    _ ≤ nativeSourceC2TailBudget k * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcut.le (sq_nonneg ‖x‖)

/-- The only remaining E4 input is the central-plus-legs sign estimate at
this exact diagonal cutoff. The tail estimate is supplied by the preceding
unconditional theorem, so no cutoff compatibility is silently assumed. -/
def HasNativeSourceC2ChosenCutoffCentralLegSign : Prop :=
  ∀ n : ℕ, ∃ a : ℕ → ℝ,
    Tendsto a atTop (nhds 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2 * n) → ℂ,
        -a k * ‖x‖ ^ 2 ≤
          nativeSourceC2CentralLegReadout n k
            (nativeSourceC2TailCutoff n k) x

/-- Combining only the still-open central/legs sign premise at the chosen
cutoff with the proved exact-tail budget yields the current E4 interface. -/
theorem nativeSourceC2ChosenCutoffSign_implies_legTailBounds
    (hSign : HasNativeSourceC2ChosenCutoffCentralLegSign) :
    HasNativeSourceC2LegTailBounds := by
  intro n
  rcases hSign n with ⟨a, ha, hsign⟩
  refine ⟨nativeSourceC2TailCutoff n, a,
    nativeSourceC2TailBudget, ha,
    nativeSourceC2TailBudget_tendsto_zero, ?_⟩
  filter_upwards [hsign,
    nativeSourceC2TailError_eventually_bounded_by_budget n] with k hsign htail
  intro x
  exact ⟨hsign x, htail x⟩

end
end CarrySelfAdjointOperator

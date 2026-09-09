import CarrySelfAdjointOperator.C2LiteralCameraFiberBracketCrosswalk
import CarrySelfAdjointOperator.CompletedNativeTfvdAllOrderTaylorCompletion
import CarrySelfAdjointOperator.CompletedNativeTfvdRawAllOrderJetBridge
import CarrySelfAdjointOperator.NewtonStirlingTransport

open scoped BigOperators

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera.FiniteBridge
open CarrySelfAdjointOperator.ProjectiveDepth

noncomputable section

/-- Evaluation of a formal camera stencil in an arbitrary complex observable.
This is the minimal linear extension of the existing atom/stencil API. -/
def evalFormalStencil (value : ℕ → ℂ) : FormalStencil →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ value

@[simp] theorem evalFormalStencil_atom (value : ℕ → ℂ) (n : ℕ) :
    evalFormalStencil value (atom n) = value n := by
  simp [evalFormalStencil, atom]

def c2FiberAllOrderBracket (order m k : ℕ) : ℂ :=
  realLogPowerDirichletPower order (1 / 2 : ℂ)
      (((2 ^ k * m - 1 : ℕ) : ℝ)) -
    2 * realLogPowerDirichletPower order (1 / 2 : ℂ)
      (((2 ^ k * m : ℕ) : ℝ)) +
      realLogPowerDirichletPower order (1 / 2 : ℂ)
        (((2 ^ k * m + 1 : ℕ) : ℝ))

theorem c2CenterStencil_eval_logPower_eq_fiberAllOrderBracket
    (order j : ℕ) :
    evalFormalStencil
        (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
        (centerStencil 2 j) =
      c2FiberAllOrderBracket order
        (c2AlignedIndexCore j) (c2AlignedIndexDepth j) := by
  rw [c2CenterStencil_eq_fiberAtomBracket]
  simp [evalFormalStencil, atom]
  have hleft := c2FiberPoint_minus_eq_nat
    (c2AlignedIndexCore j) (c2AlignedIndexDepth j)
    (c2AlignedIndexCore_pos j)
  have hright := c2FiberPoint_plus_eq_nat
    (c2AlignedIndexCore j) (c2AlignedIndexDepth j)
  simp only [c2FiberAllOrderBracket]
  rw [← hleft, ← hright]
  push_cast
  simp [c2FiberPoint]

def c2FiberNativeTaylorBracket (order m k : ℕ) : ℂ :=
  nativeDirichletSlopeTaylorCoefficient order (2 ^ k * m - 1) -
    2 * nativeDirichletSlopeTaylorCoefficient order (2 ^ k * m) +
      nativeDirichletSlopeTaylorCoefficient order (2 ^ k * m + 1)

theorem c2CenterStencil_nativeTaylorCoefficient_eq_fiberBracket
    (order j : ℕ) :
    evalFormalStencil
        (fun n => nativeDirichletSlopeTaylorCoefficient order n)
        (centerStencil 2 j) =
      c2FiberNativeTaylorBracket order
        (c2AlignedIndexCore j) (c2AlignedIndexDepth j) := by
  rw [c2CenterStencil_eq_fiberAtomBracket]
  simp [evalFormalStencil, atom, c2FiberNativeTaylorBracket]

theorem c2Tower_logPower_criticalAmplitude_eq_stirling_newtonJet
    (k r : ℕ) :
    Real.log ((2 : ℝ) ^ k) ^ r *
        CPFormal.Carry.Cp.criticalAmplitude 2 k =
      Real.log (2 : ℝ) ^ r *
        ∑ j ∈ Finset.range (r + 1),
          (Nat.stirlingSecond r j : ℝ) * (j.factorial : ℝ) *
            ProjectiveDepth.newtonJet
              (CPFormal.Analytic.Cp.primeCarryAmplitudeRatio 2) j k := by
  simpa using
    (ProjectiveDepth.tower_log_power_criticalAmplitude_eq_stirling_newtonJet
      2 k r)

theorem c2FiniteCamera_allOrderReadout_eq_seed_add_fiberBracketSum
    (value : ℕ → ℂ) (M : ℕ) :
    evalFormalStencil value (finiteStencil 2 M) =
      evalFormalStencil value (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          (evalFormalStencil value
            (centeredBracketStencil
              (2 ^ c2AlignedIndexDepth j * c2AlignedIndexCore j) 1)) := by
  rw [c2FiniteCameraStencil_eq_seed_add_fiberSum]
  simp [evalFormalStencil]

theorem c2FiniteCamera_allOrderLogPowerReadout_eq_seed_add_fiberBracketSum
    (M order : ℕ) :
    evalFormalStencil
        (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
        (finiteStencil 2 M) =
      evalFormalStencil
          (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
          (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          c2FiberAllOrderBracket order
            (c2AlignedIndexCore j) (c2AlignedIndexDepth j) := by
  rw [c2FiniteCamera_allOrderReadout_eq_seed_add_fiberBracketSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [evalFormalStencil, centeredBracketStencil, atom, c2FiberAllOrderBracket]

theorem c2FiniteCamera_nativeTaylorCoefficient_eq_seed_add_fiberBracketSum
    (M order : ℕ) :
    evalFormalStencil
        (fun n => nativeDirichletSlopeTaylorCoefficient order n)
        (finiteStencil 2 M) =
      evalFormalStencil
          (fun n => nativeDirichletSlopeTaylorCoefficient order n)
          (seedStencil 2) +
        ∑ j ∈ Finset.range M,
          c2FiberNativeTaylorBracket order
            (c2AlignedIndexCore j) (c2AlignedIndexDepth j) := by
  rw [c2FiniteCamera_allOrderReadout_eq_seed_add_fiberBracketSum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [evalFormalStencil, centeredBracketStencil, atom,
    c2FiberNativeTaylorBracket]

theorem c2AlignedCamera_allOrderBracket_eq_fiber (order j : ℕ) :
    evalFormalStencil
        (fun n => realLogPowerDirichletPower order (1 / 2 : ℂ) (n : ℝ))
        (centerStencil 2 j) =
      c2FiberAllOrderBracket order
        (c2AlignedIndexCore j) (c2AlignedIndexDepth j) :=
  c2CenterStencil_eval_logPower_eq_fiberAllOrderBracket order j

end
end CarrySelfAdjointOperator

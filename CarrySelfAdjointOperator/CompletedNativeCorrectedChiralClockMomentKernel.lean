import CarrySelfAdjointOperator.CompletedNativeCorrectedChiralClockTower
import CarrySelfAdjointOperator.GreenWronskianHankelBridge
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

noncomputable section

def correctedNativeClockParityIndex : ℕ ⊕ ℕ → ℕ
  | Sum.inl n => 2 * n
  | Sum.inr n => 2 * n + 1

theorem
canonicalCompletedNativeCorrectedClockTowerCoefficient_parity_eq_greenWronskianMomentKernel
    (i j : ℕ ⊕ ℕ) :
    canonicalCompletedNativeCorrectedClockTowerCoefficient
        (correctedNativeClockParityIndex i)
        (correctedNativeClockParityIndex j) =
      ((greenWronskianMomentKernel
          canonicalCompletedNativeLogDerivativeMoment i j : ℝ) : ℂ) := by
  rcases i with i | i <;>
  rcases j with j | j <;>
  simp [correctedNativeClockParityIndex,
    canonicalCompletedNativeCorrectedClockTowerCoefficient,
    greenWronskianMomentKernel]

theorem CorrectedNativeClockTower.parity_eq_greenWronskianMomentKernel
    {M : ℕ} (tower : CorrectedNativeClockTower M)
    (i j : ℕ ⊕ ℕ) :
    tower.coefficient
        (correctedNativeClockParityIndex i)
        (correctedNativeClockParityIndex j) =
      ((greenWronskianMomentKernel
          canonicalCompletedNativeLogDerivativeMoment i j : ℝ) : ℂ) := by
  rw [tower.coefficient_eq_canonical]
  exact
    canonicalCompletedNativeCorrectedClockTowerCoefficient_parity_eq_greenWronskianMomentKernel
      i j

end

end CarrySelfAdjointOperator

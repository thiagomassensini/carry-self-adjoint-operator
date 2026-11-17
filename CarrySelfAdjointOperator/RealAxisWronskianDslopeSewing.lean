import CarrySelfAdjointOperator.CompletedGreenRealKernelClosure
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import Mathlib.Tactic

/-!
# Division-free real-axis Wronskian-to-dslope normalization
This identity is scalar algebra, not a positive Green kernel factorization.
It retains the parameter-separation (w-z), including its zero at collision.
-/

namespace CarrySelfAdjointOperator
open scoped ComplexConjugate
noncomputable section

theorem completedGreenWronskian_eq_divisionFreeDslope
    (F Psi : ℂ → ℂ) (z w : ℂ)
    (hzF : F z ≠ 0) (hwF : F w ≠ 0)
    (hzReal : conj (F z) = F z)
    (hzCompanionReal : conj (Psi z) = Psi z) :
    completedGreenWronskian F Psi w z =
      2 * F z * F w * (w-z) *
        dslope (completedGreenNormalizedResponse F Psi) z w := by
  have hds := sub_smul_dslope (completedGreenNormalizedResponse F Psi) z w
  simp only [smul_eq_mul] at hds
  have hnormalizer :
      2 * F z * F w *
          (completedGreenNormalizedResponse F Psi w -
           completedGreenNormalizedResponse F Psi z) =
        F z * Psi w - F w * Psi z := by
    simp only [completedGreenNormalizedResponse]
    field_simp [hzF, hwF]
  unfold completedGreenWronskian
  rw [hzReal, hzCompanionReal]
  calc
    Psi w * F z - F w * Psi z =
      2 * F z * F w *
          (completedGreenNormalizedResponse F Psi w -
           completedGreenNormalizedResponse F Psi z) := by rw [hnormalizer]; ring
    _ = 2 * F z * F w *
          ((w-z) * dslope (completedGreenNormalizedResponse F Psi) z w) := by
      rw [hds]
    _ = _ := by ring

/-- The canonical completed characteristic and its companion have real
boundary values for real height, hence the formula applies without
truncation or an off-diagonal case distinction. -/
theorem completedNativeWronskian_ofReal_eq_divisionFreeDslope
    (t u : ℝ)
    (htF : completedNativeOperatorCharacteristic (t : ℂ) ≠ 0)
    (huF : completedNativeOperatorCharacteristic (u : ℂ) ≠ 0) :
    completedGreenWronskian completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (u : ℂ) (t : ℂ) =
      2 * completedNativeOperatorCharacteristic (t : ℂ) *
        completedNativeOperatorCharacteristic (u : ℂ) * ((u-t : ℝ) : ℂ) *
        dslope (completedGreenNormalizedResponse
          completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion) (t : ℂ) (u : ℂ) := by
  have hFreal : conj (completedNativeOperatorCharacteristic (t : ℂ)) =
      completedNativeOperatorCharacteristic (t : ℂ) :=
    Complex.conj_eq_iff_im.mpr (completedNativeOperatorCharacteristic_ofReal_im_eq_zero t)
  have hderivre : (deriv completedNativeOperatorCharacteristic (t : ℂ)).im = 0 := by
    simpa [iteratedDeriv_zero] using
      (iteratedDeriv_completedNativeOperatorCharacteristic_zero_im 1 t)
  have hCreal : conj (completedNativeOperatorBoundaryCompanion (t : ℂ)) =
      completedNativeOperatorBoundaryCompanion (t : ℂ) := by
    rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
    exact Complex.conj_eq_iff_im.mpr (by simpa using hderivre)
  have h := completedGreenWronskian_eq_divisionFreeDslope
    completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion
    (t : ℂ) (u : ℂ) htF huF hFreal hCreal
  simpa only [Complex.ofReal_sub] using h

end
end CarrySelfAdjointOperator

/-! Source-independent and native real-axis dependency audits. -/
#print axioms CarrySelfAdjointOperator.completedGreenWronskian_eq_divisionFreeDslope
#print axioms CarrySelfAdjointOperator.completedNativeWronskian_ofReal_eq_divisionFreeDslope

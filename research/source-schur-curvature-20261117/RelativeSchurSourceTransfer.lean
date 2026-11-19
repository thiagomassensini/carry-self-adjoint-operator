import CarrySelfAdjointOperator.NativeSourceSchurThetaIntegral
import Mathlib.Tactic

/-!
# Relative source form comparison -> Schur pivot lower bound

A *relative*, uniform-in-directions comparison of original completed
source forms controls the Schur pivot without presupposing its sign.
No positivity of the new block, no heights of zeros and no replacement
positive Gram is manufactured.

The comparison is a SOURCE OBLIGATION, not proved by Parseval alone.
-/

namespace CarrySelfAdjointOperator.RelativeSchurSourceTransfer
open CarrySelfAdjointOperator
open scoped Matrix BigOperators
noncomputable section
set_option autoImplicit false

/-- The source is tested exactly on the critical direction of the moment
sequence m. The signed comparison is to an independently certified reference
g, positive only at the old prefix. -/
theorem schur_lower_of_relative_form_comparison
    (m g : ℕ → ℝ) (s n : ℕ) (δ : ℝ)
    (hδ : 0 ≤ 1-δ)
    (hg : (sourceMomentMatrix g s n).PosDef)
    (hcompare : ∀ x : Fin (n+1) → ℝ,
      (1-δ) * sourceMomentQuadratic g s (n+1) x ≤
        sourceMomentQuadratic m s (n+1) x) :
    (1-δ)*sourceMomentSchur g s n ≤ sourceMomentSchur m s n := by
  let x : Fin (n+1) → ℝ :=
    Fin.snoc (-((sourceMomentMatrix m s n)⁻¹ *ᵥ
      sourceMomentCoupling m s n)) 1
  have hcrit : sourceMomentQuadratic m s (n+1) x =
      sourceMomentSchur m s n := by
    exact sourceMomentSchur_critical_direction_total m s n
  have hlower : sourceMomentSchur g s n ≤
      sourceMomentQuadratic g s (n+1) x := by
    dsimp [x]
    rw [sourceMomentSchur_sewing g s n hg]
    simp only [one_pow, mul_one, one_smul]
    have hnonneg : 0 ≤ sourceMomentQuadratic g s n
        (-((sourceMomentMatrix m s n)⁻¹ *ᵥ sourceMomentCoupling m s n) +
          (sourceMomentMatrix g s n)⁻¹ *ᵥ sourceMomentCoupling g s n) := by
      change 0 ≤ star _ ⬝ᵥ (sourceMomentMatrix g s n *ᵥ _)
      exact hg.posSemidef.dotProduct_mulVec_nonneg _
    linarith
  calc
    (1-δ)*sourceMomentSchur g s n ≤
        (1-δ)*sourceMomentQuadratic g s (n+1) x :=
      mul_le_mul_of_nonneg_left hlower hδ
    _ ≤ sourceMomentSchur m s n := by
      rw [← hcrit]
      exact hcompare x

/-- The stronger absolute quadratic error assumption implies the required
one-sided comparison by elementary order algebra. -/
theorem schur_lower_of_signed_relative_form_budget
    (m g : ℕ → ℝ) (s n : ℕ) (δ : ℝ)
    (hδ1 : δ < 1)
    (hg : (sourceMomentMatrix g s n).PosDef)
    (hbudget : ∀ x : Fin (n+1) → ℝ,
      |sourceMomentQuadratic m s (n+1) x -
        sourceMomentQuadratic g s (n+1) x| ≤
        δ*sourceMomentQuadratic g s (n+1) x) :
    (1-δ)*sourceMomentSchur g s n ≤ sourceMomentSchur m s n := by
  apply schur_lower_of_relative_form_comparison m g s n δ (by linarith) hg
  intro x
  have h := (abs_le.mp (hbudget x)).1
  nlinarith

/-- A certified *positive* reference pivot plus strict relative source
control propagates positivity to the genuine new Schur pivot. No sign of
the new source pivot occurs in the hypotheses. -/
theorem schur_pos_of_relative_source_certificate
    (m g : ℕ → ℝ) (s n : ℕ) (δ : ℝ)
    (hδ : δ < 1)
    (hg : (sourceMomentMatrix g s n).PosDef)
    (hgSchur : 0 < sourceMomentSchur g s n)
    (hcompare : ∀ x : Fin (n+1) → ℝ,
      (1-δ)*sourceMomentQuadratic g s (n+1) x ≤
        sourceMomentQuadratic m s (n+1) x) :
    0 < sourceMomentSchur m s n := by
  have hlo := schur_lower_of_relative_form_comparison m g s n δ
    (by linarith) hg hcompare
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hδ) hgSchur) hlo

/-- In the original completed source, the native remainder is c0 times
the canonical Schur pivot, c0>0. Only a reference/source comparison
in the completed moment metric is used here. -/
theorem native_remainder_pos_of_relative_source_certificate
    (g : ℕ → ℝ) (s n : ℕ) (δ : ℝ)
    (hδ : δ < 1)
    (hg : (sourceMomentMatrix g s n).PosDef)
    (hgSchur : 0 < sourceMomentSchur g s n)
    (hcompare : ∀ x : Fin (n+1) → ℝ,
      (1-δ)*sourceMomentQuadratic g s (n+1) x ≤
        sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment
          s (n+1) x) :
    0 < nativeSourceSchurRemainder s n := by
  rw [nativeSourceSchurRemainder_eq]
  have hc : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  exact mul_pos hc
    (schur_pos_of_relative_source_certificate
      canonicalCompletedNativeLogDerivativeMoment g s n δ
      hδ hg hgSchur hcompare)

#print axioms schur_lower_of_relative_form_comparison
#print axioms schur_lower_of_signed_relative_form_budget
#print axioms native_remainder_pos_of_relative_source_certificate
end
end CarrySelfAdjointOperator.RelativeSchurSourceTransfer

import CarrySelfAdjointOperator.CompletedC3CoisometricAmbientMomentGate
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.C3GammaCameraTraceObstruction
import Mathlib.Tactic

/-!
# Central transverse-curvature decision for the ambient C3 carrier

The full completed vertical modulus energy has an exact product-rule curvature
formula. It is weighted by the squared modulus of the completed native
characteristic. This file compares that curvature with the unweighted
ordinary C3 Dirichlet-gradient energy required by the proposed ambient
zeroth-moment sewing.

The comparison is deliberately stopped at order zero. The strict inequalities
already available for the native moment, the completed characteristic, and the
central gradient show that the proposed curvature identity is false. This is a
decision for this ambient/source-matched test; it does not construct or rule
out another carrier.
-/

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

noncomputable section

/-- On the central vertical line, the energy is the squared modulus of the
completed characteristic at I * y. -/
@[simp] theorem completedNativeVerticalModulusEnergy_zero_apply (y : ℝ) :
    completedNativeVerticalModulusEnergy 0 y =
      ‖completedNativeOperatorCharacteristic (Complex.I * (y : ℂ))‖ ^ 2 := by
  simp [completedNativeVerticalModulusEnergy]

/-- The central curvature defect: full completed vertical modulus curvature
minus the unweighted four-times ordinary C3 gradient energy. -/
def canonicalCompletedAmbientCentralCurvatureDefect : ℝ :=
  iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 -
    4 * ‖canonicalCompletedC3DirichletGradientState
      (operatorHeightParameter 0)
      (by norm_num [operatorHeightParameter])‖ ^ 2

/-- Expanding the exact vertical-energy curvature theorem leaves the
characteristic-weighted native moment against the ordinary gradient energy.
No channel is discarded from the product-rule curvature. -/
theorem
    canonicalCompletedAmbientCentralCurvatureDefect_eq_characteristicWeightedMoment_sub_gradient :
    canonicalCompletedAmbientCentralCurvatureDefect =
      4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
        canonicalCompletedNativeLogDerivativeMoment 0 -
      4 * ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  unfold canonicalCompletedAmbientCentralCurvatureDefect
  rw [completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_moment_zero]

/-- The ordinary C3 gradient at the central height has energy strictly above
the native ruler. This is the already calibrated reflected Green energy,
transported to the same operatorHeightParameter 0 state. -/
theorem
    canonicalCompletedC3DirichletGradientState_operatorHeight_zero_norm_sq_gt_sixteenth :
    (1 / 16 : ℝ) <
      ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  have h := infiniteReflectedGreenEnergy_half_gt_sixteenth
  rw [infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq] at h
  simpa [canonicalCentralCompletedDirichletGradientState,
    operatorHeightParameter] using h

/-- The characteristic-weighted native term is strictly below the ruler.
The proof keeps the sign of the native moment explicit; in the actual
formalization it is positive, while the nonpositive branch also suffices for
the strict bound. -/
theorem
    canonicalCompletedAmbientCentralCharacteristicWeightedMoment_lt_sixteenth :
    4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
        canonicalCompletedNativeLogDerivativeMoment 0 < (1 / 16 : ℝ) := by
  have hF := completedNativeCharacteristic_zero_norm_le_half
  have hFsq : ‖completedNativeOperatorCharacteristic 0‖ ^ 2 ≤ (1 / 4 : ℝ) := by
    have hs := (sq_le_sq₀ (norm_nonneg (completedNativeOperatorCharacteristic 0))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hF
    norm_num at hs ⊢
    exact hs
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  by_cases hnonneg :
      0 ≤ canonicalCompletedNativeLogDerivativeMoment 0
  · have h1 :
        4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
            canonicalCompletedNativeLogDerivativeMoment 0 ≤
          4 * (1 / 4 : ℝ) *
            canonicalCompletedNativeLogDerivativeMoment 0 :=
      mul_le_mul_of_nonneg_right (by nlinarith [hFsq]) hnonneg
    have h2 :
        4 * (1 / 4 : ℝ) *
            canonicalCompletedNativeLogDerivativeMoment 0 <
          (1 / 16 : ℝ) := by
      nlinarith [hh]
    exact h1.trans_lt h2
  · have hneg : canonicalCompletedNativeLogDerivativeMoment 0 < 0 :=
      lt_of_not_ge hnonneg
    have hnonpos :
        4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
            canonicalCompletedNativeLogDerivativeMoment 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) (sq_nonneg _)) hneg.le
    exact lt_of_le_of_lt hnonpos (by norm_num)

/-- The full vertical curvature is itself strictly below the native ruler. -/
theorem completedNativeVerticalModulusEnergy_secondDerivative_zero_lt_sixteenth :
    iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 < (1 / 16 : ℝ) := by
  rw [completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_moment_zero]
  exact canonicalCompletedAmbientCentralCharacteristicWeightedMoment_lt_sixteenth

/-- The ordinary gradient energy required by the proposed transverse identity
is strictly above one quarter after multiplication by four. -/
theorem
    canonicalCompletedC3DirichletGradientState_operatorHeight_zero_four_norm_sq_gt_quarter :
    (1 / 4 : ℝ) <
      4 * ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  have h :=
    canonicalCompletedC3DirichletGradientState_operatorHeight_zero_norm_sq_gt_sixteenth
  nlinarith

/-- The ambient central curvature defect is strictly negative. The
characteristic-weighted full curvature lies strictly below the ruler, whereas
the required unweighted ordinary-gradient energy lies strictly above after
multiplication by four. -/
theorem canonicalCompletedAmbientCentralCurvatureDefect_neg :
    canonicalCompletedAmbientCentralCurvatureDefect < 0 := by
  have hweighted :=
    completedNativeVerticalModulusEnergy_secondDerivative_zero_lt_sixteenth
  have hgrad :=
    canonicalCompletedC3DirichletGradientState_operatorHeight_zero_four_norm_sq_gt_quarter
  calc
    canonicalCompletedAmbientCentralCurvatureDefect =
        4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
            canonicalCompletedNativeLogDerivativeMoment 0 -
          4 * ‖canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter 0)
            (by norm_num [operatorHeightParameter])‖ ^ 2 :=
      canonicalCompletedAmbientCentralCurvatureDefect_eq_characteristicWeightedMoment_sub_gradient
    _ < (1 / 16 : ℝ) -
          4 * ‖canonicalCompletedC3DirichletGradientState
            (operatorHeightParameter 0)
            (by norm_num [operatorHeightParameter])‖ ^ 2 := by
      rw [completedNativeVerticalModulusEnergy_secondDerivative_zero_eq_moment_zero] at hweighted
      exact sub_lt_sub_right hweighted _
    _ < 0 := by nlinarith [hgrad]

/-- The proposed ambient transverse-curvature identity is false. -/
theorem
    completedNativeVerticalModulusEnergy_secondDerivative_zero_ne_four_gradientEnergy :
    iteratedDeriv 2 (completedNativeVerticalModulusEnergy 0) 0 ≠
      4 * ‖canonicalCompletedC3DirichletGradientState
        (operatorHeightParameter 0)
        (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  intro h
  have hd := canonicalCompletedAmbientCentralCurvatureDefect_neg
  have hz : canonicalCompletedAmbientCentralCurvatureDefect = 0 := by
    unfold canonicalCompletedAmbientCentralCurvatureDefect
    rw [h]
    ring
  linarith

/-- Consequently the normalized ambient response state cannot have zeroth
norm square equal to the canonical native zeroth moment. This is the
equivalent carrier-level failure supplied by the ambient moment gate. -/
theorem
    norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_ne_moment_zero :
    ‖canonicalCompletedC3NormalizedAmbientResponseState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 ≠
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  intro h
  have hcurvature :=
    (norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero_eq_moment_zero_iff_transverseCurvature).mp h
  exact completedNativeVerticalModulusEnergy_secondDerivative_zero_ne_four_gradientEnergy
    hcurvature

/-- The failure is strict at the normalized ambient Gram level: the
source-matched ordinary gradient divided by the completed characteristic
weight is larger than the native zeroth moment. -/
theorem
    canonicalCompletedC3NormalizedAmbientResponseState_zero_norm_sq_gt_moment_zero :
    canonicalCompletedNativeLogDerivativeMoment 0 <
      ‖canonicalCompletedC3NormalizedAmbientResponseState 0
        (by norm_num [operatorHeightParameter])‖ ^ 2 := by
  rw [norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero]
  have hF := completedNativeCharacteristic_zero_norm_le_half
  have hFsq : ‖completedNativeOperatorCharacteristic 0‖ ^ 2 ≤ (1 / 4 : ℝ) := by
    have hs := (sq_le_sq₀ (norm_nonneg (completedNativeOperatorCharacteristic 0))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hF
    norm_num at hs ⊢
    exact hs
  have hFne : completedNativeOperatorCharacteristic 0 ≠ 0 :=
    completedNativeOperatorCharacteristic_zero_ne_zero
  have hFpos : 0 < ‖completedNativeOperatorCharacteristic 0‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hFne)
  have hgrad :=
    canonicalCompletedC3DirichletGradientState_operatorHeight_zero_norm_sq_gt_sixteenth
  have hratio :
      (1 / 4 : ℝ) <
        ‖canonicalCompletedC3DirichletGradientState
          (operatorHeightParameter 0)
          (by norm_num [operatorHeightParameter])‖ ^ 2 /
          ‖completedNativeOperatorCharacteristic 0‖ ^ 2 := by
    apply (lt_div_iff₀ hFpos).2
    nlinarith [hFsq, hgrad]
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  exact lt_trans hh (lt_trans (by norm_num) hratio)

end

end CarrySelfAdjointOperator

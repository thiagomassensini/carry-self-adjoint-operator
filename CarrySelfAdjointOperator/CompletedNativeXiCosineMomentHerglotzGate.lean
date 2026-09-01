import CarrySelfAdjointOperator.CompletedNativeHerglotzFourthOrderGate
import CarrySelfAdjointOperator.CompletedNativeXiThetaMomentBounds
import Mathlib.Tactic

/-!
# Low cosine-moment criterion for the two-point Herglotz gate

For an even cosine transform with mass `μ₀`, second moment `μ₂`, and
fourth moment `μ₄`, the first three reduced Taylor coefficients have the
normalization

`c₀ = μ₀`,  `c₁ = -μ₂ / 2`,  `c₂ = μ₄ / 24`.

Under this normalization the two direct Herglotz curvature signs reduce to

`0 < μ₀`,  `0 < μ₂`,  and  `μ₀ μ₄ < 3 μ₂²`.

Thus the first polarized Herglotz/Pick section only asks for a strict
sub-Gaussian fourth-moment inequality for the completed Xi cosine kernel.
The theta-tail bounds now supply that inequality, so this file transports the
certified moment estimate all the way to unconditional two-point
Herglotz/Pick positivity.
-/

namespace CarrySelfAdjointOperator

open Filter
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- Low-order cosine-moment certificate for the actual reduced completed
characteristic coefficients. -/
def CanonicalCompletedNativeXiCosineLowMomentCertificate : Prop :=
  ∃ μ₀ μ₂ μ₄ : ℝ,
    0 < μ₀ ∧
      0 < μ₂ ∧
      μ₀ * μ₄ < 3 * μ₂ ^ 2 ∧
      completedNativeRealEvenCharacteristicCoefficient 0 = μ₀ ∧
      completedNativeRealEvenCharacteristicCoefficient 1 = -μ₂ / 2 ∧
      completedNativeRealEvenCharacteristicCoefficient 2 = μ₄ / 24

/-- After the positive cosine representation has been differentiated, the
canonical low-moment certificate has only one remaining input: the strict
fourth-moment inequality for the concrete kernel. -/
theorem canonicalCompletedNativeXiCosineLowMomentCertificate_of_momentInequality
    (hkurtosis :
      completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 <
        3 * completedNativeXiCosineMoment 1 ^ 2) :
    CanonicalCompletedNativeXiCosineLowMomentCertificate := by
  refine ⟨completedNativeXiCosineMoment 0,
    completedNativeXiCosineMoment 1,
    completedNativeXiCosineMoment 2,
    completedNativeXiCosineMoment_pos 0,
    completedNativeXiCosineMoment_pos 1,
    hkurtosis, ?_, ?_, ?_⟩
  · exact completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment
  · exact completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment
  · exact completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment

/-- Conversely, coefficient uniqueness forces any low-moment certificate to
contain the actual three moments of the concrete Xi kernel. -/
theorem canonicalCompletedNativeXiCosineLowMomentCertificate_iff_momentInequality :
    CanonicalCompletedNativeXiCosineLowMomentCertificate ↔
      completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2 <
        3 * completedNativeXiCosineMoment 1 ^ 2 := by
  constructor
  · rintro ⟨μ₀, μ₂, μ₄, _hμ₀, _hμ₂, hk, hc0, hc1, hc2⟩
    have hμ₀ : μ₀ = completedNativeXiCosineMoment 0 :=
      hc0.symm.trans
        completedNativeRealEvenCharacteristicCoefficient_zero_eq_xiCosineMoment
    have hμ₂ : μ₂ = completedNativeXiCosineMoment 1 := by
      rw [completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment] at hc1
      linarith
    have hμ₄ : μ₄ = completedNativeXiCosineMoment 2 := by
      rw [completedNativeRealEvenCharacteristicCoefficient_two_eq_xiCosineMoment] at hc2
      linarith
    simpa [hμ₀, hμ₂, hμ₄] using hk
  · exact canonicalCompletedNativeXiCosineLowMomentCertificate_of_momentInequality

/-- A positive mass and second moment give the direct second-order
characteristic-curvature sign. -/
theorem
    canonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive_of_xiCosineLowMoments
    (hcosine : CanonicalCompletedNativeXiCosineLowMomentCertificate) :
    CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive := by
  rcases hcosine with
    ⟨μ₀, μ₂, μ₄, hμ₀, hμ₂, _hkurtosis, hc0, hc1, _hc2⟩
  unfold CanonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive
  rw [hc0, hc1]
  exact mul_neg_of_pos_of_neg hμ₀
    (div_neg_of_neg_of_pos (neg_neg_of_pos hμ₂) (by norm_num))

/-- The strict normalized fourth-moment inequality is exactly strong enough
for the fourth-order logarithmic-curvature sign. -/
theorem
    canonicalCompletedNativeFourthOrderLogCurvaturePositive_of_xiCosineLowMoments
    (hcosine : CanonicalCompletedNativeXiCosineLowMomentCertificate) :
    CanonicalCompletedNativeFourthOrderLogCurvaturePositive := by
  rcases hcosine with
    ⟨μ₀, μ₂, μ₄, _hμ₀, _hμ₂, hkurtosis, hc0, hc1, hc2⟩
  unfold CanonicalCompletedNativeFourthOrderLogCurvaturePositive
  rw [hc0, hc1, hc2]
  nlinarith

/-- A low Xi cosine-moment certificate supplies both direct low-order
Herglotz curvature signs. -/
theorem
    canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_of_xiCosineLowMoments
    (hcosine : CanonicalCompletedNativeXiCosineLowMomentCertificate) :
    CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive :=
  ⟨canonicalCompletedNativeSecondOrderCharacteristicCurvaturePositive_of_xiCosineLowMoments
      hcosine,
    canonicalCompletedNativeFourthOrderLogCurvaturePositive_of_xiCosineLowMoments
      hcosine⟩

/-- The strict cosine-moment criterion closes the literal two-point radial
Herglotz section. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_xiCosineLowMoments
    (hcosine : CanonicalCompletedNativeXiCosineLowMomentCertificate) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef :=
  canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_lowOrderCurvature
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_of_xiCosineLowMoments
      hcosine)

/-- Through the exact Cayley congruence, the same criterion closes the
literal two-point chiral Pick section. -/
theorem
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_xiCosineLowMoments
    (hcosine : CanonicalCompletedNativeXiCosineLowMomentCertificate) :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).PosSemidef :=
  canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_lowOrderCurvature
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_of_xiCosineLowMoments
      hcosine)

/-! ## Unconditional closure from the certified theta bounds -/

/-- The concrete completed-Xi cosine moments satisfy the full low-order
certificate without any remaining analytic hypothesis. -/
theorem canonicalCompletedNativeXiCosineLowMomentCertificate :
    CanonicalCompletedNativeXiCosineLowMomentCertificate :=
  canonicalCompletedNativeXiCosineLowMomentCertificate_of_momentInequality
    completedNativeXiCosineMoment_strict_kurtosis

/-- Both direct low-order Herglotz curvature signs now hold
unconditionally. -/
theorem canonicalCompletedNativeLowOrderHerglotzCurvaturePositive :
    CanonicalCompletedNativeLowOrderHerglotzCurvaturePositive :=
  canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_of_xiCosineLowMoments
    canonicalCompletedNativeXiCosineLowMomentCertificate

/-- Unconditional eventual positivity of the literal two-point radial
Herglotz sample matrix. -/
theorem
    canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialHerglotzSampleMatrix k 2).PosSemidef :=
  canonicalCompletedNativeRadialHerglotzSampleMatrix_two_eventually_posSemidef_of_xiCosineLowMoments
    canonicalCompletedNativeXiCosineLowMomentCertificate

/-- The exact Cayley congruence gives the corresponding unconditional
two-point chiral Pick positivity. -/
theorem
    canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef :
    ∀ᶠ k : ℕ in atTop,
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k 2).PosSemidef :=
  canonicalCompletedNativeRadialChiralPickSampleMatrix_two_eventually_posSemidef_of_xiCosineLowMoments
    canonicalCompletedNativeXiCosineLowMomentCertificate

end

end CarrySelfAdjointOperator

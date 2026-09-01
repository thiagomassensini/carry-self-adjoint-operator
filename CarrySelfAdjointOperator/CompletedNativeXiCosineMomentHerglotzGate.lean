import CarrySelfAdjointOperator.CompletedNativeHerglotzFourthOrderGate
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
This file proves the algebraic transport from such a low-moment certificate;
it does not assert the missing integral representation or its kurtosis bound.
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

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundaryStieltjesGate
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralJetEnergyControl
import CarrySelfAdjointOperator.CompletedNativeChiralReturnMixedSourceJets
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEightBoundaryFace
import CarrySelfAdjointOperator.CompletedNativeAllOrderMomentUpperBound
import CarrySelfAdjointOperator.CompletedNativeXiThetaMoments
import CarrySelfAdjointOperator.CompletedNativeThetaFourteenthTail

namespace CarrySelfAdjointOperator
open scoped ComplexConjugate

#check nativeSourceFiniteBoundaryEnergy

#check nativeSourceFiniteBoundaryEnergy_even_split

#check nativeSourceEvenBoundary_positive_iff_stieltjes

-- Esta é a nossa pergunta, não uma prova.
def BoundaryGoal : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ x : Fin (2*n) → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy (2*n) x

#check canonicalCompletedNativeLogDerivativeMoment_zero_pos

example (x : Fin 2 → ℂ) :
    nativeSourceFiniteBoundaryEnergy 2 x =
      4 * (
        primeDepthGeometricMoment 0 *
          ((starRingEnd ℂ) (x 0) * x 0).re +
        primeDepthGeometricMoment 1 *
          ((starRingEnd ℂ) (x 1) * x 1).re
      ) := by
  simpa [
    Fin.sum_univ_one,
    nativeSourceEvenBoundaryPhase,
    nativeSourceOddBoundaryPhase,
    nativeSourceEvenBoundaryIndex,
    nativeSourceOddBoundaryIndex
  ] using
    (nativeSourceFiniteBoundaryEnergy_even_split 1 x)

example :
    0 < primeDepthGeometricMoment 0 ∧
    0 < primeDepthGeometricMoment 1 := by
  simpa only [primeDepthGeometricMoment_eq_canonical] using
    (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
      canonicalCompletedNativeLowOrderHerglotzCurvaturePositive)

theorem boundaryEnergy_two_pos
    (x : Fin 2 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 2 x := by

  have hm :
      0 < primeDepthGeometricMoment 0 ∧
      0 < primeDepthGeometricMoment 1 := by
    simpa only [primeDepthGeometricMoment_eq_canonical] using
      (canonicalCompletedNativeLowOrderHerglotzCurvaturePositive_iff_moments.mp
        canonicalCompletedNativeLowOrderHerglotzCurvaturePositive)

  have hE :
      nativeSourceFiniteBoundaryEnergy 2 x =
        4 * (
          primeDepthGeometricMoment 0 *
            ((starRingEnd ℂ) (x 0) * x 0).re +
          primeDepthGeometricMoment 1 *
            ((starRingEnd ℂ) (x 1) * x 1).re
        ) := by
    simpa [
      Fin.sum_univ_one,
      nativeSourceEvenBoundaryPhase,
      nativeSourceOddBoundaryPhase,
      nativeSourceEvenBoundaryIndex,
      nativeSourceOddBoundaryIndex
    ] using nativeSourceFiniteBoundaryEnergy_even_split 1 x

  have hnorm (z : ℂ) :
      ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
    rw [← Complex.normSq_eq_conj_mul_self]
    rfl

  have hc : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i
    · exact h.1
    · exact h.2

  rw [hE, hnorm (x 0), hnorm (x 1)]

  rcases hc with h0 | h1
  · apply mul_pos (by norm_num)
    exact add_pos_of_pos_of_nonneg
      (mul_pos hm.1 (Complex.normSq_pos.mpr h0))
      (mul_nonneg hm.2.le (Complex.normSq_nonneg _))
  · apply mul_pos (by norm_num)
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hm.1.le (Complex.normSq_nonneg _))
      (mul_pos hm.2 (Complex.normSq_pos.mpr h1))


-- Identificação exata com a energia original.
theorem boundaryEnergy_four_eq_source
    (x : Fin 4 → ℂ) :
    nativeSourceFiniteBoundaryEnergy 4 x =
      nativeSourceFourBoundaryEnergy x := by
  simpa only [
    nativeSourceFiniteBoundaryEnergy,
    nativeSourceFourBoundaryExtension
  ] using
    (nativeSourceFourBoundaryEnergy_eq_alternating_green x).symm

-- Positividade da energia original na dimensão 4.
theorem boundaryEnergy_four_pos
    (x : Fin 4 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 4 x := by
  rw [boundaryEnergy_four_eq_source]
  exact nativeSourceFourBoundaryEnergy_pos x hx
theorem boundaryEnergy_six_pos
    (x : Fin 6 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 6 x := by
  rw [nativeSourceFiniteBoundaryEnergy_six]
  exact nativeSourceSixBoundaryEnergy_pos x hx

#check nativeSourceFiniteBoundaryEnergy_eight
#check nativeSourceFiniteBoundaryEnergy_eight_pos_iff
theorem boundaryEnergy_eight_pos_of_ceiling
    (h : completedNativeRealEvenCharacteristicCoefficient 8 <
      nativeSourceEightCharacteristicCeiling)
    (x : Fin 8 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 8 x := by

  have hp : 0 < nativeSourceEightOddDiscriminant :=
    nativeSourceEightOddDiscriminant_pos_iff_characteristic_ceiling.mpr h

  exact (nativeSourceFiniteBoundaryEnergy_eight_pos_iff.mpr hp) x hx
theorem boundaryEnergy_eight_iff_ceiling :
    (∀ x : Fin 8 → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy 8 x) ↔
    completedNativeRealEvenCharacteristicCoefficient 8 <
      nativeSourceEightCharacteristicCeiling := by
  exact nativeSourceFiniteBoundaryEnergy_eight_pos_iff.trans
    nativeSourceEightOddDiscriminant_pos_iff_characteristic_ceiling
theorem boundaryEnergy_eight_coefficient_theta :
    completedNativeRealEvenCharacteristicCoefficient 8 =
      (240 * completedNativeThetaTailMoment 14 -
        (1 / 4 : ℝ) * completedNativeThetaTailMoment 16) /
        ((16 : ℕ).factorial : ℝ) := by
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 8]
  have hμ := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 7
  norm_num at hμ ⊢
  rw [hμ]
theorem boundaryEnergy_eight_iff_theta_lower :
    (∀ x : Fin 8 → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy 8 x) ↔
    960 * completedNativeThetaTailMoment 14 -
      4 * ((16 : ℕ).factorial : ℝ) *
        nativeSourceEightCharacteristicCeiling <
      completedNativeThetaTailMoment 16 := by
  rw [boundaryEnergy_eight_iff_ceiling,
    boundaryEnergy_eight_coefficient_theta]
  have hf :
      (0 : ℝ) < ((16 : ℕ).factorial : ℝ) := by
    positivity
  constructor
  · intro h
    have hh := (div_lt_iff₀ hf).mp h
    -- (240*μ₁₄ - 1/4*μ₁₆)/16! < ceiling
    -- 240*μ₁₄ - 1/4*μ₁₆ < ceiling * 16!
    -- multiply by 4: 960*μ₁₄ - μ₁₆ < 4*ceiling*16!
    -- 960*μ₁₄ - 4*ceiling*16! < μ₁₆
    have h1 : 240 * completedNativeThetaTailMoment 14 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 16 <
        nativeSourceEightCharacteristicCeiling * ↑(Nat.factorial 16) := hh
    have h2 : 4 * (240 * completedNativeThetaTailMoment 14 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 16) <
        4 * (nativeSourceEightCharacteristicCeiling * ↑(Nat.factorial 16)) := by
      exact mul_lt_mul_of_pos_left h1 (by norm_num)
    -- simplify LHS: 960*μ₁₄ - μ₁₆
    have h3 : 960 * completedNativeThetaTailMoment 14 - completedNativeThetaTailMoment 16 <
        4 * nativeSourceEightCharacteristicCeiling * ↑(Nat.factorial 16) := by
      ring_nf at h2 ⊢
      linarith
    -- rearrange: 960*μ₁₄ - 4*ceiling*16! < μ₁₆
    linarith
  · intro h
    have h1 : 960 * completedNativeThetaTailMoment 14 - completedNativeThetaTailMoment 16 <
        4 * nativeSourceEightCharacteristicCeiling * ↑(Nat.factorial 16) := by
      ring_nf at h ⊢
      linarith
    -- divide by 4: 240*μ₁₄ - 1/4*μ₁₆ < ceiling*16!
    have h2 : 240 * completedNativeThetaTailMoment 14 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 16 <
        nativeSourceEightCharacteristicCeiling * ↑(Nat.factorial 16) := by
      have h3 : (1 / 4 : ℝ) * (960 * completedNativeThetaTailMoment 14 - completedNativeThetaTailMoment 16) <
          (1 / 4 : ℝ) * (4 * nativeSourceEightCharacteristicCeiling * ↑(Nat.factorial 16)) := by
        exact mul_lt_mul_of_pos_left h1 (by norm_num)
      ring_nf at h3 ⊢
      linarith
    -- divide by 16!: (240*μ₁₄ - 1/4*μ₁₆)/16! < ceiling
    have h4 : (240 * completedNativeThetaTailMoment 14 - (1 / 4 : ℝ) * completedNativeThetaTailMoment 16) /
        ↑(Nat.factorial 16) < nativeSourceEightCharacteristicCeiling := by
      exact (div_lt_iff₀ hf).mpr h2
    linarith

theorem boundaryEnergy_theta_sixteen_upper :
    completedNativeThetaTailMoment 16 <
      960 * completedNativeThetaTailMoment 14 := by

  have hmu : 0 < completedNativeXiCosineMoment 8 :=
    completedNativeXiCosineMoment_pos 8

  have hc8 :
      0 < completedNativeRealEvenCharacteristicCoefficient 8 := by
    rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 8]
    norm_num
    exact hmu

  rw [boundaryEnergy_eight_coefficient_theta] at hc8

  have hf :
      (0 : ℝ) < ((16 : ℕ).factorial : ℝ) := by
    positivity

  have hn := (div_pos_iff_of_pos_right hf).mp hc8
  nlinarith

open MeasureTheory

theorem boundaryEnergy_eight_pos_of_firstMode
    (h :
      960 * completedNativeThetaTailMoment 14 -
        4 * ((16 : ℕ).factorial : ℝ) *
          nativeSourceEightCharacteristicCeiling <
        ∫ u in (0 : ℝ)..(9/8),
          u^16 * thetaFirstMode u) :
    ∀ x : Fin 8 → ℂ, x ≠ 0 →
      0 < nativeSourceFiniteBoundaryEnergy 8 x := by

  have hLower :=
    completedNativeThetaTailMoment_finite_lower_fourteen 16

  apply boundaryEnergy_eight_iff_theta_lower.mpr
  exact lt_of_lt_of_le h hLower

theorem boundaryEnergy_theta16_firstMode_lower :
    thetaFirstMode (17/16 : ℝ) *
        thetaPowerMass 16 0 (9/8) ≤
      completedNativeThetaTailMoment 16 := by

  have hcell :
      thetaFirstMode (17/16 : ℝ) *
          thetaPowerMass 16 0 (9/8) ≤
        ∫ u in (0 : ℝ)..(9/8),
          u^16 * thetaFirstMode u := by

    apply thetaFirstMode_weighted_cell_lower
      16 0 (9/8) (17/16)
      (thetaFirstMode (17/16))
    · norm_num
    · norm_num
    · norm_num
    · norm_num [thetaPowerMass]
    · norm_num [thetaPowerMass]
    · exact le_rfl

  exact hcell.trans
    (completedNativeThetaTailMoment_finite_lower_fourteen 16)

end CarrySelfAdjointOperator

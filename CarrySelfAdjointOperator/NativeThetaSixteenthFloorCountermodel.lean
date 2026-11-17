import CarrySelfAdjointOperator.CompletedNativeThetaBoxEighthObstruction

/-!
# The order-sixteen floor does not remove the old order-eight box countermodel

This module records an exact rational audit only.  It does not identify the
candidate with the actual theta source.  In particular, the rational floor
below is the advertised target of `theta16_floor_sum_lower_target`; this file
does not import or certify that 576-cell integral estimate.
-/
namespace CarrySelfAdjointOperator

noncomputable section

/-- The order-eight rational candidate lies above the proposed order-sixteen
theta floor.  Thus that lower threshold alone does not exclude this candidate
from the old order-fourteen box. -/
theorem thetaBoxEighthCandidate_ge_theta16_floor_target :
    (7675700000 : ℝ) / 1000000000000000000 ≤
      (thetaBoxEighthCandidate 8 : ℝ) := by
  norm_num [thetaBoxEighthCandidate]

/-- The candidate still satisfies every previously used box, recurrence,
raw-moment, and raw-Gram constraint, lies above the proposed order-sixteen
floor threshold, and has an exact negative odd response direction.  This is
an obstruction to this finite list of bounds only, not to the actual source. -/
theorem thetaBoxEighthCandidate_order16_floor_countermodel :
    nativeThetaFourteenthBox (fun n => (thetaBoxEighthCandidate n : ℝ)) ∧
    (∀ n, 0 ≤ thetaBoxEighthCandidate n) ∧
    (∀ n : ℕ, n ≤ 8 →
      thetaBoxEighthCharacteristic n =
        thetaBoxEvenCoefficient thetaBoxEighthCandidate n) ∧
    (∀ n : ℕ, n < 8 →
      thetaBoxEighthCharacteristic 0 * thetaBoxEighthLogMoment n +
        ∑ k ∈ Finset.range n, thetaBoxEighthLogMoment k *
          thetaBoxEighthCharacteristic (n-k) =
            -((n+1 : ℕ) : ℚ) * thetaBoxEighthCharacteristic (n+1)) ∧
    0 < thetaBoxEighthCharacteristic 0 ∧
    (∀ n : ℕ, n ≤ 8 →
      0 < (-1 : ℚ)^n * ((2*n).factorial : ℚ) *
        thetaBoxEighthCharacteristic n) ∧
    Matrix.PosDef (fun i j : Fin 5 =>
      (thetaBoxEighthCandidate (i.val+j.val) : ℝ)) ∧
    Matrix.PosDef (fun i j : Fin 4 =>
      (thetaBoxEighthCandidate (i.val+j.val+1) : ℝ)) ∧
    (7675700000 : ℝ) / 1000000000000000000 ≤
      (thetaBoxEighthCandidate 8 : ℝ) ∧
    (∑ i : Fin 4, ∑ j : Fin 4,
      thetaBoxEighthLogMoment (i.val+j.val+1) *
        thetaBoxEighthOddWitness i * thetaBoxEighthOddWitness j) < 0 := by
  exact ⟨thetaBoxEighthCandidate_inside,
    thetaBoxEighthCandidate_nonneg,
    thetaBoxEighthCharacteristic_from_theta,
    thetaBoxEighthLogMoment_recurrence,
    thetaBoxEighthCharacteristic_zero_pos,
    thetaBoxEighth_raw_cosine_prefix_pos,
    thetaBoxRawTheta0_posDef,
    thetaBoxRawTheta1_posDef,
    thetaBoxEighthCandidate_ge_theta16_floor_target,
    thetaBoxEighthOddWitness_negative⟩

end
end CarrySelfAdjointOperator

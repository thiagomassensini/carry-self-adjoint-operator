import CarrySelfAdjointOperator.CompletedNativeC2CentralLegEnergyLimit
import CarrySelfAdjointOperator.CompletedNativeChiralReturnJordanEnergy
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur

/-!
# Exact C2 readout against the signed physical Jordan channels

The C2 central-plus-legs readout and the original positive-minus-negative
physical channel energy have the same radial limit, with their native factor
of four retained. This is a signed identity and supplies no channel
dominance or positivity premise.
-/

namespace CarrySelfAdjointOperator

open scoped BigOperators ComplexConjugate Matrix
open Filter Topology
open ChiralReturn

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

/-- At each fixed order, the original exact-cutoff C2 central-plus-legs
readout approximates one quarter of the signed physical Jordan channel
balance, uniformly in every source vector. The crossed channel terms remain
inside the two physical norms. -/
theorem nativeSourceC2CentralLeg_jordan_channel_error
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Fin (2*n) → ℂ,
      |nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x -
        (‖nativeSourceJordanPositiveState n k x‖^2 -
          ‖nativeSourceJordanNegativeState n k x‖^2)/4| ≤ ε*‖x‖^2 := by
  have hC2 := nativeSourceC2CentralLeg_energy_eventually_uniform n (ε/2)
    (by positivity)
  have hstorage := storage_one_chiralJetInput_eventually_energy_control n (4*ε)
    (by positivity)
  filter_upwards [hC2, hstorage] with k hC2 hstorage
  intro x
  let Q := nativeSourceC2CentralLegReadout n k (nativeSourceC2TailCutoff n k) x
  let P := ‖nativeSourceJordanPositiveState n k x‖^2
  let N := ‖nativeSourceJordanNegativeState n k x‖^2
  let S := (storage k (nativeSourceChiralJetInput n k x) 1).re
  let E := nativeSourceFiniteBoundaryEnergy (2*n) x
  have hchannels : P-N = S := by
    simpa [P, N, nativeSourceJordanPositiveState,
      nativeSourceJordanNegativeState] using
      radialReturnJordanPorts_storage k (2*n) (nativeSourceChiralJetInput n k x)
  have hq : |Q-E/8| ≤ (ε/2)*‖x‖^2 := by
    simpa [Q, E] using hC2 x
  have hs : |2*S-E| ≤ (4*ε)*‖x‖^2 := by
    simpa [S, E] using hstorage x
  have heq : Q-(P-N)/4 = (Q-E/8) - (2*S-E)/8 := by
    rw [hchannels]
    dsimp [Q, S]
    ring
  have htriangle : |Q-(P-N)/4| ≤ |Q-E/8| + |(2*S-E)/8| := by
    rw [heq]
    exact abs_sub _ _
  have hsecond : |(2*S-E)/8| ≤ (ε/2)*‖x‖^2 := by
    have hdiv := div_le_div_of_nonneg_right hs
      (by norm_num : (0:ℝ) ≤ 8)
    have habs : |(2*S-E)/8| = |2*S-E|/8 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
    rw [habs]
    nlinarith
  change |Q-(P-N)/4| ≤ ε*‖x‖^2
  calc
    |Q-(P-N)/4| ≤ |Q-E/8| + |(2*S-E)/8| := htriangle
    _ ≤ (ε/2)*‖x‖^2 + (ε/2)*‖x‖^2 := add_le_add hq hsecond
    _ = ε*‖x‖^2 := by ring

private def jordanSchurCrossQuadratic {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, M i j * (conj (u i) * u j).re

private theorem jordanSchurCrossQuadratic_of_real {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    jordanSchurCrossQuadratic M (fun i => (u i : ℂ)) =
      star u ⬝ᵥ (M *ᵥ u) := by
  simp only [jordanSchurCrossQuadratic, dotProduct, Matrix.mulVec,
    Pi.star_apply, star_trivial, Finset.mul_sum, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem sourceMomentQuadratic_hankel (n : ℕ) (u : Fin n → ℝ) :
    sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 0 n u =
      star u ⬝ᵥ
        (hankelGram canonicalCompletedNativeLogDerivativeMoment n *ᵥ u) := by
  simp [sourceMomentQuadratic, sourceMomentMatrix, hankelGram,
    Matrix.mulVec, dotProduct, Pi.star_apply]

private theorem sourceMomentQuadratic_shiftedHankel (n : ℕ) (u : Fin n → ℝ) :
    sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 n u =
      star u ⬝ᵥ
        (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n *ᵥ u) := by
  simp [sourceMomentQuadratic, sourceMomentMatrix, shiftedHankel,
    Matrix.mulVec, dotProduct, Pi.star_apply]

/-- A real even-parity boundary vector reads exactly the unshifted source
moment quadratic form, with the factor four from the native boundary split. -/
theorem nativeSourceFiniteBoundaryEnergy_evenParity_eq_sourceMomentQuadratic
    (n : ℕ) (u : Fin n → ℝ) :
    nativeSourceFiniteBoundaryEnergy (2*n)
      (nativeSourceBoundaryFromParity n (fun i => (u i : ℂ)) 0) =
        4*sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 0 n u := by
  rw [nativeSourceFiniteBoundaryEnergy_even_split,
    nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity]
  simp only [Pi.zero_apply, mul_zero,
    Complex.zero_re, Finset.sum_const_zero, add_zero]
  rw [primeDepthGeometricMoment_eq_canonical]
  change 4*jordanSchurCrossQuadratic
      (hankelGram canonicalCompletedNativeLogDerivativeMoment n)
      (fun i => (u i : ℂ)) = _
  rw [jordanSchurCrossQuadratic_of_real, ← sourceMomentQuadratic_hankel]

/-- A real odd-parity boundary vector reads exactly the shifted source moment
quadratic form, retaining the same original even/odd split and scale. -/
theorem nativeSourceFiniteBoundaryEnergy_oddParity_eq_sourceMomentQuadratic
    (n : ℕ) (u : Fin n → ℝ) :
    nativeSourceFiniteBoundaryEnergy (2*n)
      (nativeSourceBoundaryFromParity n 0 (fun i => (u i : ℂ))) =
        4*sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 n u := by
  rw [nativeSourceFiniteBoundaryEnergy_even_split,
    nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity]
  simp only [Pi.zero_apply, mul_zero,
    Complex.zero_re, Finset.sum_const_zero, zero_add]
  rw [primeDepthGeometricMoment_eq_canonical]
  change 4*jordanSchurCrossQuadratic
      (shiftedHankel canonicalCompletedNativeLogDerivativeMoment n)
      (fun i => (u i : ℂ)) = _
  rw [jordanSchurCrossQuadratic_of_real, ← sourceMomentQuadratic_shiftedHankel]

/-- The native critical direction for adding one coefficient to an old
unshifted or shifted prefix. The matrix inverse is taken in the original
source moment block; hA is exactly the prefix invertibility/PosDef condition. -/
noncomputable def nativeSourceSchurCriticalCoefficients (s n : ℕ)
    (_hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n).PosDef) :
    Fin (n+1) → ℝ := by
  let A := sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n
  let b := sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n
  letI := _hA.isUnit.invertible
  exact Fin.snoc (-(A⁻¹ *ᵥ b)) 1

/-- Lift the Schur critical direction to the original even/odd boundary
coordinates, selecting the unshifted channel when `b=false` and the shifted
channel when `b=true`. -/
noncomputable def nativeSourceSchurCriticalBoundary (b : Bool) (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      (if b then 1 else 0) n).PosDef) : Fin (2*(n+1)) → ℂ := by
  cases b with
  | false =>
    exact nativeSourceBoundaryFromParity (n+1)
      (fun i =>
        (nativeSourceSchurCriticalCoefficients 0 n (by simpa using hA) i : ℂ)) 0
  | true =>
    exact nativeSourceBoundaryFromParity (n+1) 0
      (fun i =>
        (nativeSourceSchurCriticalCoefficients 1 n (by simpa using hA) i : ℂ))

/-- On the critical direction, the original native boundary energy is four
times the exact next source Schur pivot. This identity is signed and does not
assume that the pivot is positive. -/
theorem nativeSourceFiniteBoundaryEnergy_schurCritical_eq
    (b : Bool) (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      (if b then 1 else 0) n).PosDef) :
    nativeSourceFiniteBoundaryEnergy (2*(n+1))
      (nativeSourceSchurCriticalBoundary b n hA) =
        4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
          (if b then 1 else 0) n := by
  cases b with
  | false =>
    have hcrit := sourceMomentSchur_critical_direction
      canonicalCompletedNativeLogDerivativeMoment 0 n (by simpa using hA)
    change nativeSourceFiniteBoundaryEnergy (2*(n+1))
      (nativeSourceBoundaryFromParity (n+1)
        (fun i => (nativeSourceSchurCriticalCoefficients 0 n (by simpa using hA) i : ℂ)) 0) = _
    rw [nativeSourceFiniteBoundaryEnergy_evenParity_eq_sourceMomentQuadratic]
    simpa [nativeSourceSchurCriticalCoefficients] using congrArg (fun r : ℝ => 4*r) hcrit
  | true =>
    have hcrit := sourceMomentSchur_critical_direction
      canonicalCompletedNativeLogDerivativeMoment 1 n (by simpa using hA)
    change nativeSourceFiniteBoundaryEnergy (2*(n+1))
      (nativeSourceBoundaryFromParity (n+1) 0
        (fun i => (nativeSourceSchurCriticalCoefficients 1 n (by simpa using hA) i : ℂ))) = _
    rw [nativeSourceFiniteBoundaryEnergy_oddParity_eq_sourceMomentQuadratic]
    simpa [nativeSourceSchurCriticalCoefficients] using congrArg (fun r : ℝ => 4*r) hcrit

/-- The actual Jordan-channel signed energy converges on the Schur critical
direction to four times the native source pivot, retaining both physical
channels and their original L2 metric. -/
theorem nativeSourceSchurCritical_physicalJordan_energy_tendsto
    (b : Bool) (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      (if b then 1 else 0) n).PosDef) :
    Tendsto (fun k => 2 *
      (‖nativeSourceJordanPositiveState (n+1) k
          (nativeSourceSchurCriticalBoundary b n hA)‖^2 -
       ‖nativeSourceJordanNegativeState (n+1) k
          (nativeSourceSchurCriticalBoundary b n hA)‖^2)) atTop
      (nhds (4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
        (if b then 1 else 0) n)) := by
  have h := nativeSourceJordan_signed_energy_tendsto (n+1)
    (nativeSourceSchurCriticalBoundary b n hA)
  rw [nativeSourceFiniteBoundaryEnergy_schurCritical_eq] at h
  exact h

/-- The same critical channel limit reads the native Schur remainder after
the original leading coefficient scale. -/
theorem nativeSourceSchurRemainder_eq_scaled_schur_value
    (b : Bool) (n : ℕ) :
    nativeSourceSchurRemainder (if b then 1 else 0) n =
      (completedNativeRealEvenCharacteristicCoefficient 0 / 4) *
        (4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
          (if b then 1 else 0) n) := by
  rw [nativeSourceSchurRemainder_eq]
  ring

/-- After the original leading-coefficient scaling, the Jordan channel energy
on the critical vector converges to the native Schur remainder. -/
theorem nativeSourceSchurRemainder_scaled_physicalJordan_energy_tendsto
    (b : Bool) (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      (if b then 1 else 0) n).PosDef) :
    Tendsto (fun k =>
      (completedNativeRealEvenCharacteristicCoefficient 0 / 4) *
        (2 * (‖nativeSourceJordanPositiveState (n+1) k
            (nativeSourceSchurCriticalBoundary b n hA)‖^2 -
          ‖nativeSourceJordanNegativeState (n+1) k
            (nativeSourceSchurCriticalBoundary b n hA)‖^2))) atTop
      (nhds (nativeSourceSchurRemainder (if b then 1 else 0) n)) := by
  have hlim := nativeSourceSchurCritical_physicalJordan_energy_tendsto b n hA
  have hscaled := hlim.const_mul
    (completedNativeRealEvenCharacteristicCoefficient 0 / 4)
  have heq : (completedNativeRealEvenCharacteristicCoefficient 0 / 4) *
      (4*sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
        (if b then 1 else 0) n) = nativeSourceSchurRemainder (if b then 1 else 0) n := by
    rw [nativeSourceSchurRemainder_eq]
    ring
  rw [← heq]
  exact hscaled

end
end CarrySelfAdjointOperator

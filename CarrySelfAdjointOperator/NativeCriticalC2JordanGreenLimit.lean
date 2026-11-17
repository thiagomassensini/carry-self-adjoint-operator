import CarrySelfAdjointOperator.CompletedNativeChiralJordanSchurCrosswalk
import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport
import CarrySelfAdjointOperator.NativeSchurEulerBalance

/-! A single theorem composes the existing C2, physical Jordan, Schur, and
Green readouts on the same critical vector. The C2 index is `n+1` because the
critical vector extends an old Hankel prefix of size `n` to size `n+1`.
Nothing here asserts a sign unless an enlarged positive prefix is supplied. -/
namespace CarrySelfAdjointOperator

open Filter Topology MeasureTheory Set Polynomial XiThetaCosine
open ChiralReturn
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem nativeCriticalC2Readout_tendsto_pivot
    (b : Bool) (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      (if b then 1 else 0) n).PosDef) :
    Tendsto
      (fun k => nativeSourceC2CentralLegReadout (n+1) k
        (nativeSourceC2TailCutoff (n+1) k)
        (nativeSourceSchurCriticalBoundary b n hA))
      atTop
      (nhds (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
        (if b then 1 else 0) n / 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let x := nativeSourceSchurCriticalBoundary b n hA
  let η := ε / (‖x‖^2 + 1)
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos hε (by positivity)
  have hsmall : η * ‖x‖^2 < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ‖x‖^2 + 1)).2
    nlinarith [sq_nonneg (‖x‖ : ℝ), hε]
  filter_upwards
    [nativeSourceC2CentralLeg_energy_eventually_uniform (n+1) η hη]
    with k hk
  have h := hk x
  have hcenter :
      nativeSourceFiniteBoundaryEnergy (2*(n+1)) x / 8 =
        sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
          (if b then 1 else 0) n / 2 := by
    rw [nativeSourceFiniteBoundaryEnergy_schurCritical_eq b n hA]
    ring
  rw [hcenter] at h
  have hdist :
      dist
        (nativeSourceC2CentralLegReadout (n+1) k
          (nativeSourceC2TailCutoff (n+1) k) x)
        (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
          (if b then 1 else 0) n / 2) ≤ η * ‖x‖^2 := by
    simpa [Real.dist_eq] using h
  exact lt_of_le_of_lt hdist hsmall

/-- On the existing Schur critical direction, the C2 central-plus-legs
readout, the original scaled signed Jordan channels, the Schur remainder,
and the exact Green integral all read the same scalar. The old prefix must be
positive definite to define the critical direction and obtain its C2/Jordan
limits; the identity itself supplies no sign. -/
theorem nativeCriticalC2JordanGreenLimit
    (b : Bool) (n : ℕ)
    (hA : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      (if b then 1 else 0) n).PosDef) :
    Tendsto
      (fun k => nativeSourceC2CentralLegReadout (n+1) k
        (nativeSourceC2TailCutoff (n+1) k)
        (nativeSourceSchurCriticalBoundary b n hA))
      atTop
      (nhds (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
        (if b then 1 else 0) n / 2)) ∧
    Tendsto
      (fun k =>
        (completedNativeRealEvenCharacteristicCoefficient 0 / 4) *
          (2 * (‖nativeSourceJordanPositiveState (n+1) k
              (nativeSourceSchurCriticalBoundary b n hA)‖^2 -
            ‖nativeSourceJordanNegativeState (n+1) k
              (nativeSourceSchurCriticalBoundary b n hA)‖^2)))
      atTop
      (nhds (nativeSourceSchurRemainder (if b then 1 else 0) n)) ∧
    nativeSourceSchurRemainder (if b then 1 else 0) n =
      2 * completedNativeRealEvenCharacteristicCoefficient 0 *
        (sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment
          (if b then 1 else 0) n / 2) ∧
    nativeSourceSchurRemainder (if b then 1 else 0) n =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial
          (nativeSchurThetaPolynomial (if b then 1 else 0) n)).eval u *
            thetaTail u := by
  refine ⟨nativeCriticalC2Readout_tendsto_pivot b n hA, ?_, ?_, ?_⟩
  · exact nativeSourceSchurRemainder_scaled_physicalJordan_energy_tendsto b n hA
  · rw [nativeSourceSchurRemainder_eq]
    ring
  · exact nativeSourceSchurRemainder_eq_thetaGreen_integral
      (if b then 1 else 0) n

private theorem nativeSource_nextPrefix_posDef_oldPrefix_posDef
    (s n : ℕ)
    (hNext : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      s (n+1)).PosDef) :
    (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n).PosDef := by
  exact Matrix.PosDef.submatrix hNext (Fin.castSucc_injective n)

/-- A positive enlarged canonical Hankel prefix gives a positive Schur pivot
and therefore a positive complete theta-Green integral. This conditional
form is designed for finite certificates such as H6/K6; it assumes no
all-order positivity. -/
theorem nativeCriticalGreenPositive_of_extendedPrefix_posDef
    (s n : ℕ)
    (hNext : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      s (n+1)).PosDef) :
    0 < ∫ u in Ioi (0 : ℝ),
      (nativeThetaGreenPolynomial (nativeSchurThetaPolynomial s n)).eval u *
        thetaTail u := by
  have hA := nativeSource_nextPrefix_posDef_oldPrefix_posDef s n hNext
  have hp := (sourceMomentMatrix_succ_posDef_iff
    canonicalCompletedNativeLogDerivativeMoment s n hA).mp hNext
  have hc0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  rw [← nativeSourceSchurRemainder_eq_thetaGreen_integral s n,
    nativeSourceSchurRemainder_eq]
  exact mul_pos hc0 hp

/-- Under a positive enlarged even prefix, the complete signed Euler integral
is strictly positive. This is the finite-certificate route for the even
sector, which has no auxiliary Euler square. -/
theorem nativeSchurEuler_even_integral_pos_of_extendedPrefix_posDef
    (n : ℕ)
    (hNext : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      0 (n+1)).PosDef) :
    0 < nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 0 n) := by
  have hA := nativeSource_nextPrefix_posDef_oldPrefix_posDef 0 n hNext
  have hp := (sourceMomentMatrix_succ_posDef_iff
    canonicalCompletedNativeLogDerivativeMoment 0 n hA).mp hNext
  have hc0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hR : 0 < nativeSourceSchurRemainder 0 n := by
    rw [nativeSourceSchurRemainder_eq]
    exact mul_pos hc0 hp
  rw [← nativeSchurEuler_even_balance n hA.isUnit]
  exact mul_pos (by positivity) hR

/-- Under a positive enlarged odd prefix, the exact odd Euler compensation
inequality holds, including its existing nonnegative readout square. -/
theorem nativeSchurEuler_odd_compensation_of_extendedPrefix_posDef
    (n : ℕ)
    (hNext : (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment
      1 (n+1)).PosDef) :
    -2 * completedNativeRealEvenCharacteristicCoefficient 0 *
        (nativeSchurCriticalReadout 1 n)^2 <
      nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 1 n) := by
  have hA := nativeSource_nextPrefix_posDef_oldPrefix_posDef 1 n hNext
  have hp := (sourceMomentMatrix_succ_posDef_iff
    canonicalCompletedNativeLogDerivativeMoment 1 n hA).mp hNext
  have hc0 : 0 < completedNativeRealEvenCharacteristicCoefficient 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  have hR : 0 < nativeSourceSchurRemainder 1 n := by
    rw [nativeSourceSchurRemainder_eq]
    exact mul_pos hc0 hp
  have hsum : 0 <
      nativeXiPolynomialIntegral (nativeSchurEulerPolynomial 1 n) +
        2 * completedNativeRealEvenCharacteristicCoefficient 0 *
          (nativeSchurCriticalReadout 1 n)^2 := by
    rw [← nativeSchurEuler_odd_balance n hA.isUnit]
    exact mul_pos (by positivity) hR
  linarith

end
end CarrySelfAdjointOperator

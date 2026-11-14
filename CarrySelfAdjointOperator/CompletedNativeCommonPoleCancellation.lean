import CarrySelfAdjointOperator.CommonPoleHankelCancellation
import CarrySelfAdjointOperator.CompletedOperatorCharacteristic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Common-pole cancellation in logarithmic response germs

This module isolates the factor `s - 1` in the original C2 camera
factorization.  Its rank-one odd Taylor channel is handled algebraically in
`CommonPoleHankelCancellation`; the remaining source is kept independent.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Half of the negative logarithmic derivative in the height variable. -/
def halfLogResponse (X : ℂ → ℂ) (z : ℂ) : ℂ :=
  -deriv X z / (2 * X z)

/-- The logarithmic response of a product is the sum of the two responses,
where both factors are nonzero at the point. -/
theorem halfLogResponse_mul (X U : ℂ → ℂ) (z : ℂ)
    (hX : DifferentiableAt ℂ X z) (hU : DifferentiableAt ℂ U z)
    (hX0 : X z ≠ 0) (hU0 : U z ≠ 0) :
    halfLogResponse (fun w => X w * U w) z =
      halfLogResponse X z + halfLogResponse U z := by
  have hd : deriv (fun w => X w * U w) z =
      deriv X z * U z + X z * deriv U z := by
    exact deriv_mul hX hU
  unfold halfLogResponse
  rw [hd]
  field_simp [hX0, hU0]
  ring

/-- The common factor cancels from a quotient before taking its logarithmic
response.  This version only differentiates the reduced quotient `U/V`; it
therefore applies even where an unreduced common factor vanishes. -/
theorem halfLogResponse_div_reduced (U V : ℂ → ℂ) (z : ℂ)
    (hU : DifferentiableAt ℂ U z) (hV : DifferentiableAt ℂ V z)
    (hU0 : U z ≠ 0) (hV0 : V z ≠ 0) :
    halfLogResponse (fun w => U w / V w) z =
      halfLogResponse U z - halfLogResponse V z := by
  have hd : deriv (fun w => U w / V w) z =
      (deriv U z * V z - U z * deriv V z) / V z ^ 2 := by
    exact deriv_fun_div hU hV hV0
  unfold halfLogResponse
  rw [hd]
  field_simp [hU0, hV0]
  ring

/-- The unreduced quotient and its reduced form agree as germs wherever the
common factor is nonzero. -/
theorem commonFactor_quotient_eventuallyEq
    (X U V : ℂ → ℂ) (z : ℂ)
    (hX : DifferentiableAt ℂ X z) (hV : DifferentiableAt ℂ V z)
    (hX0 : X z ≠ 0) (hV0 : V z ≠ 0) :
    (fun w => X w * U w / (X w * V w)) =ᶠ[nhds z]
      (fun w => U w / V w) := by
  filter_upwards
    [hX.continuousAt.eventually_ne hX0, hV.continuousAt.eventually_ne hV0]
    with w hXw hVw
  field_simp [hXw, hVw]

/-- The common linear factor in centered height coordinates, `s(z)-1`. -/
def commonPoleHeightFactor (z : ℂ) : ℂ :=
  operatorHeightParameter z - 1

/-- The linear factor is `-(1-2iz)/2`. -/
theorem commonPoleHeightFactor_eq (z : ℂ) :
    commonPoleHeightFactor z = (-1 / 2 : ℂ) * (1 - 2 * Complex.I * z) := by
  simp [commonPoleHeightFactor, operatorHeightParameter]
  ring

/-- Its half-logarithmic response has the exact simple-pole formula. -/
theorem commonPoleHeightFactor_response (z : ℂ) :
    halfLogResponse commonPoleHeightFactor z =
      Complex.I / (1 - 2 * Complex.I * z) := by
  have hd : deriv commonPoleHeightFactor z = Complex.I := by
    unfold commonPoleHeightFactor operatorHeightParameter
    simp
  unfold halfLogResponse
  rw [hd, commonPoleHeightFactor_eq]
  field_simp

/-- Odd part of the common-pole response. -/
def commonPoleOddResponse (z : ℂ) : ℂ :=
  (halfLogResponse commonPoleHeightFactor z -
    halfLogResponse commonPoleHeightFactor (-z)) / 2

/-- Exact rational expression for the odd part of the shared pole. -/
theorem commonPoleOddResponse_eq (z : ℂ)
    (hz : 1 + 4 * z ^ 2 ≠ 0) :
    commonPoleOddResponse z = -2 * z / (1 + 4 * z ^ 2) := by
  have hsq : (2 * Complex.I * z) ^ 2 = -4 * z ^ 2 := by
    calc
      (2 * Complex.I * z) ^ 2 = 4 * Complex.I ^ 2 * z ^ 2 := by ring
      _ = -4 * z ^ 2 := by rw [Complex.I_sq]; ring
  have hfactor : 1 + 4 * z ^ 2 =
      (1 - 2 * Complex.I * z) * (1 + 2 * Complex.I * z) := by
    calc
      1 + 4 * z ^ 2 = 1 - (2 * Complex.I * z) ^ 2 := by rw [hsq]; ring
      _ = (1 - 2 * Complex.I * z) * (1 + 2 * Complex.I * z) := by ring
  have hminus : 1 - 2 * Complex.I * z ≠ 0 := by
    intro h
    apply hz
    rw [hfactor, h]
    simp
  have hplus : 1 + 2 * Complex.I * z ≠ 0 := by
    intro h
    apply hz
    rw [hfactor, h]
    simp
  have hneg : 1 - 2 * Complex.I * (-z) ≠ 0 := by
    simpa using hplus
  have hnegEq : 1 - 2 * Complex.I * (-z) = 1 + 2 * Complex.I * z := by ring
  have hnum :
      Complex.I * (1 + 2 * Complex.I * z) -
        Complex.I * (1 - 2 * Complex.I * z) = -4 * z := by
    calc
      Complex.I * (1 + 2 * Complex.I * z) -
          Complex.I * (1 - 2 * Complex.I * z) =
        4 * Complex.I ^ 2 * z := by ring
      _ = -4 * z := by rw [Complex.I_sq]; ring
  rw [commonPoleOddResponse, commonPoleHeightFactor_response z,
    commonPoleHeightFactor_response (-z), hnegEq]
  rw [div_sub_div _ _ hminus hplus]
  have hnum' :
      Complex.I * (1 + 2 * Complex.I * z) -
        (1 - 2 * Complex.I * z) * Complex.I = -4 * z := by
    calc
      Complex.I * (1 + 2 * Complex.I * z) -
          (1 - 2 * Complex.I * z) * Complex.I =
        Complex.I * (1 + 2 * Complex.I * z) -
          Complex.I * (1 - 2 * Complex.I * z) := by ring
      _ = -4 * z := hnum
  rw [hnum', hfactor]
  have hprod :
      (1 - 2 * Complex.I * z) * (1 + 2 * Complex.I * z) ≠ 0 :=
    mul_ne_zero hminus hplus
  field_simp [hz, hprod]
  ring

/-- The divided-difference kernel identity, multiplied through by both
original denominators.  This remains meaningful on the diagonal `w = z`. -/
theorem commonPoleOddResponse_dividedDifference_mul
    (z w : ℂ) (hz : 1 + 4 * z ^ 2 ≠ 0) (hw : 1 + 4 * w ^ 2 ≠ 0) :
    (commonPoleOddResponse w - commonPoleOddResponse z) *
        ((1 + 4 * z ^ 2) * (1 + 4 * w ^ 2)) =
      (w - z) * (-2 + 8 * z * w) := by
  have hz' : 1 + z ^ 2 * 4 ≠ 0 := by
    simpa [mul_comm] using hz
  have hw' : 1 + w ^ 2 * 4 ≠ 0 := by
    simpa [mul_comm] using hw
  rw [commonPoleOddResponse_eq w hw, commonPoleOddResponse_eq z hz]
  field_simp [hz, hz', hw, hw']
  ring


/-- Off the diagonal, the multiplied identity yields the ordinary divided
difference. On the diagonal use the multiplied identity, which never divides
by `w-z`. -/
theorem commonPoleOddResponse_dividedDifference
    (z w : ℂ) (hz : 1 + 4 * z ^ 2 ≠ 0) (hw : 1 + 4 * w ^ 2 ≠ 0)
    (hzw : w ≠ z) :
    (commonPoleOddResponse w - commonPoleOddResponse z) / (w - z) =
      (-2 + 8 * z * w) / ((1 + 4 * z ^ 2) * (1 + 4 * w ^ 2)) := by
  apply (div_eq_div_iff (sub_ne_zero.mpr hzw)
    (mul_ne_zero hz hw)).2
  have h := commonPoleOddResponse_dividedDifference_mul z w hz hw
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- The divided-difference numerator is the sum of two separable channels:
a constant and a product of one `z`-factor with one `w`-factor. -/
theorem commonPoleOddKernelNumerator_separable (z w : ℂ) :
    -2 + 8 * z * w = (-2 : ℂ) * 1 + (8 * z) * w := by
  ring

/-- Coefficients of the formal geometric expansion, specified by its
second-order recurrence. -/
def commonPoleOddSeriesCoefficient : ℕ → ℝ
  | 0 => 0
  | 1 => -2
  | n + 2 => -4 * commonPoleOddSeriesCoefficient n

theorem commonPoleOddSeriesCoefficient_recurrence (n : ℕ) :
    commonPoleOddSeriesCoefficient (n + 2) =
      -4 * commonPoleOddSeriesCoefficient n := by
  rfl

theorem commonPoleOddSeriesCoefficient_odd (j : ℕ) :
    commonPoleOddSeriesCoefficient (2 * j + 1) =
      commonPoleOddCoefficient j := by
  induction j with
  | zero => simp [commonPoleOddSeriesCoefficient, commonPoleOddCoefficient]
  | succ j ih =>
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]
      rw [commonPoleOddSeriesCoefficient, ih]
      simp [commonPoleOddCoefficient, pow_succ]
      ring

def commonPoleOddFormalSeries : PowerSeries ℝ :=
  PowerSeries.mk commonPoleOddSeriesCoefficient

def commonPoleOddFormalDenominator : PowerSeries ℝ :=
  1 + PowerSeries.C (4 : ℝ) * PowerSeries.X ^ 2

@[simp] theorem commonPoleOddFormalSeries_coeff (n : ℕ) :
    PowerSeries.coeff n commonPoleOddFormalSeries =
      commonPoleOddSeriesCoefficient n := by
  rw [commonPoleOddFormalSeries, PowerSeries.coeff_mk]

/-- The coefficient sequence is exactly the formal solution of the rational
identity `(1+4X^2) R(X) = -2X`, so its odd coefficients are the claimed
`-2*(-4)^j`. -/
theorem commonPoleOddFormalSeries_rational_identity :
    commonPoleOddFormalDenominator * commonPoleOddFormalSeries =
      PowerSeries.C (-2 : ℝ) * PowerSeries.X := by
  ext n
  have hdecomp :
      commonPoleOddFormalDenominator * commonPoleOddFormalSeries =
        commonPoleOddFormalSeries + PowerSeries.C (4 : ℝ) *
          (PowerSeries.X ^ 2 * commonPoleOddFormalSeries) := by
    unfold commonPoleOddFormalDenominator
    calc
      (1 + PowerSeries.C (4 : ℝ) * PowerSeries.X ^ 2) *
          commonPoleOddFormalSeries =
        1 * commonPoleOddFormalSeries +
          (PowerSeries.C (4 : ℝ) * PowerSeries.X ^ 2) *
            commonPoleOddFormalSeries := by rw [add_mul]
      _ = commonPoleOddFormalSeries + PowerSeries.C (4 : ℝ) *
          (PowerSeries.X ^ 2 * commonPoleOddFormalSeries) := by
            simp [mul_assoc]
  rw [hdecomp, (PowerSeries.coeff n).map_add, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
      simp [commonPoleOddFormalSeries, commonPoleOddSeriesCoefficient,
        PowerSeries.coeff_X_pow_mul']
  | succ n =>
      cases n with
      | zero =>
          simp [commonPoleOddFormalSeries, commonPoleOddSeriesCoefficient,
            PowerSeries.coeff_X_pow_mul']
      | succ n =>
          have hshift :
              PowerSeries.coeff (n + 1 + 1)
                  (PowerSeries.X ^ 2 * commonPoleOddFormalSeries) =
                PowerSeries.coeff n commonPoleOddFormalSeries := by
            rw [show n + 1 + 1 = n + 2 by omega]
            exact PowerSeries.coeff_X_pow_mul commonPoleOddFormalSeries 2 n
          have hidx : n + 1 + 1 = n + 2 := by omega
          have hrhs : PowerSeries.coeff (n + 2)
                (PowerSeries.C (-2 : ℝ) * PowerSeries.X) = 0 := by
            have heq : PowerSeries.C (-2 : ℝ) * PowerSeries.X =
                PowerSeries.C (-2 : ℝ) * PowerSeries.X ^ 1 := by simp
            rw [heq, PowerSeries.coeff_C_mul_X_pow]
            simp
          rw [hidx, hshift, commonPoleOddFormalSeries_coeff,
            commonPoleOddFormalSeries_coeff,
            commonPoleOddSeriesCoefficient_recurrence, hrhs]
          ring

/-- Since the denominator has constant coefficient one, the displayed series
is the unique formal solution of the rational equation
`(1+4X^2) R(X) = -2X`. -/
theorem commonPoleOddFormalSeries_unique_rational_solution
    (S : PowerSeries ℝ)
    (hS : commonPoleOddFormalDenominator * S =
      PowerSeries.C (-2 : ℝ) * PowerSeries.X) :
    S = commonPoleOddFormalSeries := by
  have hunit : IsUnit commonPoleOddFormalDenominator := by
    apply (PowerSeries.isUnit_iff_constantCoeff).2
    simp [commonPoleOddFormalDenominator]
  apply hunit.mul_left_cancel
  calc
    commonPoleOddFormalDenominator * S =
        PowerSeries.C (-2 : ℝ) * PowerSeries.X := hS
    _ = commonPoleOddFormalDenominator * commonPoleOddFormalSeries :=
      commonPoleOddFormalSeries_rational_identity.symm

end

end CarrySelfAdjointOperator

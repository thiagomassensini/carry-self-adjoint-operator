import CarrySelfAdjointOperator.LocalHadamardMomentBridge
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Formal-power-series interpretation of the local Hadamard recurrence

The earlier local coefficients are extracted by differentiating the
completed-native characteristic. This module verifies that the resulting
division-free recursive coefficients really give the formal logarithmic
derivative of their own deflated Taylor series. No zero table, positivity,
or factorization over the complete zero set is involved.
-/

namespace CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section

def localDeflatedFormalSeries (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk a

def localLogResponseFormalSeries (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (localLogDerivativeCoefficients a)

/-- The coefficient recurrence is exactly the formal product
(A'/A)*A=A' on the nose, without an analytic convergence assumption. -/
theorem localLogResponseFormalSeries_mul_deflated
    (a : ℕ → ℂ) (ha : a 0 ≠ 0) :
    localLogResponseFormalSeries a * localDeflatedFormalSeries a =
      PowerSeries.derivative ℂ (localDeflatedFormalSeries a) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [localDeflatedFormalSeries, localLogResponseFormalSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self]
  have hrec := localLogDerivativeCoefficients_recurrence a ha n
  rw [Finset.sum_attach (Finset.range n)
    (fun k : ℕ => localLogDerivativeCoefficients a k * a (n - k))] at hrec
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm, add_comm] using hrec

/-- Formal logarithmic derivative, with the inverse justified by the
nonzero constant coefficient of the deflated series. -/
theorem localLogResponseFormalSeries_eq_formal_log_derivative
    (a : ℕ → ℂ) (ha : a 0 ≠ 0) :
    localLogResponseFormalSeries a =
      PowerSeries.derivative ℂ (localDeflatedFormalSeries a) *
        (localDeflatedFormalSeries a)⁻¹ := by
  have hconst :
      PowerSeries.constantCoeff (localDeflatedFormalSeries a) ≠ 0 := by
    simpa [localDeflatedFormalSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      using ha
  have hprod :=
    localLogResponseFormalSeries_mul_deflated a ha
  calc
    localLogResponseFormalSeries a =
        localLogResponseFormalSeries a *
          (localDeflatedFormalSeries a * (localDeflatedFormalSeries a)⁻¹) := by
            simp only [PowerSeries.mul_inv_cancel _ hconst, mul_one]
    _ = (localLogResponseFormalSeries a * localDeflatedFormalSeries a) *
          (localDeflatedFormalSeries a)⁻¹ := by ring
    _ = PowerSeries.derivative ℂ (localDeflatedFormalSeries a) *
          (localDeflatedFormalSeries a)⁻¹ := by rw [hprod]

/-- The local characteristic itself provides the normalization a0=1
at every simple zero; in particular the formal logarithmic
response is uniquely determined by the differentiated completed germ. -/
theorem nativeLocalLogResponseFormalSeries_mul
    (gamma : ℝ)
    (hsimple :
      iteratedDeriv 1 completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    localLogResponseFormalSeries (nativeLocalDeflatedCoefficient gamma) *
        localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma) =
      PowerSeries.derivative ℂ
        (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma)) := by
  apply localLogResponseFormalSeries_mul_deflated
  rw [nativeLocalDeflatedCoefficient_zero gamma hsimple]
  exact one_ne_zero

/-- The historical S_m is literally the signed coefficient of the
formal logarithmic derivative of the native deflated Taylor series.
This is the coefficient-level bridge to the series A'/A. -/
theorem nativeLocalHadamardMoment_eq_formal_log_derivative_coeff
    (gamma : ℝ)
    (hsimple :
      iteratedDeriv 1 completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0)
    (m : ℕ) (hm : 0 < m) :
    nativeLocalHadamardMoment gamma m =
      (-1 : ℂ)^(m - 1) *
        PowerSeries.coeff (m - 1)
          (PowerSeries.derivative ℂ
              (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma)) *
            (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma))⁻¹) := by
  unfold nativeLocalHadamardMoment localHadamardMoment
  simp only [Nat.ne_of_gt hm, if_false]
  rw [← localLogResponseFormalSeries_eq_formal_log_derivative
      (nativeLocalDeflatedCoefficient gamma)]
  · simp [localLogResponseFormalSeries]
  · rw [nativeLocalDeflatedCoefficient_zero gamma hsimple]
    exact one_ne_zero

/-- At any simple real zero, S6 is the (negative) fifth coefficient
of the exact formal logarithmic derivative of the deflated F germ. -/
theorem nativeLocalS6_eq_formal_log_derivative_coeff
    (gamma : ℝ)
    (hsimple :
      iteratedDeriv 1 completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    nativeLocalHadamardMoment gamma 6 =
      -(PowerSeries.coeff 5
          (PowerSeries.derivative ℂ
              (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma)) *
            (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma))⁻¹)) := by
  simpa only [show (-1 : ℂ)^5 = -1 by norm_num, neg_one_mul] using
    nativeLocalHadamardMoment_eq_formal_log_derivative_coeff
      gamma hsimple 6 (by norm_num)

/-- At any simple real zero, S7 is the sixth formal log-derivative
coefficient of the same completed characteristic. -/
theorem nativeLocalS7_eq_formal_log_derivative_coeff
    (gamma : ℝ)
    (hsimple :
      iteratedDeriv 1 completedNativeOperatorCharacteristic (gamma : ℂ) ≠ 0) :
    nativeLocalHadamardMoment gamma 7 =
      PowerSeries.coeff 6
          (PowerSeries.derivative ℂ
              (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma)) *
            (localDeflatedFormalSeries (nativeLocalDeflatedCoefficient gamma))⁻¹) := by
  simpa only [show (-1 : ℂ)^6 = 1 by norm_num, one_mul] using
    nativeLocalHadamardMoment_eq_formal_log_derivative_coeff
      gamma hsimple 7 (by norm_num)

end
end CarrySelfAdjointOperator

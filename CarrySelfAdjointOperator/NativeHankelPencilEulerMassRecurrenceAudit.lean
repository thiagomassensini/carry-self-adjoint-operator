import CarrySelfAdjointOperator.NativeHankelPencilEulerOrderTwo
import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport

/-! Exact audit of what the signed Euler balances imply when comparing the
order-two gates with the next order. The mass increments are retained; their
first required comparison reduces exactly to the as-yet-unproved order-three
remainder sign. -/
namespace CarrySelfAdjointOperator

open MeasureTheory Set Polynomial XiThetaCosine
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "m" => canonicalCompletedNativeLogDerivativeMoment
local notation "c₀" => completedNativeRealEvenCharacteristicCoefficient 0

def nativeSchurEulerEvenMassDeficit (n : ℕ) : ℝ :=
  nativeThetaNegativeMass (nativeSchurEulerPolynomial 0 n) -
    nativeThetaPositiveMass (nativeSchurEulerPolynomial 0 n)

def nativeSchurEulerOddMassDeficit (n : ℕ) : ℝ :=
  nativeThetaNegativeMass (nativeSchurEulerPolynomial 1 n) -
    nativeThetaPositiveMass (nativeSchurEulerPolynomial 1 n) -
      2*c₀*(nativeSchurCriticalReadout 1 n)^2

/-- The spatial Euler derivative has zero value and zero derivative at the
center, since each Schur theta polynomial has no terms below degree two. -/
theorem nativeSchurEulerPolynomial_center_traces (s n : ℕ) :
    (nativeSchurEulerPolynomial s n).eval 0 = 0 ∧
      (nativeSchurEulerPolynomial s n).derivative.eval 0 = 0 := by
  obtain ⟨_,h1⟩ := nativeSchurThetaPolynomial_center_traces s n
  constructor
  · simp [nativeSchurEulerPolynomial]
  · simp [nativeSchurEulerPolynomial, Polynomial.derivative_mul, h1]

/-- Green transport for the Euler density, with the central terms shown to
vanish exactly. The equality is for the signed integral only. -/
theorem nativeSchurEulerPolynomial_integral_eq_green (s n : ℕ) :
    nativeXiPolynomialIntegral (nativeSchurEulerPolynomial s n) =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (nativeSchurEulerPolynomial s n)).eval u *
          thetaTail u := by
  rw [nativeXiPolynomialIntegral_eq_thetaGreen_integral]
  obtain ⟨h0,h1⟩ := nativeSchurEulerPolynomial_center_traces s n
  simp [h0,h1]

/-- The even signed-mass deficit is exactly the negative Euler balance. -/
theorem nativeSchurEuler_even_massDeficit_eq_neg_remainder (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 0 n)) :
    nativeSchurEulerEvenMassDeficit n =
      -((4*n+2 : ℕ) : ℝ)*nativeSourceSchurRemainder 0 n := by
  have h := nativeSchurEuler_even_balance n hA
  rw [nativeXiPolynomialIntegral_eq_masses] at h
  unfold nativeSchurEulerEvenMassDeficit
  linarith [h]

/-- The odd deficit subtracts the surviving source square. It is likewise
the negative of the full odd Euler balance. -/
theorem nativeSchurEuler_odd_massDeficit_eq_neg_remainder (n : ℕ)
    (hA : IsUnit (sourceMomentMatrix m 1 n)) :
    nativeSchurEulerOddMassDeficit n =
      -((4*n+4 : ℕ) : ℝ)*nativeSourceSchurRemainder 1 n := by
  have h := nativeSchurEuler_odd_mass_balance n hA
  unfold nativeSchurEulerOddMassDeficit
  linarith [h]

/-- The order-three prefixes are invertible from the source-first order-two
determinant certificates. This assumes no order-four positivity. -/
theorem nativeSourceEuler_even_prefix_three_isUnit :
    IsUnit (sourceMomentMatrix m 0 3) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  change nativeSourcePrefixDet 0 3 ≠ 0
  exact (ne_of_gt nativeSourceEuler_even_three_prefixDet_pos)

theorem nativeSourceEuler_odd_prefix_three_isUnit :
    IsUnit (sourceMomentMatrix m 1 3) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  change nativeSourcePrefixDet 1 3 ≠ 0
  exact (ne_of_gt nativeSourceEuler_odd_three_prefixDet_pos)

/-- Exact change in the even deficit from order two to order three. -/
theorem nativeSchurEuler_even_massDeficit_increment_two_to_three :
    nativeSchurEulerEvenMassDeficit 3 - nativeSchurEulerEvenMassDeficit 2 =
      (10 : ℝ)*nativeSourceSchurRemainder 0 2 -
        (14 : ℝ)*nativeSourceSchurRemainder 0 3 := by
  rw [nativeSchurEuler_even_massDeficit_eq_neg_remainder 3
        nativeSourceEuler_even_prefix_three_isUnit,
      nativeSchurEuler_even_massDeficit_eq_neg_remainder 2
        nativeSourceEuler_even_prefix_two_isUnit]
  ring

/-- Exact change in the odd deficit from order two to order three. The
increment of the readout square is already included in the deficit. -/
theorem nativeSchurEuler_odd_massDeficit_increment_two_to_three :
    nativeSchurEulerOddMassDeficit 3 - nativeSchurEulerOddMassDeficit 2 =
      (12 : ℝ)*nativeSourceSchurRemainder 1 2 -
        (16 : ℝ)*nativeSourceSchurRemainder 1 3 := by
  rw [nativeSchurEuler_odd_massDeficit_eq_neg_remainder 3
        nativeSourceEuler_odd_prefix_three_isUnit,
      nativeSchurEuler_odd_massDeficit_eq_neg_remainder 2
        nativeSourceEuler_odd_prefix_two_isUnit]
  ring

/-- The first even mass-increment comparison that would propagate the known
order-two gate is equivalent to positivity of the new order-three Euler
remainder. Thus the signed balance alone does not advance the induction. -/
theorem nativeSchurEuler_even_increment_gate_iff_orderThree_remainder_pos :
    (nativeSchurEulerEvenMassDeficit 3 - nativeSchurEulerEvenMassDeficit 2 <
      (10 : ℝ)*nativeSourceSchurRemainder 0 2) ↔
      0 < nativeSourceSchurRemainder 0 3 := by
  have h := nativeSchurEuler_even_massDeficit_increment_two_to_three
  rw [h]
  constructor <;> intro hh <;> nlinarith

/-- The first odd mass-increment comparison retains the increment of the
cofactor square. The exact signed balances reduce it to the order-three
remainder sign, without establishing that sign. -/
theorem nativeSchurEuler_odd_increment_gate_iff_orderThree_remainder_pos :
    (nativeSchurEulerOddMassDeficit 3 - nativeSchurEulerOddMassDeficit 2 <
      (12 : ℝ)*nativeSourceSchurRemainder 1 2) ↔
      0 < nativeSourceSchurRemainder 1 3 := by
  have h := nativeSchurEuler_odd_massDeficit_increment_two_to_three
  rw [h]
  constructor <;> intro hh <;> nlinarith

end
end CarrySelfAdjointOperator

#print axioms CarrySelfAdjointOperator.nativeSchurEulerPolynomial_integral_eq_green
#print axioms CarrySelfAdjointOperator.nativeSchurEuler_even_massDeficit_eq_neg_remainder
#print axioms CarrySelfAdjointOperator.nativeSchurEuler_odd_massDeficit_eq_neg_remainder
#print axioms CarrySelfAdjointOperator.nativeSchurEuler_even_massDeficit_increment_two_to_three
#print axioms CarrySelfAdjointOperator.nativeSchurEuler_odd_massDeficit_increment_two_to_three
#print axioms CarrySelfAdjointOperator.nativeSchurEuler_even_increment_gate_iff_orderThree_remainder_pos
#print axioms CarrySelfAdjointOperator.nativeSchurEuler_odd_increment_gate_iff_orderThree_remainder_pos

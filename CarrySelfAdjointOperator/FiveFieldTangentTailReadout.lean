import CarrySelfAdjointOperator.FiveFieldTangentReconstruction
import CarrySelfAdjointOperator.FiveFieldChiralEndpointTail

/-!
# Exponential tails through the concrete tangent readout

The functional here is the explicit `scalar_from_H` reconstruction, not an
abstract functional supplied as a hypothesis. Integrability of finite
polynomial densities is proved. Identifying a reconstructed tangent with an
actual amplitude derivative remains a separate geometric obligation.
-/

namespace NativeCarryFiveFieldCapstone

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

local instance : ContinuousENorm (Fin 3 → TwoByTwo) :=
  inferInstanceAs (ContinuousENorm (Fin 3 → Fin 2 → Fin 2 → ℂ))

def twoJumpScalarFromMomentsContinuous (κ t1 t2 : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ) : (Fin 3 → TwoByTwo) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (twoJumpScalarFromMoments κ t1 t2 A u)

/-- Passing the integral through the full reconstruction pipeline. -/
theorem twoJumpScalarFromMoments_integral (κ t1 t2 : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (x : ℝ) (H : ℝ → Fin 3 → TwoByTwo) (hH : IntegrableOn H (Ioi x)) :
    (∫ t in Ioi x, twoJumpScalarFromMoments κ t1 t2 A u (H t)) =
      twoJumpScalarFromMoments κ t1 t2 A u (∫ t in Ioi x, H t) := by
  exact (twoJumpScalarFromMomentsContinuous κ t1 t2 A u).integral_comp_comm hH

/-- Polynomial Cauchy-moment data with explicit finite matrix coefficients. -/
def twoJumpPolynomialMomentDensity (s : Finset ℕ)
    (P : ℕ → Fin 3 → TwoByTwo) (t : ℝ) : Fin 3 → TwoByTwo :=
  ∑ m ∈ s, ((Real.exp (-t) : ℂ) * (t : ℂ) ^ m) • P m

set_option maxHeartbeats 800000 in
theorem twoJumpPolynomialMomentDensity_integrable (x : ℝ) (s : Finset ℕ)
    (P : ℕ → Fin 3 → TwoByTwo) :
    IntegrableOn (twoJumpPolynomialMomentDensity s P) (Ioi x) := by
  exact integrable_finsetSum s fun m _ =>
    (integrableOn_complex_exp_neg_mul_natPow x m).smul_const (P m)

/-- The scalar polynomial uses the same coefficients as the concrete
    reconstruction, without introducing a physical pairing by definition. -/
theorem twoJumpScalarFromMoments_polynomial_tail (κ t1 t2 : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (x : ℝ) (s : Finset ℕ) (P : ℕ → Fin 3 → TwoByTwo) :
    (∫ t in Ioi x, (Real.exp (-t) : ℂ) *
      ∑ m ∈ s, twoJumpScalarFromMoments κ t1 t2 A u (P m) * (t : ℂ) ^ m) =
    twoJumpScalarFromMoments κ t1 t2 A u
      (∫ t in Ioi x, twoJumpPolynomialMomentDensity s P t) := by
  rw [← twoJumpScalarFromMoments_integral κ t1 t2 A u x _
    (twoJumpPolynomialMomentDensity_integrable x s P)]
  apply integral_congr_ae
  filter_upwards with t
  simp only [twoJumpPolynomialMomentDensity, map_sum, map_smul, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Endpoint duality now lands in the explicit tangent reconstruction of
    the polynomial tail, not only in an unrelated scalar integral. -/
theorem twoJumpMoment_endpoint_eq_reconstructed_tail (κ t1 t2 : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (x : ℝ) (hx : (x : ℂ) = t1 ∨ (x : ℂ) = t2)
    (s : Finset ℕ) (P : ℕ → Fin 3 → TwoByTwo) :
    (∑ m ∈ s, twoJumpScalarFromMoments κ t1 t2 A u (P m) * twoJumpMomentF t1 t2 m) +
      ((x : ℂ) + 1) *
        (∑ m ∈ s, twoJumpScalarFromMoments κ t1 t2 A u (P m) * twoJumpMomentG t1 t2 m) =
    (Real.exp x : ℂ) * twoJumpScalarFromMoments κ t1 t2 A u
      (∫ t in Ioi x, twoJumpPolynomialMomentDensity s P t) := by
  rw [twoJumpMoment_projected_endpoint_eq_exp_mul_tail t1 t2 x hx s,
    twoJumpScalarFromMoments_polynomial_tail]

/-- Exact `2 i / pi` normalization of section 5 of the endpoint notes.
The vector `v` is reconstructed from the amplitude density. Identifying it
with the actual amplitude derivative is NOT asserted by this theorem. -/
theorem twoJumpProjectedTail_eq_reconstructed_pairing (κ t1 t2 : ℂ)
    (A : Fin 3 → TwoByTwo) (u : Fin 4 → ℂ)
    (x : ℝ) (s : Finset ℕ) (P : ℕ → Fin 3 → TwoByTwo) :
    let v := twoJumpResidueCoordinateLinear A
      (twoJumpTangentResiduesLinear κ t1 t2 A
        (∫ t in Ioi x, twoJumpPolynomialMomentDensity s P t))
    (∫ t in Ioi x, (Real.exp (-t) : ℂ) *
      ((4 / ((Real.pi : ℂ) * Complex.I)) *
        ∑ m ∈ s, twoJumpScalarFromMoments κ t1 t2 A u (-P m) * (t : ℂ) ^ m)) =
    (2 * Complex.I / (Real.pi : ℂ)) *
      (u 0 * v 2 + u 1 * v 3 - u 2 * v 0 - u 3 * v 1) := by
  dsimp only
  simp only [map_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
  rw [integral_neg]
  simp_rw [← mul_assoc (Real.exp _ : ℂ),
    mul_comm (Real.exp _ : ℂ) (4 / ((Real.pi : ℂ) * Complex.I)), mul_assoc]
  rw [integral_const_mul, twoJumpScalarFromMoments_polynomial_tail]
  simp only [twoJumpScalarFromMoments, LinearMap.comp_apply,
    twoJumpRadialPairingLinear, LinearMap.coe_mk, AddHom.coe_mk,
    div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring

end

end NativeCarryFiveFieldCapstone

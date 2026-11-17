import CarrySelfAdjointOperator.C2MellinPositiveDensity
import CarrySelfAdjointOperator.C2MellinLogMomentDerivative

open Set MeasureTheory

namespace CarrySelfAdjointOperator

noncomputable section

/-- The rational density used by the original positive-density development is
pointwise the same as the seed plus the geometric hyperbolic C2-cell density.
The equality is on the Mellin domain `x > 0`, where the source identities are
stated. -/
theorem nativeC2MellinDensity_eq_geometricDensity {x : ℝ} (hx : 0 < x) :
    nativeC2MellinDensity x = nativeC2MellinGeometricDensity x := by
  unfold nativeC2MellinDensity nativeC2MellinGeometricDensity
  rw [nativeC2MellinOmega0_eq_exp_sinh hx]
  rfl

/-- The old rational-source integral and the geometric-cell-source integral
are the same function of the Mellin parameter. -/
theorem nativeC2MellinSourceIntegral_eq_geometricSourceIntegral :
    nativeC2MellinSourceIntegral = nativeC2MellinGeometricSourceIntegral := by
  funext s
  change (∫ x in Ioi (0 : ℝ), x ^ (s - 1) * nativeC2MellinDensity x) =
    ∫ x in Ioi (0 : ℝ), nativeC2MellinGeometricLogIntegrand 0 s x
  simp only [nativeC2MellinGeometricLogIntegrand, pow_zero, mul_one]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  rw [nativeC2MellinDensity_eq_geometricDensity hx]

/-- Every fixed logarithmic source moment agrees across the rational and
geometric spellings of the C2 density. -/
theorem nativeC2MellinLogMoment_eq_geometricLogMoment (s : ℝ) (r : ℕ) :
    nativeC2MellinLogMoment s r = nativeC2MellinGeometricLogMoment r s := by
  change (∫ x in Ioi (0 : ℝ), x ^ (s - 1) * (Real.log x) ^ r *
      nativeC2MellinDensity x) =
    ∫ x in Ioi (0 : ℝ), nativeC2MellinGeometricLogIntegrand r s x
  simp only [nativeC2MellinGeometricLogIntegrand]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  rw [nativeC2MellinDensity_eq_geometricDensity hx]

/-- The legacy all-orders derivative obligation holds for order one at the
critical Mellin parameter. This is a concrete instance, not an all-orders
claim about `nativeC2MellinIteratedDerivativeObligation`. -/
theorem nativeC2MellinIteratedDerivative_one_half :
    iteratedDeriv 1 nativeC2MellinSourceIntegral (1 / 2 : ℝ) =
      nativeC2MellinLogMoment (1 / 2 : ℝ) 1 := by
  rw [nativeC2MellinSourceIntegral_eq_geometricSourceIntegral,
    nativeC2MellinGeometricSourceIntegral_iteratedDeriv_one_half,
    nativeC2MellinLogMoment_eq_geometricLogMoment]

/-- The legacy all-orders derivative obligation holds for order two at the
critical Mellin parameter. The geometric proof establishes the first
derivative identity on a neighborhood before differentiating it. -/
theorem nativeC2MellinIteratedDerivative_two_half :
    iteratedDeriv 2 nativeC2MellinSourceIntegral (1 / 2 : ℝ) =
      nativeC2MellinLogMoment (1 / 2 : ℝ) 2 := by
  rw [nativeC2MellinSourceIntegral_eq_geometricSourceIntegral,
    nativeC2MellinGeometricSourceIntegral_iteratedDeriv_two_half,
    nativeC2MellinLogMoment_eq_geometricLogMoment]

end

end CarrySelfAdjointOperator

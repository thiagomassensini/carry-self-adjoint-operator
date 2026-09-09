import CarrySelfAdjointOperator.NewtonStirlingOperatorIntertwining
import CarrySelfAdjointOperator.CompletedC3ValveNaturality

/-!
# Native depth and horizontal Cp commutator coefficients

The vector here is the existing Dirichlet monomial restricted to `p^k`.
The depth connection has already removed the critical amplitude. Its phase
normalizer must therefore remove only phase, whereas `cpPhaseNormalizer`
removes both phase and critical amplitude. The final crosswalk identifies
coefficients; it does not identify the tower vector with a horizontal gradient.
-/

namespace CarrySelfAdjointOperator.ProjectiveDepth

open CPFormal.Analytic.Cp

noncomputable section

/-- Restriction of the native Dirichlet monomial to the multiplicative tower. -/
def nativeDirichletTower (p : ℕ) (s : ℂ) (k : ℕ) : ℂ :=
  natDirichletTerm s (p ^ k)

@[simp] theorem nativeDirichletTower_zero (p : ℕ) (s : ℂ) :
    nativeDirichletTower p s 0 = 1 := by
  simp [nativeDirichletTower, natDirichletTerm, dirichletTerm]

theorem nativeDirichletTower_succ (p : ℕ) (s : ℂ) (k : ℕ) :
    nativeDirichletTower p s (k + 1) =
      natDirichletTerm s p * nativeDirichletTower p s k := by
  simp only [nativeDirichletTower, pow_succ, natDirichletTerm_mul]
  ring

/-- The covariant shift eigenvalue, using the existing native carry ratio. -/
def nativeDepthShiftEigenvalue (p : ℕ) (s : ℂ) : ℂ :=
  (primeCarryAmplitudeRatio p : ℂ)⁻¹ * natDirichletTerm s p

theorem nativeDepthShiftEigenvalue_eq_cpow
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    nativeDepthShiftEigenvalue p s = (p : ℂ) ^ ((1 : ℂ) / 2 - s) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hsqrt : (Real.sqrt (p : ℝ) : ℂ) = (p : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg p)]
    push_cast
    rfl
  simp only [nativeDepthShiftEigenvalue, primeCarryAmplitudeRatio,
    Complex.ofReal_inv, inv_inv, hsqrt, natDirichletTerm, dirichletTerm,
    Int.cast_natCast]
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hpC]

/-- The actual tower is an eigenvector of the existing covariant shift. -/
theorem nativeDepthShift_nativeDirichletTower (p : ℕ) (s : ℂ) :
    (weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) + (LinearMap.id : Module.End ℂ (ℕ → ℂ)))
        (nativeDirichletTower p s) =
      nativeDepthShiftEigenvalue p s • nativeDirichletTower p s := by
  funext k
  change (primeCarryAmplitudeRatio p : ℂ)⁻¹ * nativeDirichletTower p s (k + 1) -
      nativeDirichletTower p s k + nativeDirichletTower p s k = _
  rw [nativeDirichletTower_succ]
  simp [nativeDepthShiftEigenvalue, mul_assoc]

/-- The unnormalized logarithmic commutator eigenvalue. -/
def nativeDepthCommutatorEigenvalue (p : ℕ) (s : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * nativeDepthShiftEigenvalue p s

theorem nativeDepthCommutator_nativeDirichletTower (p : ℕ) (s : ℂ) :
    (weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) * towerLogMultiplication p -
        towerLogMultiplication p * weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p))
        (nativeDirichletTower p s) =
      nativeDepthCommutatorEigenvalue p s • nativeDirichletTower p s := by
  rw [nativeDepthDifference_logMultiplication_commutator]
  change (Real.log (p : ℝ) : ℂ) •
      ((weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) + (LinearMap.id : Module.End ℂ (ℕ → ℂ)))
        (nativeDirichletTower p s)) = _
  rw [nativeDepthShift_nativeDirichletTower, smul_smul]
  rfl

/-- Phase removal only: the connection already supplies the critical scale. -/
def nativeDepthPhaseNormalizer (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (Complex.I * s.im)

/-- Exact accounting of the critical amplitude between the two normalizers. -/
theorem nativeDepthPhaseNormalizer_mul_ratio_inv
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    nativeDepthPhaseNormalizer p s * (primeCarryAmplitudeRatio p : ℂ)⁻¹ =
      cpPhaseNormalizer p s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hsqrt : (Real.sqrt (p : ℝ) : ℂ) = (p : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg p)]
    push_cast
    rfl
  simp only [nativeDepthPhaseNormalizer, primeCarryAmplitudeRatio,
    Complex.ofReal_inv, inv_inv, hsqrt, cpPhaseNormalizer]
  rw [← Complex.cpow_add _ _ hpC, add_comm]

/-- This coefficient is computed from the actual depth commutator action. -/
def normalizedDepthCommutatorEigenvalue (p : ℕ) (s : ℂ) : ℂ :=
  nativeDepthPhaseNormalizer p s * nativeDepthCommutatorEigenvalue p s

theorem normalizedDepthCommutatorEigenvalue_eq_cpLogScale
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    normalizedDepthCommutatorEigenvalue p s =
      cpPhaseNormalizer p s * cpLogScaleCoefficient p s := by
  unfold normalizedDepthCommutatorEigenvalue nativeDepthCommutatorEigenvalue
    nativeDepthShiftEigenvalue cpLogScaleCoefficient
  calc
    _ = (nativeDepthPhaseNormalizer p s * (primeCarryAmplitudeRatio p : ℂ)⁻¹) *
        ((Real.log (p : ℝ) : ℂ) * natDirichletTerm s p) := by ring
    _ = _ := by rw [nativeDepthPhaseNormalizer_mul_ratio_inv p hp s]

theorem normalizedDepthCommutatorEigenvalue_eq_radial_logScale
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    normalizedDepthCommutatorEigenvalue p s =
      (Real.log (p : ℝ) : ℂ) *
        (((p : ℝ) ^ (-criticalDisplacement s.re) : ℝ) : ℂ) := by
  rw [normalizedDepthCommutatorEigenvalue_eq_cpLogScale p hp.ne_zero]
  unfold cpLogScaleCoefficient
  calc
    _ = (Real.log (p : ℝ) : ℂ) *
        (cpPhaseNormalizer p s * natDirichletTerm s p) := by ring
    _ = _ := by rw [cpPhaseNormalizer_mul_eigenvalue p hp s]

/-- Horizontal Cp readout uses exactly the normalized depth eigenvalue. -/
theorem phaseNormalizedCpLogJetCommutator_eq_depthEigenvalue_mul_gradient
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpLogJetCommutator p s n =
      normalizedDepthCommutatorEigenvalue p s * positiveDirichletGradient s n := by
  rw [normalizedDepthCommutatorEigenvalue_eq_cpLogScale p hp]
  unfold phaseNormalizedCpLogJetCommutator
  rw [cpLogJetCommutator_eq_logScale_mul_gradient p hp]
  ring

/-- The normalized operator acts on the tower with the same scalar as Cp. -/
theorem normalizedDepthCommutator_nativeDirichletTower (p : ℕ) (s : ℂ) :
    nativeDepthPhaseNormalizer p s •
      ((weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) * towerLogMultiplication p -
          towerLogMultiplication p * weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p))
          (nativeDirichletTower p s)) =
      normalizedDepthCommutatorEigenvalue p s • nativeDirichletTower p s := by
  rw [nativeDepthCommutator_nativeDirichletTower, smul_smul]
  rfl

/-- Evaluate the actual normalized operator at the tower seed, which is one.
No division by the tower vector is needed. -/
theorem normalizedDepthCommutator_at_zero (p : ℕ) (s : ℂ) :
    nativeDepthPhaseNormalizer p s *
      ((weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) * towerLogMultiplication p -
          towerLogMultiplication p * weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p))
          (nativeDirichletTower p s) 0) =
      normalizedDepthCommutatorEigenvalue p s := by
  have h := congrFun (normalizedDepthCommutator_nativeDirichletTower p s) 0
  simpa using h

/-- Direct operator-to-Cp readout, retaining distinct vertical and horizontal indices. -/
theorem phaseNormalizedCpLogJetCommutator_eq_depthOperatorReadout
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) (n : ℕ) :
    phaseNormalizedCpLogJetCommutator p s n =
      (nativeDepthPhaseNormalizer p s *
        ((weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p) * towerLogMultiplication p -
            towerLogMultiplication p * weightedDepthDifferenceLinear (primeCarryAmplitudeRatio p))
            (nativeDirichletTower p s) 0)) * positiveDirichletGradient s n := by
  rw [normalizedDepthCommutator_at_zero,
    phaseNormalizedCpLogJetCommutator_eq_depthEigenvalue_mul_gradient p hp s n]

/-- The coefficient crosswalk survives the existing full formal-series readout. -/
theorem canonicalCpLogJetCommutatorSeries_normalized_eq_depthEigenvalue
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    cpPhaseNormalizer p s • canonicalCpLogJetCommutatorSeries p s =
      normalizedDepthCommutatorEigenvalue p s • canonicalCpOrdinaryGradientSeries s := by
  ext n
  simpa [canonicalCpLogJetCommutatorSeries, canonicalCpOrdinaryGradientSeries,
    phaseNormalizedCpLogJetCommutator] using
    phaseNormalizedCpLogJetCommutator_eq_depthEigenvalue_mul_gradient p hp s n

/-- Transport the same equality with the existing projective coordinate map. -/
theorem toProjective_normalizedCpLogJetCommutatorSeries_eq_depthEigenvalue
    (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    toProjective (cpPhaseNormalizer p s • canonicalCpLogJetCommutatorSeries p s) =
      toProjective
        (normalizedDepthCommutatorEigenvalue p s • canonicalCpOrdinaryGradientSeries s) := by
  rw [canonicalCpLogJetCommutatorSeries_normalized_eq_depthEigenvalue p hp s]

end
end CarrySelfAdjointOperator.ProjectiveDepth

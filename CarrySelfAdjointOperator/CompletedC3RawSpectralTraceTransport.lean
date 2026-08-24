import CarrySelfAdjointOperator.CompletedC3RawGreenGamma
import CarrySelfAdjointOperator.CanonicalC3GlobalCameraBoundaryBridge

/-!
# Raw C3 coefficient to completed spectral trace

This file records the coefficient transport without identifying distinct
stages prematurely:

1. the raw C3 eigenvalue determines the C3 chart factor;
2. the raw logarithmic companion determines the derivative of that factor;
3. phase normalization and reflection turn the raw eigenvalue difference
   into the centered spectral factor times the positive radial cofactor;
4. the reflected Gram term is the inner product of the same completed
   all-cutoff states.

The final theorem isolates, without a free defect parameter, the remaining
statement needed to identify the `F, -F'` boundary Wronskian with that
completed state-level Green form.
-/

open scoped Topology BigOperators lp ENNReal NNReal ComplexConjugate

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Raw eigenvalue and logarithmic companion -/

/-- The C3 chart factor is affine in the raw camera eigenvalue. -/
theorem cpChartFactor_three_eq_one_sub_three_mul_rawEigenvalue
    (s : ℂ) :
    cpChartFactor 3 s =
      1 - (3 : ℂ) * NativeCarryC3Crosswalk.c3RawCameraEigenvalue s := by
  unfold cpChartFactor NativeCarryC3Crosswalk.c3RawCameraEigenvalue
  rw [← prime_mul_dirichletTerm_eq_cpow_one_sub 3 (by norm_num) s]
  rfl

/-- The logarithmic companion is exactly minus the derivative of the raw
camera eigenvalue. -/
theorem hasDerivAt_c3RawCameraEigenvalue
    (s : ℂ) :
    HasDerivAt NativeCarryC3Crosswalk.c3RawCameraEigenvalue
      (-cpLogScaleCoefficient 3 s) s := by
  change HasDerivAt (fun u : ℂ => natDirichletTerm u 3)
    (-cpLogScaleCoefficient 3 s) s
  simpa only [cpLogScaleCoefficient, natLogDirichletTerm] using
    (hasDerivAt_natDirichletTerm_eq_neg_natLogDirichletTerm
      3 (by norm_num) s)

/-- Differentiating the affine chart identity retains the logarithmic
channel: `factor' = 3 * log(3) * 3^(-s)`. -/
theorem deriv_cpChartFactor_three_eq_three_mul_logScale
    (s : ℂ) :
    deriv (cpChartFactor 3) s =
      (3 : ℂ) * cpLogScaleCoefficient 3 s := by
  have hraw := hasDerivAt_c3RawCameraEigenvalue s
  have hderived :
      HasDerivAt
        (fun u : ℂ =>
          1 - (3 : ℂ) *
            NativeCarryC3Crosswalk.c3RawCameraEigenvalue u)
        ((3 : ℂ) * cpLogScaleCoefficient 3 s) s := by
    have hbase :=
      (hasDerivAt_const (x := s) (c := (1 : ℂ))).sub
        (hraw.const_mul (3 : ℂ))
    change HasDerivAt
      (fun u : ℂ =>
        1 - (3 : ℂ) *
          NativeCarryC3Crosswalk.c3RawCameraEigenvalue u)
      (0 - (3 : ℂ) * (-cpLogScaleCoefficient 3 s)) s at hbase
    simpa only [mul_neg, sub_neg_eq_add, zero_add] using hbase
  have hfunctions :
      (fun u : ℂ =>
        1 - (3 : ℂ) *
          NativeCarryC3Crosswalk.c3RawCameraEigenvalue u) =
        cpChartFactor 3 := by
    funext u
    exact (cpChartFactor_three_eq_one_sub_three_mul_rawEigenvalue u).symm
  rw [hfunctions] at hderived
  exact hderived.deriv

/-! ## Coefficient transport before any real-part projection -/

/-- Raw reflected C3 coefficient after the canonical phase normalization. -/
def canonicalC3RadiallyNormalizedRawCoefficient (s : ℂ) : ℂ :=
  cpPhaseNormalizer 3 (reflectedParameter s) *
      NativeCarryC3Crosswalk.c3RawCameraEigenvalue (reflectedParameter s) -
    cpPhaseNormalizer 3 s *
      NativeCarryC3Crosswalk.c3RawCameraEigenvalue s

/-- Phase removal turns the raw coefficient into the real radial
difference. -/
theorem canonicalC3RadiallyNormalizedRawCoefficient_eq_radialDifference
    (s : ℂ) :
    canonicalC3RadiallyNormalizedRawCoefficient s =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) := by
  unfold canonicalC3RadiallyNormalizedRawCoefficient
    NativeCarryC3Crosswalk.c3RawCameraEigenvalue
  rw [cpPhaseNormalizer_mul_eigenvalue 3 (by norm_num)
      (reflectedParameter s),
    cpPhaseNormalizer_mul_eigenvalue 3 (by norm_num) s,
    criticalDisplacement_reflectedParameter]
  simp only [neg_neg]
  rw [show cpRadialDifference 3 (criticalDisplacement s.re) =
      (3 : ℝ) ^ (criticalDisplacement s.re) -
        (3 : ℝ) ^ (-criticalDisplacement s.re) by rfl]
  push_cast
  rfl

/-- The radial difference is exactly the centered spectral skew, rotated
before projection, times the positive radial cofactor. -/
theorem radialDifference_eq_i_mul_centeredFactor_mul_cofactor
    (s : ℂ) :
    ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) =
      Complex.I *
        (centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s)) *
        ((cpRadialCofactor 3 (criticalDisplacement s.re) : ℝ) : ℂ) := by
  have hcentered :
      centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s) =
        (-(2 : ℂ) * Complex.I) *
          (criticalDisplacement s.re : ℂ) := by
    apply Complex.ext
    · simp [centeredHeightParameter, criticalDisplacement, Complex.mul_re,
        Complex.mul_im]
    · simp [centeredHeightParameter, criticalDisplacement, Complex.mul_re,
        Complex.mul_im]
      ring
  rw [cpRadialDifference_eq_two_mul_delta_mul_cofactor, hcentered]
  push_cast
  have hI :
      Complex.I * (-(2 : ℂ) * Complex.I) = (2 : ℂ) := by
    calc
      Complex.I * (-(2 : ℂ) * Complex.I) =
          -(2 : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -(2 : ℂ) * (-1) := by rw [Complex.I_mul_I]
      _ = 2 := by ring
  calc
    (2 : ℂ) * (criticalDisplacement s.re : ℂ) *
          (cpRadialCofactor 3 (criticalDisplacement s.re) : ℂ) =
        (Complex.I * (-(2 : ℂ) * Complex.I)) *
          (criticalDisplacement s.re : ℂ) *
            (cpRadialCofactor 3 (criticalDisplacement s.re) : ℂ) := by
      rw [hI]
    _ = Complex.I *
          ((-(2 : ℂ) * Complex.I) *
            (criticalDisplacement s.re : ℂ)) *
          (cpRadialCofactor 3 (criticalDisplacement s.re) : ℂ) := by
      ring

theorem canonicalC3RadiallyNormalizedRawCoefficient_eq_spectralFactor
    (s : ℂ) :
    canonicalC3RadiallyNormalizedRawCoefficient s =
      Complex.I *
        (centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s)) *
        ((cpRadialCofactor 3 (criticalDisplacement s.re) : ℝ) : ℂ) := by
  rw [canonicalC3RadiallyNormalizedRawCoefficient_eq_radialDifference,
    radialDifference_eq_i_mul_centeredFactor_mul_cofactor]

/-! ## The same completed all-cutoff state -/

/-- The reflected infinite pairing is the inner product of the two ordinary
channels in the completed all-cutoff state. -/
theorem canonicalCompletedC3RawGammaGram_reflected_eq_infinitePairing
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawGammaGram s (reflectedParameter s)
        hs.1 (by simpa [reflectedParameter] using sub_pos.mpr hs.2) =
      infiniteReflectedGradientPairing s := by
  unfold canonicalCompletedC3RawGammaGram
    infiniteReflectedGradientPairing finiteReflectedGradientEdge
  rw [lp.inner_eq_tsum]
  congr 1
  funext n
  simp [RCLike.inner_apply, mul_comm]

/-- Positive radial energy expressed only through the same completed
ordinary state pair. -/
def canonicalCompletedC3RawStateRadialEnergy
    (s : ℂ) (hs : s ∈ genuineCriticalStrip) : ℝ :=
  2 * cpRadialCofactor 3 (criticalDisplacement s.re) *
    (canonicalCompletedC3RawGammaGram s (reflectedParameter s)
      hs.1 (by simpa [reflectedParameter] using sub_pos.mpr hs.2)).re

theorem canonicalCompletedC3RawStateRadialEnergy_eq_infiniteEnergy
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3RawStateRadialEnergy s hs =
      canonicalCompletedC3InfiniteRadialGreenEnergy s := by
  unfold canonicalCompletedC3RawStateRadialEnergy
    canonicalCompletedC3InfiniteRadialGreenEnergy
    infiniteReflectedGreenEnergy
  rw [canonicalCompletedC3RawGammaGram_reflected_eq_infinitePairing hs]

/-- After phase normalization and the final channel-local rotation, the raw
coefficient acts on the same completed state by the centered spectral
factor. -/
theorem canonicalCompletedC3NormalizedGreenLimitTrace_eq_rawStateSpectralForm
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    canonicalCompletedC3NormalizedGreenLimitTrace s =
      (centeredHeightParameter s -
          (starRingEnd ℂ) (centeredHeightParameter s)) *
        (canonicalCompletedC3RawStateRadialEnergy s hs : ℂ) := by
  rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_energy,
    canonicalCompletedC3RawStateRadialEnergy_eq_infiniteEnergy hs]

/-! ## Completed `F, -F'` traces -/

/-- Value and companion read from one tail-completed enriched TFVD pair. -/
def canonicalCompletedC3TracePair (z : ℂ) : ℂ × ℂ :=
  (canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout z,
    canonicalCompletedC3EnrichedTfvdBoundaryCompanion z)

/-- On the strip, that same trace pair is literally `(F, -F')`. -/
theorem canonicalCompletedC3TracePair_eq_F_negFprime
    {z : ℂ} (hs : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3TracePair z =
      (completedNativeOperatorCharacteristic z,
        -deriv completedNativeOperatorCharacteristic z) := by
  unfold canonicalCompletedC3TracePair
  apply Prod.ext
  · exact
      canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout_eq_characteristic
        hs
  · rw [
      canonicalCompletedC3EnrichedTfvdBoundaryCompanion_eq_completedNativeOperatorBoundaryCompanion
        hs,
      completedNativeOperatorBoundaryCompanion_eq_neg_deriv]

/-- No residual is hidden in the final statement: identifying the completed
`F, -F'` Wronskian with the same-state spectral Green form is exactly
identifying it with the already constructed normalized C3 Green limit. -/
theorem completedTraceWronskian_eq_rawStateSpectralForm_iff_greenLimit
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion
          (centeredHeightParameter s) (centeredHeightParameter s) =
        (centeredHeightParameter s -
            (starRingEnd ℂ) (centeredHeightParameter s)) *
          (canonicalCompletedC3RawStateRadialEnergy s hs : ℂ) ↔
      completedGreenWronskian
          canonicalCompletedC3EnrichedTfvdCompletedValueTailReadout
          canonicalCompletedC3EnrichedTfvdBoundaryCompanion
          (centeredHeightParameter s) (centeredHeightParameter s) =
        canonicalCompletedC3NormalizedGreenLimitTrace s := by
  rw [canonicalCompletedC3NormalizedGreenLimitTrace_eq_rawStateSpectralForm hs]

end

end CarrySelfAdjointOperator

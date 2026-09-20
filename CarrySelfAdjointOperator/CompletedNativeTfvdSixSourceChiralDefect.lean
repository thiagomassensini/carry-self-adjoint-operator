import CarrySelfAdjointOperator.PrimeDepthAllOrderMomentBridge
import CarrySelfAdjointOperator.CompletedNativeChiralReturnStorage
import Mathlib.Tactic

/-!
# Six-source TFVD/Green realization of the radial chiral defect

The complete seeded-clock six-source TFVD/Green kernel has already been
identified with the completed-native divided slope.  Separately, the divided
slope is a positive-amplitude congruence of the Cauchy multiplier defect.
This module composes those two identifications without inserting a positivity
assumption:

```text
material six-source kernel
  = (1 / 2) A* (Gram(Cauchy) - Gram(chiral multiplier)) A.
```

Thus the input and output channels are the concrete Cauchy feature and its
chiral-multiplier image, while the left hand side remains the full material
TFVD/Green clock readout.  The equality is deliberately kept separate from
the still-open assertion that this signed difference is positive semidefinite.
In particular, none of the literal BR2 center-leg energy-excess results are
used here.
-/

open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- The finite quadratic form read directly from the material six-source
TFVD/Green radial kernel.  This is the source-side candidate defect for a
coefficient vector `c`; it is defined before any semidefinite claim. -/
def nativeC3SeededClockTfvdSixSourceRadialSampleQuadratic
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (k N : ℕ) (c : Fin N → ℂ) : ℂ :=
  star c ⬝ᵥ
    (nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
      M q hq0 hq1 S k N *ᵥ c)

/-- The exact radial six-source TFVD/Green sample is the positive-amplitude
congruence of the Cauchy input-minus-multiplier-output Gram defect.  This is
an equality of material kernels, not a claim that either side is positive. -/
theorem nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_eq_chiralMultiplierDefect
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
        M q hqpos.le hq1 S k N =
      (2 : ℝ)⁻¹ •
        (Matrix.conjTranspose
              (Matrix.diagonal (fun i : Fin N =>
                completedNativeNormalizedPositiveChiralAmplitude
                  (canonicalCompletedC3RadialTiltPoint k i))) *
            canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N *
          Matrix.diagonal (fun i : Fin N =>
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k i))) := by
  rw [nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_eq_dslope
      M q hqpos hq1 S k N hregular,
    canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence
      k N hregular,
    canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect]

/-- Entrywise version of the same material identity.  It keeps the two
ambient Cauchy channels visible as the signed projective chiral form, so the
factor `1 / 2` and the positive amplitude cannot be silently dropped. -/
theorem nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_apply_eq_projectiveChiralForm
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin N) :
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
        M q hqpos.le hq1 S k N i j =
      canonicalCompletedNativeProjectiveChiralForm
        (canonicalCompletedNativeRadialProjectiveChiralState k i)
        (canonicalCompletedNativeRadialProjectiveChiralState k j) := by
  have hmatrix :=
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_eq_projectiveChiral
      M q hqpos hq1 S k N hregular
  change
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
        M q hqpos.le hq1 S k N i j = _
  rw [hmatrix]
  rfl

/-- The real part of the material six-source quadratic defect is precisely
the Cauchy input energy minus the chiral-multiplier output energy, up to the
forced factor `2`.  In particular, this gives an explicit finite-combination
energy identity without taking either moment-matrix positivity or the
contractivity conclusion as an input. -/
theorem nativeC3SeededClockTfvdSixSourceRadialSampleQuadratic_re_eq_chiralInput_sub_output
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (c : Fin N → ℂ) :
    2 *
        (nativeC3SeededClockTfvdSixSourceRadialSampleQuadratic
          M q hqpos.le hq1 S k N c).re =
      ‖∑ i, (c i * completedNativeNormalizedPositiveChiralAmplitude
          (canonicalCompletedC3RadialTiltPoint k i)) •
          completedNativeRadialChiralCauchyState k i‖ ^ 2 -
        ‖∑ i, (c i * completedNativeNormalizedPositiveChiralAmplitude
          (canonicalCompletedC3RadialTiltPoint k i)) •
          completedNativeRadialChiralMultiplierState k i‖ ^ 2 := by
  have hstorage := ChiralReturn.storage_one_eq_native_quadratic k N c hregular
  have hmaterial :
      ChiralReturn.storage k
          (fun i => c i * completedNativeNormalizedPositiveChiralAmplitude
            (canonicalCompletedC3RadialTiltPoint k i)) 1 =
        2 * nativeC3SeededClockTfvdSixSourceRadialSampleQuadratic
          M q hqpos.le hq1 S k N c := by
    rw [hstorage,
      ← nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_eq_dslope
        M q hqpos hq1 S k N hregular]
    rfl
  have hreal := congrArg Complex.re hmaterial
  rw [ChiralReturn.storage_re_eq_norm_balance] at hreal
  simpa [Complex.mul_re] using hreal.symm

/-- Smallest finite sanity check: the one-point material sample is exactly
the diagonal signed Cauchy-versus-multiplier defect.  Its sign is therefore
equivalent to the still-separate one-vector multiplier contraction; this
theorem intentionally establishes the orientation and normalization only. -/
theorem nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_one_apply_zero_eq_projectiveChiralDiagonal
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (k : ℕ)
    (hregular : ∀ i : Fin 1,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
        M q hqpos.le hq1 S k 1 0 0 =
      canonicalCompletedNativeProjectiveChiralForm
        (canonicalCompletedNativeRadialProjectiveChiralState k 0)
        (canonicalCompletedNativeRadialProjectiveChiralState k 0) := by
  exact
    nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_apply_eq_projectiveChiralForm
      M q hqpos hq1 S k 1 hregular 0 0

/-- On each regular finite radial section, positivity of the material
six-source kernel is *equivalent* to the Cauchy multiplier contraction.  This
records the precise remaining gate after the exact source-to-defect
composition, rather than treating that gate as already discharged. -/
theorem nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_posSemidef_iff_chiralMultiplierContractive
    (M : ℕ) (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (S : Finset NativeGpreBoundaryContext)
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (nativeC3SeededClockTfvdSixSourceRadialSampleMatrix
        M q hqpos.le hq1 S k N).PosSemidef ↔
      CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N :=
  nativeC3SeededClockTfvdSixSourceRadialSampleMatrix_posSemidef_iff_contractive
    M q hqpos hq1 S k N hregular

end

end CarrySelfAdjointOperator

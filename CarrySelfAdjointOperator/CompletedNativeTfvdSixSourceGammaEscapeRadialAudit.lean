import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceGammaEscapeBalance
import CarrySelfAdjointOperator.CompletedNativeTfvdSixSourceChiralDefect
import Mathlib.Tactic

/-!
# Radial audit of the polarized Cauchy--Gamma-escape balance

This module does not identify the Gamma balance with the Pick or `dslope`
defect.  Instead it puts them on the same canonical shifted radial grid and
defines their exact entrywise residual after retaining the forced `1 / 2`
and positive-chiral-amplitude congruence.  Thus the one-, two-, and
three-point microscopes expose the one remaining equality that would have to
be established for a Gamma-escape realization of the material defect.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

noncomputable section

/-- The exact Cauchy factor on the shifted radial grid.  It is the
quarter-turned spectral separation `I / (zⱼ - conj zᵢ)`, expressed without
any fitted normalization. -/
def canonicalCompletedNativeRadialChiralCauchyFactor
    (k i j : ℕ) : ℂ :=
  ((k : ℝ) + 1) * (((i + j + 2 : ℕ) : ℝ)⁻¹)

@[simp] theorem canonicalCompletedNativeRadialChiralCauchyFactor_zero_zero
    (k : ℕ) :
    canonicalCompletedNativeRadialChiralCauchyFactor k 0 0 =
      ((((k : ℝ) + 1) * ((2 : ℝ)⁻¹) : ℝ) : ℂ) := by
  unfold canonicalCompletedNativeRadialChiralCauchyFactor
  norm_num

@[simp] theorem canonicalCompletedNativeRadialChiralCauchyFactor_zero_one
    (k : ℕ) :
    canonicalCompletedNativeRadialChiralCauchyFactor k 0 1 =
      ((((k : ℝ) + 1) * ((3 : ℝ)⁻¹) : ℝ) : ℂ) := by
  unfold canonicalCompletedNativeRadialChiralCauchyFactor
  norm_num

@[simp] theorem canonicalCompletedNativeRadialChiralCauchyFactor_one_zero
    (k : ℕ) :
    canonicalCompletedNativeRadialChiralCauchyFactor k 1 0 =
      ((((k : ℝ) + 1) * ((3 : ℝ)⁻¹) : ℝ) : ℂ) := by
  unfold canonicalCompletedNativeRadialChiralCauchyFactor
  norm_num

@[simp] theorem canonicalCompletedNativeRadialChiralCauchyFactor_one_one
    (k : ℕ) :
    canonicalCompletedNativeRadialChiralCauchyFactor k 1 1 =
      ((((k : ℝ) + 1) * ((4 : ℝ)⁻¹) : ℝ) : ℂ) := by
  unfold canonicalCompletedNativeRadialChiralCauchyFactor
  norm_num

/-- The polarized Cauchy--Gamma-escape balance sampled on the canonical
off-axis radial grid.  The half-plane witness is supplied separately because
the shifted grid is only in the completed ambient resolvent domain once its
finite sample size is fixed. -/
def canonicalCompletedNativeRadialGammaEscapeBalanceSampleMatrix
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3GammaCauchyEscapeBalanceKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
      (hhalf j)

/-- The exact unresolved radial channel: completed-native `dslope` minus
the Gamma Cauchy--escape balance.  It is a kernel residual, not a Cholesky
factorization and not a positivity assertion. -/
def canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re) :
    Matrix (Fin N) (Fin N) ℂ :=
  canonicalCompletedNativeRadialDslopeSampleMatrix k N -
    canonicalCompletedNativeRadialGammaEscapeBalanceSampleMatrix k N hhalf

/-- Entrywise spelling of the sampled Gamma balance. -/
theorem canonicalCompletedNativeRadialGammaEscapeBalanceSampleMatrix_apply
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (i j : Fin N) :
    canonicalCompletedNativeRadialGammaEscapeBalanceSampleMatrix
        k N hhalf i j =
      canonicalCompletedC3GammaCauchyEscapeBalanceKernel
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
        (hhalf j) :=
  rfl

/-- Entrywise spelling of the unresolved `dslope`-minus-Gamma residual. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix_apply
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (i j : Fin N) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k N hhalf i j =
      canonicalCompletedNativePolarizedDslopeKernel
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j) -
      canonicalCompletedC3GammaCauchyEscapeBalanceKernel
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
        (hhalf j) :=
  rfl

/-- Exact radial entry formula for the Pick kernel itself.  The factor on
the right is the quarter-turn divided by the spectral separation on this
grid; it is retained as the concrete Cauchy normalization. -/
theorem canonicalCompletedNativeRadialChiralPickSampleMatrix_apply_eq_cauchyFactor
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedNativeRadialChiralPickSampleMatrix k N i j =
      canonicalCompletedNativeRadialChiralCauchyFactor k i j *
        (1 -
          conj (completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k i)) *
            completedNativeHermiteBiehlerChiralQuotient
              (canonicalCompletedC3RadialTiltPoint k j)) := by
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect,
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply]
  unfold canonicalCompletedNativeRadialChiralCauchyFactor
  push_cast
  rfl

/-- After all canonical amplitudes are retained, the radial residual is
exactly the amplitude-congruent Pick entry minus the Gamma balance.  No
equality is claimed between the two summands. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidual_apply_eq_amplitudePick_sub
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin N) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k N hhalf i j =
      (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (conj (completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k i)) *
            canonicalCompletedNativeRadialChiralPickSampleMatrix k N i j *
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k j)) -
        canonicalCompletedC3GammaCauchyEscapeBalanceKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
          (hhalf j) := by
  have hmatrix := canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence
    k N hregular
  have happly := congrFun (congrFun hmatrix i) j
  unfold canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
    canonicalCompletedNativeRadialGammaEscapeBalanceSampleMatrix
  simp only [Matrix.sub_apply, Matrix.of_apply]
  rw [happly]
  simp only [Matrix.smul_apply,
    Matrix.mul_diagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Pi.star_apply, Complex.real_smul,
    Complex.ofReal_inv, starRingEnd_apply]

/-- Fully scalarized radial comparison, with the quarter-turn/separation
factor, the forced half, and both positive chiral amplitudes all visible. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidual_apply_eq_explicit_sub
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin N) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k N hhalf i j =
      (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (conj (completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k i)) *
            canonicalCompletedNativeRadialChiralCauchyFactor k i j *
            (1 -
              conj (completedNativeHermiteBiehlerChiralQuotient
                (canonicalCompletedC3RadialTiltPoint k i)) *
                completedNativeHermiteBiehlerChiralQuotient
                  (canonicalCompletedC3RadialTiltPoint k j)) *
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k j)) -
        canonicalCompletedC3GammaCauchyEscapeBalanceKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
          (hhalf j) := by
  rw [canonicalCompletedNativeRadialGammaEscapePickResidual_apply_eq_amplitudePick_sub
      k N hhalf hregular i j,
    canonicalCompletedNativeRadialChiralPickSampleMatrix_apply_eq_cauchyFactor
      k N i j]
  ring

/-- The residual vanishes precisely when the sampled Gamma balance equals
the completed-native `dslope` sample matrix.  This is the exact remaining
upstream sewing condition; no semidefinite premise occurs. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidual_eq_zero_iff
    (k N : ℕ)
    (hhalf : ∀ i : Fin N,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k N hhalf = 0 ↔
      canonicalCompletedNativeRadialDslopeSampleMatrix k N =
        canonicalCompletedNativeRadialGammaEscapeBalanceSampleMatrix k N hhalf := by
  unfold canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
  exact sub_eq_zero

/-- The one-point microscope is the `z₀ = I/(k+1)` diagonal instance of the
fully scalarized residual formula. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidual_one_apply_zero
    (k : ℕ)
    (hhalf : ∀ i : Fin 1,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (hregular : ∀ i : Fin 1,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k 1 hhalf 0 0 =
      (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (conj (completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k 0)) *
            canonicalCompletedNativeRadialChiralCauchyFactor k 0 0 *
            (1 -
              conj (completedNativeHermiteBiehlerChiralQuotient
                (canonicalCompletedC3RadialTiltPoint k 0)) *
                completedNativeHermiteBiehlerChiralQuotient
                  (canonicalCompletedC3RadialTiltPoint k 0)) *
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k 0)) -
        canonicalCompletedC3GammaCauchyEscapeBalanceKernel
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k 0)
          (hhalf 0) := by
  exact
    canonicalCompletedNativeRadialGammaEscapePickResidual_apply_eq_explicit_sub
      k 1 hhalf hregular (0 : Fin 1) (0 : Fin 1)

/-- The two-point microscope supplies all four entries at
`I/(k+1), 2I/(k+1)` by specializing `i,j : Fin 2`; the exact scalar
coefficient is retained entrywise rather than fitted numerically. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidual_two_apply
    (k : ℕ)
    (hhalf : ∀ i : Fin 2,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (hregular : ∀ i : Fin 2,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin 2) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k 2 hhalf i j =
      (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (conj (completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k i)) *
            canonicalCompletedNativeRadialChiralCauchyFactor k i j *
            (1 -
              conj (completedNativeHermiteBiehlerChiralQuotient
                (canonicalCompletedC3RadialTiltPoint k i)) *
                completedNativeHermiteBiehlerChiralQuotient
                  (canonicalCompletedC3RadialTiltPoint k j)) *
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k j)) -
        canonicalCompletedC3GammaCauchyEscapeBalanceKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
          (hhalf j) :=
  canonicalCompletedNativeRadialGammaEscapePickResidual_apply_eq_explicit_sub
    k 2 hhalf hregular i j

/-- The three-point microscope supplies every entry at
`I/(k+1), 2I/(k+1), 3I/(k+1)` with the same exact amplitude and separation
normalization.  It deliberately stops at entries rather than a determinant. -/
theorem canonicalCompletedNativeRadialGammaEscapePickResidual_three_apply
    (k : ℕ)
    (hhalf : ∀ i : Fin 3,
      0 < (operatorHeightParameter
        (canonicalCompletedC3RadialTiltPoint k i)).re)
    (hregular : ∀ i : Fin 3,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (i j : Fin 3) :
    canonicalCompletedNativeRadialGammaEscapePickResidualSampleMatrix
        k 3 hhalf i j =
      (((2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (conj (completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k i)) *
            canonicalCompletedNativeRadialChiralCauchyFactor k i j *
            (1 -
              conj (completedNativeHermiteBiehlerChiralQuotient
                (canonicalCompletedC3RadialTiltPoint k i)) *
                completedNativeHermiteBiehlerChiralQuotient
                  (canonicalCompletedC3RadialTiltPoint k j)) *
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k j)) -
        canonicalCompletedC3GammaCauchyEscapeBalanceKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)
          (hhalf j) :=
  canonicalCompletedNativeRadialGammaEscapePickResidual_apply_eq_explicit_sub
    k 3 hhalf hregular i j

end

end CarrySelfAdjointOperator

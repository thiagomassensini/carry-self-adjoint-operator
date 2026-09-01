import CarrySelfAdjointOperator.CompletedNativeChiralPickHankel
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Radial chiral multiplier realization

The spectral-separation quotient in the completed chiral identity is not a
pointwise scalar normalization.  On the shifted imaginary grid it is the
Cauchy kernel

`(k + 1) / (i + j + 2)`.

This module realizes that matrix as a genuine `L^2[0,1]` Gram matrix.  The
completed Hermite--Biehler quotient then acts as a diagonal multiplier on the
finite Cauchy family.  Its defect Gram is exactly the radial chiral Pick
matrix, so finite-combination contractivity is the vector form of the Pick
gate used by the completed-native Hankel limit.

No positivity of the completed moments, spectral statement, or confinement
claim is assumed.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace MatrixOrder unitInterval

namespace CarrySelfAdjointOperator

open Filter MeasureTheory

noncomputable section

/-! ## The canonical Cauchy carrier -/

/-- Hilbert carrier for the separation regularizer. -/
abbrev CanonicalCompletedNativeChiralCauchyCarrier :=
  Lp ℂ 2 (volume : Measure unitInterval)

/-- The monomial half-density `sqrt x * x^n` on the unit interval. -/
def completedNativeChiralCauchyContinuousFeature
    (n : ℕ) : C(unitInterval, ℂ) where
  toFun x := ((Real.sqrt (x : ℝ) * (x : ℝ) ^ n : ℝ) : ℂ)
  continuous_toFun := by fun_prop

/-- The same half-density as an `L^2[0,1]` vector. -/
def completedNativeChiralCauchyFeature
    (n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ContinuousMap.toLp 2 volume ℂ
    (completedNativeChiralCauchyContinuousFeature n)

/-- The half-density monomials realize the shifted Hilbert matrix exactly. -/
theorem inner_completedNativeChiralCauchyFeature
    (i j : ℕ) :
    inner ℂ (completedNativeChiralCauchyFeature i)
        (completedNativeChiralCauchyFeature j) =
      (((i + j + 2 : ℕ) : ℝ)⁻¹ : ℂ) := by
  rw [completedNativeChiralCauchyFeature,
    completedNativeChiralCauchyFeature,
    ContinuousMap.inner_toLp]
  change
    (∫ x : unitInterval,
      (((Real.sqrt (x : ℝ) * (x : ℝ) ^ j : ℝ) : ℂ) *
        conj (((Real.sqrt (x : ℝ) * (x : ℝ) ^ i : ℝ) : ℂ)))) = _
  have hsubtype :
      (∫ x : unitInterval,
          (((Real.sqrt (x : ℝ) * (x : ℝ) ^ j : ℝ) : ℂ) *
            conj (((Real.sqrt (x : ℝ) * (x : ℝ) ^ i : ℝ) : ℂ)))) =
        ∫ x in Set.Icc (0 : ℝ) 1,
          (((Real.sqrt x * x ^ j : ℝ) : ℂ) *
            conj (((Real.sqrt x * x ^ i : ℝ) : ℂ))) := by
    simpa [unitInterval.volume_def] using
      (MeasureTheory.integral_subtype_comap
        (μ := (volume : Measure ℝ)) measurableSet_Icc
        (fun x : ℝ =>
          (((Real.sqrt x * x ^ j : ℝ) : ℂ) *
            conj (((Real.sqrt x * x ^ i : ℝ) : ℂ)))))
  rw [hsubtype]
  have hintegrand :
      (fun x : ℝ =>
          (((Real.sqrt x * x ^ j : ℝ) : ℂ) *
            conj (((Real.sqrt x * x ^ i : ℝ) : ℂ)))) =ᵐ[
        volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x : ℝ => ((x ^ (i + j + 1) : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hx0 : 0 ≤ x := hx.1
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [show Real.sqrt x * x ^ j * (Real.sqrt x * x ^ i) =
        (Real.sqrt x) ^ 2 * x ^ (i + j) by
          rw [pow_add]
          ring,
      Real.sq_sqrt hx0]
    rw [pow_succ]
    ring
  rw [integral_congr_ae hintegrand]
  have hsetIntegral :
      (∫ x in Set.Icc (0 : ℝ) 1,
          ((x ^ (i + j + 1) : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..1, ((x ^ (i + j + 1) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      MeasureTheory.setIntegral_congr_set Ioc_ae_eq_Icc]
  rw [hsetIntegral, intervalIntegral.integral_ofReal]
  rw [integral_pow]
  norm_num
  ring

/-- Radial Cauchy vector with the exact scale imposed by the shifted grid. -/
def completedNativeRadialChiralCauchyState
    (k n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) •
    completedNativeChiralCauchyFeature n

/-- The scaled carrier realizes `(k+1)/(i+j+2)` exactly. -/
theorem inner_completedNativeRadialChiralCauchyState
    (k i j : ℕ) :
    inner ℂ (completedNativeRadialChiralCauchyState k i)
        (completedNativeRadialChiralCauchyState k j) =
      ((((k : ℝ) + 1) * (((i + j + 2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
  unfold completedNativeRadialChiralCauchyState
  rw [inner_smul_left, inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  simp only [Complex.conj_ofReal]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  calc
    Real.sqrt ((k : ℝ) + 1) *
          (Real.sqrt ((k : ℝ) + 1) * (((i + j + 2 : ℕ) : ℝ)⁻¹)) =
        (Real.sqrt ((k : ℝ) + 1)) ^ 2 *
          (((i + j + 2 : ℕ) : ℝ)⁻¹) := by ring
    _ = ((k : ℝ) + 1) * (((i + j + 2 : ℕ) : ℝ)⁻¹) := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)]

/-! ## The radial multiplier defect -/

/-- The completed chiral quotient acting on one Cauchy feature. -/
def completedNativeRadialChiralMultiplierState
    (k n : ℕ) : CanonicalCompletedNativeChiralCauchyCarrier :=
  completedNativeHermiteBiehlerChiralQuotient
      (canonicalCompletedC3RadialTiltPoint k n) •
    completedNativeRadialChiralCauchyState k n

/-- Finite defect Gram of the radial chiral multiplier. -/
def canonicalCompletedNativeRadialChiralMultiplierDefectMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ
      (fun i : Fin N => completedNativeRadialChiralCauchyState k i) -
    Matrix.gram ℂ
      (fun i : Fin N => completedNativeRadialChiralMultiplierState k i)

/-- Entrywise form of the multiplier defect. -/
theorem canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply
    (k N : ℕ) (i j : Fin N) :
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N i j =
      ((((k : ℝ) + 1) *
          ((((i : ℕ) + (j : ℕ) + 2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) *
        (1 -
          conj (completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k i)) *
          completedNativeHermiteBiehlerChiralQuotient
            (canonicalCompletedC3RadialTiltPoint k j)) := by
  unfold canonicalCompletedNativeRadialChiralMultiplierDefectMatrix
    completedNativeRadialChiralMultiplierState
  simp only [Matrix.sub_apply, Matrix.gram_apply, inner_smul_left,
    inner_smul_right]
  rw [inner_completedNativeRadialChiralCauchyState]
  ring

/-- Exact spectral separation on the shifted imaginary grid. -/
theorem canonicalCompletedC3RadialTilt_separation_eq
    (k i j : ℕ) :
    canonicalCompletedC3RadialTiltPoint k j -
        conj (canonicalCompletedC3RadialTiltPoint k i) =
      Complex.I *
        (((((i + j + 2 : ℕ) : ℝ) * ((k : ℝ) + 1)⁻¹ : ℝ) : ℂ)) := by
  apply Complex.ext
  · simp [canonicalCompletedC3RadialTiltPoint,
      canonicalCompletedC3RadialTiltStep, canonicalGreenJetStep]
  · rw [Complex.sub_im, Complex.conj_im,
      canonicalCompletedC3RadialTiltPoint_im,
      canonicalCompletedC3RadialTiltPoint_im]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul]
    push_cast
    ring

/-- The quarter-turned reciprocal separation is the Cauchy Gram factor. -/
theorem canonicalCompletedC3RadialTilt_I_div_separation
    (k i j : ℕ) :
    Complex.I /
        (canonicalCompletedC3RadialTiltPoint k j -
          conj (canonicalCompletedC3RadialTiltPoint k i)) =
      ((((k : ℝ) + 1) * (((i + j + 2 : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) := by
  rw [canonicalCompletedC3RadialTilt_separation_eq]
  have hk : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (k : ℝ) + 1 ≠ 0)
  have hij : ((((i + j + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : ((i + j + 2 : ℕ) : ℝ) ≠ 0)
  push_cast
  field_simp [Complex.I_ne_zero, hk, hij]

/-- The abstract multiplier defect is exactly the radial Pick sample matrix.
This is the division by spectral separation realized as a Hilbert Gram, not
as an ad hoc scalar cancellation. -/
theorem canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect
    (k N : ℕ) :
    canonicalCompletedNativeRadialChiralPickSampleMatrix k N =
      canonicalCompletedNativeRadialChiralMultiplierDefectMatrix k N := by
  ext i j
  rw [canonicalCompletedNativeRadialChiralMultiplierDefectMatrix_apply]
  unfold canonicalCompletedNativeRadialChiralPickSampleMatrix
    completedNativeHermiteBiehlerChiralPickKernel
  simp only [Matrix.of_apply]
  rw [show
      Complex.I *
            (1 -
              conj (completedNativeHermiteBiehlerChiralQuotient
                (canonicalCompletedC3RadialTiltPoint k i)) *
              completedNativeHermiteBiehlerChiralQuotient
                (canonicalCompletedC3RadialTiltPoint k j)) /
          (canonicalCompletedC3RadialTiltPoint k j -
            conj (canonicalCompletedC3RadialTiltPoint k i)) =
        (Complex.I /
            (canonicalCompletedC3RadialTiltPoint k j -
              conj (canonicalCompletedC3RadialTiltPoint k i))) *
          (1 -
            conj (completedNativeHermiteBiehlerChiralQuotient
              (canonicalCompletedC3RadialTiltPoint k i)) *
            completedNativeHermiteBiehlerChiralQuotient
              (canonicalCompletedC3RadialTiltPoint k j)) by ring]
  rw [canonicalCompletedC3RadialTilt_I_div_separation]

/-! ## Contractive form of the Pick gate -/

/-- A difference of two finite Gram matrices is positive semidefinite exactly
when synthesis by the second family is contractive relative to synthesis by
the first family. -/
theorem gram_sub_gram_posSemidef_iff_synthesis_norm_le
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v w : ι → E) :
    (Matrix.gram ℂ v - Matrix.gram ℂ w).PosSemidef ↔
      ∀ c : ι → ℂ,
        ‖∑ i, c i • w i‖ ≤ ‖∑ i, c i • v i‖ := by
  constructor
  · intro h c
    have hquadratic := h.dotProduct_mulVec_nonneg c
    rw [Matrix.sub_mulVec, dotProduct_sub,
      Matrix.star_dotProduct_gram_mulVec,
      Matrix.star_dotProduct_gram_mulVec,
      RCLike.le_iff_re_im] at hquadratic
    have hsquares :
        ‖∑ i, c i • w i‖ ^ 2 ≤ ‖∑ i, c i • v i‖ ^ 2 := by
      have hnonneg :
          0 ≤ ‖∑ i, c i • v i‖ ^ 2 - ‖∑ i, c i • w i‖ ^ 2 := by
        simpa only [map_zero, map_sub, inner_self_eq_norm_sq] using
          hquadratic.1
      exact sub_nonneg.mp hnonneg
    exact
      (sq_le_sq₀ (norm_nonneg (∑ i, c i • w i))
        (norm_nonneg (∑ i, c i • v i))).mp hsquares
  · intro hcontractive
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.isHermitian_gram ℂ v).sub
        (Matrix.isHermitian_gram ℂ w))
    intro c
    rw [Matrix.sub_mulVec, dotProduct_sub,
      Matrix.star_dotProduct_gram_mulVec,
      Matrix.star_dotProduct_gram_mulVec,
      RCLike.le_iff_re_im]
    constructor
    · have hsquares :
          ‖∑ i, c i • w i‖ ^ 2 ≤ ‖∑ i, c i • v i‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg (∑ i, c i • w i))
          (norm_nonneg (∑ i, c i • v i))).mpr
            (hcontractive c)
      simpa only [map_zero, map_sub, inner_self_eq_norm_sq] using
        (sub_nonneg.mpr hsquares)
    · simp only [map_zero, map_sub, inner_self_im, sub_self]

/-- Congruence by a diagonal matrix with nonzero diagonal preserves and
reflects positive semidefiniteness. -/
theorem diagonal_congruence_posSemidef_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) (A : Matrix ι ι ℂ) :
    (Matrix.conjTranspose (Matrix.diagonal a) * A *
        Matrix.diagonal a).PosSemidef ↔
      A.PosSemidef := by
  constructor
  · intro h
    let inverseDiagonal : Matrix ι ι ℂ :=
      Matrix.diagonal (fun i => (a i)⁻¹)
    have hinverse := h.conjTranspose_mul_mul_same inverseDiagonal
    have hrecover :
        Matrix.conjTranspose inverseDiagonal *
              (Matrix.conjTranspose (Matrix.diagonal a) * A *
                Matrix.diagonal a) *
            inverseDiagonal = A := by
      ext i j
      simp [inverseDiagonal, Matrix.mul_assoc, ha]
    rw [hrecover] at hinverse
    exact hinverse
  · intro h
    exact h.conjTranspose_mul_mul_same (Matrix.diagonal a)

/-! ## Nonvanishing positive amplitude -/

/-- Scalar amplitude of the normalized positive Hermite--Biehler channel. -/
def completedNativeNormalizedPositiveChiralAmplitude (z : ℂ) : ℂ :=
  canonicalCompletedC3FullWronskianChiralNormalization z *
    completedNativePositiveHermiteBiehlerCoordinate z

/-- The positive scalar chiral kernel is a rank-one Gram with its exact
factor `1/2`. -/
theorem completedNativeNormalizedPositiveChiralTraceKernel_eq_amplitude
    (z w : ℂ) :
    completedNativeNormalizedPositiveChiralTraceKernel z w =
      (2 : ℂ)⁻¹ *
        conj (completedNativeNormalizedPositiveChiralAmplitude z) *
          completedNativeNormalizedPositiveChiralAmplitude w := by
  unfold completedNativeNormalizedPositiveChiralTraceKernel
    completedNativeNormalizedPositiveChiralTraceState
    completedNativeNormalizedPositiveChiralAmplitude
  rw [inner_smul_left, inner_smul_right,
    inner_completedScalarBoundaryPositivePolarization,
    completedNativeFNegFPrime_positiveCombination,
    completedNativeFNegFPrime_positiveCombination]
  simp only [RCLike.inner_apply, map_mul]
  ring

/-- The positive normalized amplitude is nonzero wherever both its
characteristic normalization and positive Hermite--Biehler coordinate are
regular. -/
theorem completedNativeNormalizedPositiveChiralAmplitude_ne_zero
    {z : ℂ}
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    completedNativeNormalizedPositiveChiralAmplitude z ≠ 0 := by
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
  exact mul_ne_zero
    (inv_ne_zero
      (mul_ne_zero
        (by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)) hzF))
    hzPositive

/-! ## Exact diagonal congruence with the completed dslope -/

/-- On a regular radial grid, the completed-native `dslope` sample matrix is
the positive-amplitude diagonal congruence of the chiral Pick matrix. -/
theorem canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    canonicalCompletedNativeRadialDslopeSampleMatrix k N =
      (2 : ℝ)⁻¹ •
        (Matrix.conjTranspose
              (Matrix.diagonal (fun i : Fin N =>
                completedNativeNormalizedPositiveChiralAmplitude
                  (canonicalCompletedC3RadialTiltPoint k i))) *
            canonicalCompletedNativeRadialChiralPickSampleMatrix k N *
          Matrix.diagonal (fun i : Fin N =>
            completedNativeNormalizedPositiveChiralAmplitude
              (canonicalCompletedC3RadialTiltPoint k i))) := by
  ext i j
  have hfactor :=
    canonicalCompletedNativePolarizedDslopeKernel_eq_positive_mul_pick
      (hregular i).1 (hregular i).2.1 (hregular j).2.1
      (sub_ne_zero.mp
        (canonicalCompletedC3RadialTilt_separation_ne_zero k i j))
      (hregular i).2.2 (hregular j).2.2
  rw [canonicalCompletedNativeRadialDslopeSampleMatrix,
    Matrix.of_apply, hfactor,
    completedNativeNormalizedPositiveChiralTraceKernel_eq_amplitude]
  simp only [Matrix.smul_apply, Matrix.mul_diagonal,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Pi.star_apply, canonicalCompletedNativeRadialChiralPickSampleMatrix,
    Matrix.of_apply, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_ofNat, starRingEnd_apply]
  ring

/-- Because the positive amplitude is nonzero, the radial `dslope` and Pick
sample matrices have exactly the same positive-semidefinite status. -/
theorem
    canonicalCompletedNativeRadialDslopeSampleMatrix_posSemidef_iff_pick
    (k N : ℕ)
    (hregular : ∀ i : Fin N,
      canonicalCompletedC3RadialTiltPoint k i ∈
          completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate
            (canonicalCompletedC3RadialTiltPoint k i) ≠ 0) :
    (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef ↔
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k N).PosSemidef := by
  rw [canonicalCompletedNativeRadialDslopeSampleMatrix_eq_pickCongruence
    k N hregular]
  let amplitude : Fin N → ℂ := fun i =>
    completedNativeNormalizedPositiveChiralAmplitude
      (canonicalCompletedC3RadialTiltPoint k i)
  have hamplitude : ∀ i, amplitude i ≠ 0 := fun i =>
    completedNativeNormalizedPositiveChiralAmplitude_ne_zero
      (hregular i).2.1 (hregular i).2.2
  let congruence : Matrix (Fin N) (Fin N) ℂ :=
    Matrix.conjTranspose (Matrix.diagonal amplitude) *
      canonicalCompletedNativeRadialChiralPickSampleMatrix k N *
        Matrix.diagonal amplitude
  have hcongruence :
      congruence.PosSemidef ↔
        (canonicalCompletedNativeRadialChiralPickSampleMatrix k N).PosSemidef := by
    exact diagonal_congruence_posSemidef_iff amplitude hamplitude _
  constructor
  · intro hscaled
    have htwice := hscaled.smul (show (0 : ℝ) ≤ 2 by norm_num)
    have hcongruencePos : congruence.PosSemidef := by
      simpa [congruence, amplitude, smul_smul] using htwice
    exact hcongruence.mp hcongruencePos
  · intro hPick
    have hcongruencePos : congruence.PosSemidef := hcongruence.mpr hPick
    simpa [congruence, amplitude] using
      hcongruencePos.smul (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by positivity)

/-- Finite-combination contractivity of the completed chiral quotient on the
canonical radial Cauchy family. -/
def CanonicalCompletedNativeRadialChiralMultiplierContractiveAt
    (k N : ℕ) : Prop :=
  ∀ c : Fin N → ℂ,
    ‖∑ i, c i • completedNativeRadialChiralMultiplierState k i‖ ≤
      ‖∑ i, c i • completedNativeRadialChiralCauchyState k i‖

/-- On every finite radial grid, multiplier contractivity is exactly Pick
positive semidefiniteness. -/
theorem
    canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
    (k N : ℕ) :
    CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N ↔
      (canonicalCompletedNativeRadialChiralPickSampleMatrix k N).PosSemidef := by
  rw [canonicalCompletedNativeRadialChiralPickSampleMatrix_eq_multiplierDefect]
  unfold CanonicalCompletedNativeRadialChiralMultiplierContractiveAt
    canonicalCompletedNativeRadialChiralMultiplierDefectMatrix
  exact
    (gram_sub_gram_posSemidef_iff_synthesis_norm_le
      (fun i : Fin N => completedNativeRadialChiralCauchyState k i)
      (fun i : Fin N => completedNativeRadialChiralMultiplierState k i)).symm

/-- All-order radial multiplier gate: every finite family is eventually
contractive along the canonical shrinking grid. -/
def CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in atTop,
    CanonicalCompletedNativeRadialChiralMultiplierContractiveAt k N

/-- The vector contraction gate and the radial Pick gate are definitionally
the same finite quadratic inequalities after the Cauchy realization. -/
theorem
    canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_pick :
    CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive ↔
      CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite := by
  constructor
  · intro h N
    filter_upwards [h N] with k hk
    exact
      (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
        k N).mp hk
  · intro h N
    filter_upwards [h N] with k hk
    exact
      (canonicalCompletedNativeRadialChiralMultiplierContractiveAt_iff_pickPosSemidef
        k N).mpr hk

/-- Eventual positivity of the completed-native `dslope` on the canonical
shifted radial grids. -/
def CanonicalCompletedNativeRadialDslopeEventuallyPosSemidefinite : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in atTop,
    (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef

/-- The concrete multiplier contraction is exactly eventual radial `dslope`
positivity.  The reverse direction uses the nonvanishing positive amplitude
on the centered germ, so no information is lost in the diagonal congruence. -/
theorem
    canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_dslope :
    CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive ↔
      CanonicalCompletedNativeRadialDslopeEventuallyPosSemidefinite := by
  constructor
  · intro hcontractive
    have hPick :
        CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite :=
      canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_pick.mp
        hcontractive
    intro N
    exact
      canonicalCompletedNativeRadialDslopeSampleMatrix_eventually_posSemidef_of_chiralPick
        hPick N
  · intro hdslope
    apply
      canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_pick.mpr
    intro N
    have hregular : ∀ᶠ k : ℕ in atTop, ∀ i : Fin N,
        canonicalCompletedC3RadialTiltPoint k i ∈
            completedNativeHeightDomain ∧
          completedNativeOperatorCharacteristic
              (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 ∧
            completedNativePositiveHermiteBiehlerCoordinate
              (canonicalCompletedC3RadialTiltPoint k i) ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      exact (canonicalCompletedC3RadialTiltPoint_tendsto_zero i).eventually
        completedNativeChiralPickFactorization_eventually_regular
    filter_upwards [hdslope N, hregular] with k hk hreg
    exact
      (canonicalCompletedNativeRadialDslopeSampleMatrix_posSemidef_iff_pick
        k N hreg).mp hk

/-- Contractivity of the concrete chiral multiplier supplies the closed
positive forms of both completed-native Hankel towers. -/
theorem
    canonicalCompletedNativeStieltjesPosSemidefinite_of_radialChiralMultiplier
    (hcontractive :
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive) :
    CanonicalCompletedNativeStieltjesPosSemidefinite :=
  canonicalCompletedNativeStieltjesPosSemidefinite_of_radialChiralPick
    (canonicalCompletedNativeRadialChiralMultiplierEventuallyContractive_iff_pick.mp
      hcontractive)

/-- The multiplier route reaches the strict Stieltjes gate once the already
isolated finite-section nondegeneracy condition is supplied. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier
    (hcontractive :
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeStieltjesPositivity := by
  rw [
    canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate]
  exact
    ⟨canonicalCompletedNativeStieltjesPosSemidefinite_of_radialChiralMultiplier
        hcontractive,
      hnondegenerate⟩

/-- Concrete HP carrier obtained from radial chiral multiplier contractivity
and finite moment nondegeneracy. -/
theorem completedNativeRealHPCarrierCertificate_of_radialChiralMultiplier
    (hcontractive :
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier
          hcontractive hnondegenerate)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier
      hcontractive hnondegenerate)

/-- End-to-end conditional endpoint of route B: the concrete radial
multiplier contraction and finite-section nondegeneracy feed the existing
self-adjoint Jacobi confinement theorem. -/
theorem completedNativeOperator_zero_im_eq_zero_of_radialChiralMultiplier
    (hcontractive :
      CanonicalCompletedNativeRadialChiralMultiplierEventuallyContractive)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_radialChiralMultiplier
      hcontractive hnondegenerate)
    hzDomain hzero

end

end CarrySelfAdjointOperator

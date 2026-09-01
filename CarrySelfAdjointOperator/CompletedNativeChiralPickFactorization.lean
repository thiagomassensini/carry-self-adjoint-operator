import CarrySelfAdjointOperator.CompletedC3CausalChiralPolarizedAudit
import CarrySelfAdjointOperator.CompletedNativeDslopeSamplePositivity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Chiral Pick factorization of the completed-native divided slope

The scalar Hermite--Biehler channels already give the exact signed identity

`i * (K₊(z,w) - K₋(z,w)) = (w - conj z) * dslope(z,w)`.

This module removes the remaining indefinite notation without assuming a
positivity theorem.  Away from zeros of the positive chiral coordinate, the
negative channel is the positive channel multiplied by the two copies of the
canonical chiral quotient.  Consequently `dslope` factors exactly as a
positive rank-one Gram kernel times the upper-half-plane Pick kernel of that
quotient.

Thus the all-order positivity problem is reduced to a genuine polarized
contractivity statement.  Pointwise or diagonal norm dominance is not used
as a substitute for kernel positivity.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The canonical chiral quotient -/

/-- Ratio of the negative and positive completed Hermite--Biehler
coordinates.  It is kept as total complex division; the exact factorization
below records explicitly where the positive coordinate must be nonzero. -/
def completedNativeHermiteBiehlerChiralQuotient (z : ℂ) : ℂ :=
  completedNativeNegativeHermiteBiehlerCoordinate z /
    completedNativePositiveHermiteBiehlerCoordinate z

/-- Centered evenness pins the chiral quotient to `-1`. -/
@[simp] theorem completedNativeHermiteBiehlerChiralQuotient_zero :
    completedNativeHermiteBiehlerChiralQuotient 0 = -1 := by
  unfold completedNativeHermiteBiehlerChiralQuotient
  rw [completedNativePositiveHermiteBiehlerCoordinate_zero,
    completedNativeNegativeHermiteBiehlerCoordinate_zero]
  have hF := completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp [hF]

/-- The positive Hermite--Biehler coordinate is nonzero throughout a
neighborhood of the center.  Hence the chiral quotient used for the all-order
germ does not require an extra denominator hypothesis. -/
theorem completedNativePositiveHermiteBiehlerCoordinate_eventually_ne_zero :
    ∀ᶠ z : ℂ in nhds 0,
      completedNativePositiveHermiteBiehlerCoordinate z ≠ 0 := by
  have hFanalytic :=
    completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain
  have hcontinuous :
      ContinuousAt completedNativePositiveHermiteBiehlerCoordinate 0 := by
    unfold completedNativePositiveHermiteBiehlerCoordinate
    exact hFanalytic.deriv.neg.continuousAt.add
      (continuousAt_const.mul hFanalytic.continuousAt)
  have hcenter :
      completedNativePositiveHermiteBiehlerCoordinate 0 ≠ 0 := by
    rw [completedNativePositiveHermiteBiehlerCoordinate_zero]
    exact mul_ne_zero Complex.I_ne_zero
      completedNativeOperatorCharacteristic_zero_ne_zero
  exact hcontinuous.eventually_ne hcenter

/-- All regularity conditions used by the chiral Pick factorization hold
simultaneously near the centered germ: strip membership, nonvanishing of the
completed characteristic, and nonvanishing of the positive chiral
coordinate. -/
theorem completedNativeChiralPickFactorization_eventually_regular :
    ∀ᶠ z : ℂ in nhds 0,
      z ∈ completedNativeHeightDomain ∧
        completedNativeOperatorCharacteristic z ≠ 0 ∧
          completedNativePositiveHermiteBiehlerCoordinate z ≠ 0 := by
  have hdomain : ∀ᶠ z : ℂ in nhds 0,
      z ∈ completedNativeHeightDomain :=
    isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain
  have hF : ∀ᶠ z : ℂ in nhds 0,
      completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hdomain, hF,
    completedNativePositiveHermiteBiehlerCoordinate_eventually_ne_zero]
      with z hzDomain hzF hzPositive
  exact ⟨hzDomain, hzF, hzPositive⟩

/-- The normalized negative chiral Gram is obtained from the positive one by
the two copies of the chiral quotient.  This is an exact scalar identity,
not a comparison of diagonal norms. -/
theorem completedNativeNormalizedNegativeChiralTraceKernel_eq_quotient_mul_positive
    {z w : ℂ}
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hwPositive : completedNativePositiveHermiteBiehlerCoordinate w ≠ 0) :
    completedNativeNormalizedNegativeChiralTraceKernel z w =
      conj (completedNativeHermiteBiehlerChiralQuotient z) *
        completedNativeHermiteBiehlerChiralQuotient w *
          completedNativeNormalizedPositiveChiralTraceKernel z w := by
  have hzQuotientConj :
      conj (completedNativeHermiteBiehlerChiralQuotient z) *
          conj (completedNativePositiveHermiteBiehlerCoordinate z) =
        conj (completedNativeNegativeHermiteBiehlerCoordinate z) := by
    unfold completedNativeHermiteBiehlerChiralQuotient
    rw [div_eq_mul_inv, map_mul, map_inv₀]
    exact div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).2 hzPositive)
  have hwQuotient :
      completedNativeHermiteBiehlerChiralQuotient w *
          completedNativePositiveHermiteBiehlerCoordinate w =
        completedNativeNegativeHermiteBiehlerCoordinate w := by
    unfold completedNativeHermiteBiehlerChiralQuotient
    exact div_mul_cancel₀ _ hwPositive
  unfold completedNativeNormalizedNegativeChiralTraceKernel
    completedNativeNormalizedPositiveChiralTraceKernel
    completedNativeNormalizedNegativeChiralTraceState
    completedNativeNormalizedPositiveChiralTraceState
  simp only [inner_smul_left, inner_smul_right]
  rw [inner_completedScalarBoundaryNegativePolarization,
    inner_completedScalarBoundaryPositivePolarization,
    completedNativeFNegFPrime_negativeCombination,
    completedNativeFNegFPrime_negativeCombination,
    completedNativeFNegFPrime_positiveCombination,
    completedNativeFNegFPrime_positiveCombination]
  simp only [RCLike.inner_apply]
  rw [← hzQuotientConj, ← hwQuotient]
  ring

/-- Signed chiral difference after removing the common positive channel. -/
theorem completedNativeNormalizedChiralDifference_eq_positive_mul_quotientDefect
    {z w : ℂ}
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hwPositive : completedNativePositiveHermiteBiehlerCoordinate w ≠ 0) :
    completedNativeNormalizedPositiveChiralTraceKernel z w -
        completedNativeNormalizedNegativeChiralTraceKernel z w =
      completedNativeNormalizedPositiveChiralTraceKernel z w *
        (1 - conj (completedNativeHermiteBiehlerChiralQuotient z) *
          completedNativeHermiteBiehlerChiralQuotient w) := by
  rw [completedNativeNormalizedNegativeChiralTraceKernel_eq_quotient_mul_positive
    hzPositive hwPositive]
  ring

/-! ## Pick kernel and exact dslope factorization -/

/-- Upper-half-plane Pick kernel of the canonical chiral quotient, with the
quarter turn forced by the Wronskian orientation. -/
def completedNativeHermiteBiehlerChiralPickKernel (z w : ℂ) : ℂ :=
  Complex.I *
    (1 - conj (completedNativeHermiteBiehlerChiralQuotient z) *
      completedNativeHermiteBiehlerChiralQuotient w) /
        (w - conj z)

/-- The completed-native divided slope is exactly the Hadamard product of
the positive chiral Gram and the Pick kernel of the chiral quotient. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_eq_positive_mul_pick
    {z w : ℂ}
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0)
    (hsep : w ≠ conj z)
    (hzPositive : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0)
    (hwPositive : completedNativePositiveHermiteBiehlerCoordinate w ≠ 0) :
    canonicalCompletedNativePolarizedDslopeKernel z w =
      completedNativeNormalizedPositiveChiralTraceKernel z w *
        completedNativeHermiteBiehlerChiralPickKernel z w := by
  rw [completedNativePolarizedDslopeKernel_eq_scalarChiralDifference_div
      hzStrip hzF hwF hsep,
    completedNativeNormalizedChiralDifference_eq_positive_mul_quotientDefect
      hzPositive hwPositive]
  unfold completedNativeHermiteBiehlerChiralPickKernel
  ring

/-! ## Finite polarized positivity transfer -/

/-- A positive Pick matrix for the chiral quotient gives a positive matrix
of completed-native divided slopes on the same finite upper-half-plane
sample.  The transfer is the Schur product theorem; no Gram equality is
assumed. -/
theorem canonicalCompletedNativePolarizedDslopeKernel_posSemidef_of_chiralPick
    {ι : Type*} [Finite ι]
    (point : ι → ℂ)
    (hstrip : ∀ i, operatorHeightParameter (point i) ∈ genuineCriticalStrip)
    (hF : ∀ i, completedNativeOperatorCharacteristic (point i) ≠ 0)
    (hsep : ∀ i j, point j ≠ conj (point i))
    (hpositive : ∀ i,
      completedNativePositiveHermiteBiehlerCoordinate (point i) ≠ 0)
    (hPick :
      (Matrix.of fun i j =>
        completedNativeHermiteBiehlerChiralPickKernel
          (point i) (point j)).PosSemidef) :
    (Matrix.of fun i j =>
      canonicalCompletedNativePolarizedDslopeKernel
        (point i) (point j)).PosSemidef := by
  have hPositiveGram :
      (Matrix.of fun i j =>
        completedNativeNormalizedPositiveChiralTraceKernel
          (point i) (point j)).PosSemidef :=
    completedNativeNormalizedPositiveChiralTraceKernel_posSemidef point
  have hProduct := hPositiveGram.hadamard hPick
  have hmatrix :
      (Matrix.of fun i j =>
        canonicalCompletedNativePolarizedDslopeKernel
          (point i) (point j)) =
      (Matrix.of fun i j =>
        completedNativeNormalizedPositiveChiralTraceKernel
          (point i) (point j)) ⊙
      (Matrix.of fun i j =>
        completedNativeHermiteBiehlerChiralPickKernel
          (point i) (point j)) := by
    ext i j
    rw [Matrix.hadamard_apply]
    exact canonicalCompletedNativePolarizedDslopeKernel_eq_positive_mul_pick
      (hstrip i) (hF i) (hF j) (hsep i j)
        (hpositive i) (hpositive j)
  rw [hmatrix]
  exact hProduct

/-! ## Canonical radial specialization -/

/-- Chiral Pick matrix on the same shifted radial grid used by the completed
Gamma and `dslope` all-order limits. -/
def canonicalCompletedNativeRadialChiralPickSampleMatrix
    (k N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    completedNativeHermiteBiehlerChiralPickKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)

/-- Minimal radial Pick positivity statement: for each finite section, the
canonical shrinking upper-half-plane samples are eventually positive
semidefinite.  This definition does not assert the property. -/
def CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
    (canonicalCompletedNativeRadialChiralPickSampleMatrix k N).PosSemidef

/-- Eventual radial Pick positivity transfers to the completed-native radial
`dslope` samples with no extra strip, zero, or denominator premise.  All
regularity conditions follow from the centered germ. -/
theorem
    canonicalCompletedNativeRadialDslopeSampleMatrix_eventually_posSemidef_of_chiralPick
    (hPick :
      CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite)
    (N : ℕ) :
    ∀ᶠ k : ℕ in Filter.atTop,
      (canonicalCompletedNativeRadialDslopeSampleMatrix k N).PosSemidef := by
  have hregular : ∀ᶠ k : ℕ in Filter.atTop, ∀ i : Fin N,
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
  filter_upwards [hPick N, hregular] with k hkPick hkRegular
  unfold canonicalCompletedNativeRadialDslopeSampleMatrix
  apply canonicalCompletedNativePolarizedDslopeKernel_posSemidef_of_chiralPick
    (point := fun i : Fin N => canonicalCompletedC3RadialTiltPoint k i)
  · intro i
    exact (hkRegular i).1
  · intro i
    exact (hkRegular i).2.1
  · intro i j
    exact sub_ne_zero.mp
      (canonicalCompletedC3RadialTilt_separation_ne_zero k i j)
  · intro i
    exact (hkRegular i).2.2
  · simpa [canonicalCompletedNativeRadialChiralPickSampleMatrix] using hkPick

end

end CarrySelfAdjointOperator

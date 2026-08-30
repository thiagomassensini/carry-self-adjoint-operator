import CarrySelfAdjointOperator.CompletedC3FinalReadoutKernelBridge
import CarrySelfAdjointOperator.CanonicalCompletedNativeStieltjesOperator
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Sampled positivity route for the completed-native dslope

This file isolates the finite algebra behind the real-axis positivity route.
Normalized forward differences are obtained from a sampled kernel matrix by
one lower-triangular congruence.  Consequently positivity of the sampled
`dslope` kernel passes to every finite forward-difference matrix before the
coefficient limit is taken.

No Green carrier, Stieltjes certificate, zero-set statement, or spectral
hypothesis is used here.
-/

namespace CarrySelfAdjointOperator

noncomputable section

/-- Real signed-binomial coefficient of the normalized forward difference of
order `order`, evaluated at sample `index`. -/
def completedGreenRealForwardDifferenceCoefficient
    (step : ℝ) (order index : ℕ) : ℝ :=
  (((order.factorial : ℝ) * step ^ order)⁻¹) *
    ((((-1 : ℤ) ^ (order - index) * order.choose index : ℤ) : ℝ))

@[simp] theorem completedGreenRealForwardDifferenceCoefficient_eq_zero_of_lt
    {step : ℝ} {order index : ℕ} (h : order < index) :
    completedGreenRealForwardDifferenceCoefficient step order index = 0 := by
  simp [completedGreenRealForwardDifferenceCoefficient,
    Nat.choose_eq_zero_of_lt h]

theorem sum_range_completedGreenRealForwardDifferenceCoefficient_mul
    {N : ℕ} (step : ℝ) (order : Fin N) (f : ℕ → ℝ) :
    (∑ index ∈ Finset.range N,
        completedGreenRealForwardDifferenceCoefficient
          step order index * f index) =
      ∑ index ∈ Finset.range ((order : ℕ) + 1),
        completedGreenRealForwardDifferenceCoefficient
          step order index * f index := by
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_iff.mpr order.isLt)
  · intro index hindexN hindexOrder
    have hlt : (order : ℕ) < index := by
      have hnot : ¬index < (order : ℕ) + 1 := by
        simpa only [Finset.mem_range] using hindexOrder
      omega
    simp [completedGreenRealForwardDifferenceCoefficient_eq_zero_of_lt hlt]

theorem sum_fin_completedGreenRealForwardDifferenceCoefficient_mul
    {N : ℕ} (step : ℝ) (order : Fin N) (f : ℕ → ℝ) :
    (∑ index : Fin N,
        completedGreenRealForwardDifferenceCoefficient
          step order index * f index) =
      ∑ index ∈ Finset.range ((order : ℕ) + 1),
        completedGreenRealForwardDifferenceCoefficient
          step order index * f index := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ index ∈ Finset.range N,
        if h : index < N then
          completedGreenRealForwardDifferenceCoefficient
            step order (⟨index, h⟩ : Fin N) * f (⟨index, h⟩ : Fin N)
        else 0) =
      ∑ index ∈ Finset.range N,
        completedGreenRealForwardDifferenceCoefficient
          step order index * f index := by
            apply Finset.sum_congr rfl
            intro index hindex
            rw [dif_pos (Finset.mem_range.mp hindex)]
    _ = _ :=
      sum_range_completedGreenRealForwardDifferenceCoefficient_mul
        step order f

/-- Lower-triangular matrix taking the first `N` sampled values to the first
`N` normalized forward differences.  Rows index samples and columns index
difference orders. -/
def completedGreenRealForwardDifferenceTransform
    (step : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun index order ↦
    completedGreenRealForwardDifferenceCoefficient step order index

/-- Real part of a complex kernel sampled on the first `N` points of one
real ray. -/
def completedGreenRealKernelSampleMatrix
    (kernel : ℂ → ℂ → ℂ) (step : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦
    (kernel (((i : ℕ) : ℂ) * (step : ℂ))
      (((j : ℕ) : ℂ) * (step : ℂ))).re

/-- Congruence of the sampled kernel by the normalized forward-difference
transform. -/
def completedGreenRealKernelForwardDifferenceMatrix
    (kernel : ℂ → ℂ → ℂ) (step : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  let transform := completedGreenRealForwardDifferenceTransform step N
  transform.conjTranspose *
    completedGreenRealKernelSampleMatrix kernel step N * transform

/-- Sampled kernel positivity survives the complete normalized
forward-difference transform. -/
theorem completedGreenRealKernelForwardDifferenceMatrix_posSemidef
    {kernel : ℂ → ℂ → ℂ} {step : ℝ} {N : ℕ}
    (hsample :
      (completedGreenRealKernelSampleMatrix kernel step N).PosSemidef) :
    (completedGreenRealKernelForwardDifferenceMatrix
      kernel step N).PosSemidef := by
  simpa [completedGreenRealKernelForwardDifferenceMatrix] using
    hsample.conjTranspose_mul_mul_same
      (completedGreenRealForwardDifferenceTransform step N)

/-- The congruence entry at orders `p,q` is exactly the real part of the
corresponding normalized complex forward difference. -/
theorem completedGreenRealKernelForwardDifferenceMatrix_apply
    (kernel : ℂ → ℂ → ℂ) (step : ℝ) (N : ℕ) (p q : Fin N) :
    completedGreenRealKernelForwardDifferenceMatrix kernel step N p q =
      (completedGreenKernelForwardDifference kernel (step : ℂ) p q).re := by
  classical
  unfold completedGreenRealKernelForwardDifferenceMatrix
    completedGreenRealForwardDifferenceTransform
    completedGreenRealKernelSampleMatrix
    completedGreenKernelForwardDifference
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  let sample : ℕ → ℕ → ℝ := fun i j ↦
    (kernel ((i : ℂ) * (step : ℂ))
      ((j : ℂ) * (step : ℂ))).re
  change
    (∑ j : Fin N,
        (∑ i : Fin N,
          completedGreenRealForwardDifferenceCoefficient step p i *
            sample i j) *
          completedGreenRealForwardDifferenceCoefficient step q j) = _
  rw [show (∑ j : Fin N,
        (∑ i : Fin N,
          completedGreenRealForwardDifferenceCoefficient step p i *
            sample i j) *
          completedGreenRealForwardDifferenceCoefficient step q j) =
      ∑ j : Fin N,
        completedGreenRealForwardDifferenceCoefficient step q j *
          (∑ i : Fin N,
            completedGreenRealForwardDifferenceCoefficient step p i *
              sample i j) by
        apply Finset.sum_congr rfl
        intro j _
        ring]
  rw [sum_fin_completedGreenRealForwardDifferenceCoefficient_mul
    step q (fun j ↦ ∑ i : Fin N,
      completedGreenRealForwardDifferenceCoefficient step p i * sample i j)]
  have hinner :
      (∑ j ∈ Finset.range ((q : ℕ) + 1),
        completedGreenRealForwardDifferenceCoefficient step q j *
          ∑ i : Fin N,
            completedGreenRealForwardDifferenceCoefficient step p i *
              sample i j) =
        ∑ j ∈ Finset.range ((q : ℕ) + 1),
          completedGreenRealForwardDifferenceCoefficient step q j *
            ∑ i ∈ Finset.range ((p : ℕ) + 1),
              completedGreenRealForwardDifferenceCoefficient step p i *
                sample i j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [sum_fin_completedGreenRealForwardDifferenceCoefficient_mul
      step p (fun i ↦ sample i j)]
  rw [hinner]
  let realSum : ℝ :=
    ∑ j ∈ Finset.range ((q : ℕ) + 1),
      completedGreenRealForwardDifferenceCoefficient step q j *
        ∑ i ∈ Finset.range ((p : ℕ) + 1),
          completedGreenRealForwardDifferenceCoefficient step p i *
            sample i j
  change realSum = _
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  simp_rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zero_add]
  have hnormalization (order : ℕ) :
      (((order.factorial : ℂ) * (step : ℂ) ^ order)⁻¹) =
        ((((order.factorial : ℝ) * step ^ order)⁻¹ : ℝ) : ℂ) := by
    norm_cast
  have hintCast (value : ℤ) :
      (value : ℂ) = ((value : ℝ) : ℂ) := by
    norm_cast
  simp_rw [hnormalization]
  simp only [Complex.conj_ofReal, zsmul_eq_mul]
  simp_rw [hintCast]
  simp_rw [Finset.mul_sum]
  simp only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero]
  unfold realSum sample
  simp only [completedGreenRealForwardDifferenceCoefficient]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hsampleArgument (index : ℕ) :
      (index : ℂ) * (step : ℂ) =
        (step : ℂ) * (index : ℂ) := by
    ring
  simp_rw [hsampleArgument]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-! ## Specialization to the completed-native dslope -/

/-- Real step underlying `canonicalGreenJetStep`. -/
def canonicalGreenJetRealStep (k : ℕ) : ℝ :=
  ((k : ℝ) + 1)⁻¹

@[simp] theorem canonicalGreenJetRealStep_coe (k : ℕ) :
    (canonicalGreenJetRealStep k : ℂ) = canonicalGreenJetStep k := by
  simp [canonicalGreenJetRealStep, canonicalGreenJetStep]

/-- The completed-native divided-slope kernel, before taking real parts in a
sample matrix. -/
def canonicalCompletedNativeDslopeKernel (x z : ℂ) : ℂ :=
  dslope
    (completedGreenNormalizedResponse
      completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion) x z

/-- Concrete positivity property of all finite real-ray sample matrices of
the completed-native `dslope`.  This is a kernel statement, not a carrier or
moment certificate. -/
def CanonicalCompletedNativeDslopeSamplePosSemidefinite : Prop :=
  ∀ k N : ℕ,
    (completedGreenRealKernelSampleMatrix
      canonicalCompletedNativeDslopeKernel
      (canonicalGreenJetRealStep k) N).PosSemidef

/-- Minimal sample-positivity input needed by the coefficient limit.  For
each fixed matrix order, only the canonical grids sufficiently close to the
center have to be positive semidefinite. -/
def CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in Filter.atTop,
    (completedGreenRealKernelSampleMatrix
      canonicalCompletedNativeDslopeKernel
      (canonicalGreenJetRealStep k) N).PosSemidef

/-- The first sampled block has no cutoff dependence: its unique entry is the
zeroth completed-native logarithmic moment. -/
theorem canonicalCompletedNativeDslopeSampleMatrix_one
    (step : ℝ) :
    completedGreenRealKernelSampleMatrix
        canonicalCompletedNativeDslopeKernel step 1 =
      Matrix.diagonal (fun _ : Fin 1 ↦
        canonicalCompletedNativeLogDerivativeMoment 0) := by
  ext i j
  fin_cases i
  fin_cases j
  have hcoefficient :=
    completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized 0 0
  have hreal := congrArg Complex.re hcoefficient
  simpa [completedGreenRealKernelSampleMatrix,
    canonicalCompletedNativeDslopeKernel, dslope_same,
    completedNativeGreenResponseTaylorCoefficient, iteratedDeriv_one,
    polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient] using hreal

/-- Consequently the first sampled positivity obligation is exactly the
nonnegativity of the zeroth canonical moment. -/
theorem canonicalCompletedNativeDslopeSampleMatrix_one_posSemidef_iff
    (step : ℝ) :
    (completedGreenRealKernelSampleMatrix
      canonicalCompletedNativeDslopeKernel step 1).PosSemidef ↔
      0 ≤ canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [canonicalCompletedNativeDslopeSampleMatrix_one,
    Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    exact h 0
  · intro h _
    exact h

/-- Pointwise sample positivity implies its minimal eventual form. -/
theorem CanonicalCompletedNativeDslopeSamplePosSemidefinite.eventually
    (hdslope : CanonicalCompletedNativeDslopeSamplePosSemidefinite) :
    CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite := by
  intro N
  exact Filter.Eventually.of_forall fun k ↦ hdslope k N

/-- Even order embedded in the common first-`2N` forward-difference block. -/
def completedGreenEvenOrderIndex {N : ℕ} (i : Fin N) : Fin (2 * N) :=
  ⟨2 * (i : ℕ), by omega⟩

/-- Odd order embedded in the common first-`2N` forward-difference block. -/
def completedGreenOddOrderIndex {N : ℕ} (i : Fin N) : Fin (2 * N) :=
  ⟨2 * (i : ℕ) + 1, by omega⟩

/-- Positivity of every finite sampled `dslope` matrix passes through the
triangular forward-difference congruence and the coefficient limit to both
canonical Hankel towers. -/
theorem canonicalCompletedNativeHankelPair_posSemidef_of_dslopeSamples
    (hdslope : CanonicalCompletedNativeDslopeSamplePosSemidefinite)
    (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosSemidef ∧
      (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N).PosSemidef := by
  let transformed (k : ℕ) :=
    completedGreenRealKernelForwardDifferenceMatrix
      canonicalCompletedNativeDslopeKernel
      (canonicalGreenJetRealStep k) (2 * N)
  have htransformed (k : ℕ) : (transformed k).PosSemidef := by
    exact completedGreenRealKernelForwardDifferenceMatrix_posSemidef
      (hdslope k (2 * N))
  constructor
  · apply matrixPosSemidef_of_tendsto_entrywise
      (A := fun k ↦ (transformed k).submatrix
        completedGreenEvenOrderIndex completedGreenEvenOrderIndex)
    · intro k
      exact (htransformed k).submatrix completedGreenEvenOrderIndex
    · intro i j
      rw [show (fun k ↦
          (transformed k).submatrix
            completedGreenEvenOrderIndex completedGreenEvenOrderIndex i j) =
        fun k ↦
          (completedGreenKernelForwardDifference
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetStep k) (2 * (i : ℕ)) (2 * (j : ℕ))).re by
          funext k
          rw [show canonicalGreenJetStep k =
              (canonicalGreenJetRealStep k : ℂ) by simp]
          exact completedGreenRealKernelForwardDifferenceMatrix_apply
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetRealStep k) (2 * N)
            (completedGreenEvenOrderIndex i)
            (completedGreenEvenOrderIndex j)]
      change Filter.Tendsto
        (fun k ↦
          (completedGreenKernelForwardDifference
            (fun x z ↦ dslope
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) x z)
            (canonicalGreenJetStep k) (2 * (i : ℕ))
              (2 * (j : ℕ))).re)
        Filter.atTop
        (nhds (hankelGram
          canonicalCompletedNativeLogDerivativeMoment N i j))
      simpa [hankelGram,
        completedGreenParityOrder, greenWronskianMomentKernel] using
        completedNativeGreenKernelForwardDifference_dslope_re_tendsto
          (Sum.inl (i : ℕ)) (Sum.inl (j : ℕ))
  · apply matrixPosSemidef_of_tendsto_entrywise
      (A := fun k ↦ (transformed k).submatrix
        completedGreenOddOrderIndex completedGreenOddOrderIndex)
    · intro k
      exact (htransformed k).submatrix completedGreenOddOrderIndex
    · intro i j
      rw [show (fun k ↦
          (transformed k).submatrix
            completedGreenOddOrderIndex completedGreenOddOrderIndex i j) =
        fun k ↦
          (completedGreenKernelForwardDifference
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetStep k) (2 * (i : ℕ) + 1)
              (2 * (j : ℕ) + 1)).re by
          funext k
          rw [show canonicalGreenJetStep k =
              (canonicalGreenJetRealStep k : ℂ) by simp]
          exact completedGreenRealKernelForwardDifferenceMatrix_apply
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetRealStep k) (2 * N)
            (completedGreenOddOrderIndex i)
            (completedGreenOddOrderIndex j)]
      change Filter.Tendsto
        (fun k ↦
          (completedGreenKernelForwardDifference
            (fun x z ↦ dslope
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) x z)
            (canonicalGreenJetStep k) (2 * (i : ℕ) + 1)
              (2 * (j : ℕ) + 1)).re)
        Filter.atTop
        (nhds (shiftedHankel
          canonicalCompletedNativeLogDerivativeMoment N i j))
      simpa [shiftedHankel,
        completedGreenParityOrder, greenWronskianMomentKernel] using
        completedNativeGreenKernelForwardDifference_dslope_re_tendsto
          (Sum.inr (i : ℕ)) (Sum.inr (j : ℕ))

/-- Eventual positive semidefiniteness is sufficient: a finite initial part
of the shrinking-grid sequence has no effect on its coefficient limit. -/
theorem canonicalCompletedNativeHankelPair_posSemidef_of_eventually_dslopeSamples
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite)
    (N : ℕ) :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosSemidef ∧
      (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N).PosSemidef := by
  have hsamples : ∀ᶠ k : ℕ in Filter.atTop,
      (completedGreenRealKernelSampleMatrix
        canonicalCompletedNativeDslopeKernel
        (canonicalGreenJetRealStep k) (2 * N)).PosSemidef :=
    hdslope (2 * N)
  rw [Filter.eventually_atTop] at hsamples
  obtain ⟨K, hK⟩ := hsamples
  let transformed (k : ℕ) :=
    completedGreenRealKernelForwardDifferenceMatrix
      canonicalCompletedNativeDslopeKernel
      (canonicalGreenJetRealStep (k + K)) (2 * N)
  have htransformed (k : ℕ) : (transformed k).PosSemidef := by
    exact completedGreenRealKernelForwardDifferenceMatrix_posSemidef
      (hK (k + K) (by omega))
  constructor
  · apply matrixPosSemidef_of_tendsto_entrywise
      (A := fun k ↦ (transformed k).submatrix
        completedGreenEvenOrderIndex completedGreenEvenOrderIndex)
    · intro k
      exact (htransformed k).submatrix completedGreenEvenOrderIndex
    · intro i j
      rw [show (fun k ↦
          (transformed k).submatrix
            completedGreenEvenOrderIndex completedGreenEvenOrderIndex i j) =
        fun k ↦
          (completedGreenKernelForwardDifference
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetStep (k + K))
            (2 * (i : ℕ)) (2 * (j : ℕ))).re by
          funext k
          rw [show canonicalGreenJetStep (k + K) =
              (canonicalGreenJetRealStep (k + K) : ℂ) by simp]
          exact completedGreenRealKernelForwardDifferenceMatrix_apply
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetRealStep (k + K)) (2 * N)
            (completedGreenEvenOrderIndex i)
            (completedGreenEvenOrderIndex j)]
      change Filter.Tendsto
        (fun k ↦
          (completedGreenKernelForwardDifference
            (fun x z ↦ dslope
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) x z)
            (canonicalGreenJetStep (k + K)) (2 * (i : ℕ))
              (2 * (j : ℕ))).re)
        Filter.atTop
        (nhds (hankelGram
          canonicalCompletedNativeLogDerivativeMoment N i j))
      have hlimit :=
        completedNativeGreenKernelForwardDifference_dslope_re_tendsto
          (Sum.inl (i : ℕ)) (Sum.inl (j : ℕ))
      have hshift := hlimit.comp (Filter.tendsto_add_atTop_nat K)
      simpa only [Function.comp_def, hankelGram,
        completedGreenParityOrder, greenWronskianMomentKernel] using hshift
  · apply matrixPosSemidef_of_tendsto_entrywise
      (A := fun k ↦ (transformed k).submatrix
        completedGreenOddOrderIndex completedGreenOddOrderIndex)
    · intro k
      exact (htransformed k).submatrix completedGreenOddOrderIndex
    · intro i j
      rw [show (fun k ↦
          (transformed k).submatrix
            completedGreenOddOrderIndex completedGreenOddOrderIndex i j) =
        fun k ↦
          (completedGreenKernelForwardDifference
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetStep (k + K)) (2 * (i : ℕ) + 1)
              (2 * (j : ℕ) + 1)).re by
          funext k
          rw [show canonicalGreenJetStep (k + K) =
              (canonicalGreenJetRealStep (k + K) : ℂ) by simp]
          exact completedGreenRealKernelForwardDifferenceMatrix_apply
            canonicalCompletedNativeDslopeKernel
            (canonicalGreenJetRealStep (k + K)) (2 * N)
            (completedGreenOddOrderIndex i)
            (completedGreenOddOrderIndex j)]
      change Filter.Tendsto
        (fun k ↦
          (completedGreenKernelForwardDifference
            (fun x z ↦ dslope
              (completedGreenNormalizedResponse
                completedNativeOperatorCharacteristic
                completedNativeOperatorBoundaryCompanion) x z)
            (canonicalGreenJetStep (k + K)) (2 * (i : ℕ) + 1)
              (2 * (j : ℕ) + 1)).re)
        Filter.atTop
        (nhds (shiftedHankel
          canonicalCompletedNativeLogDerivativeMoment N i j))
      have hlimit :=
        completedNativeGreenKernelForwardDifference_dslope_re_tendsto
          (Sum.inr (i : ℕ)) (Sum.inr (j : ℕ))
      have hshift := hlimit.comp (Filter.tendsto_add_atTop_nat K)
      simpa only [Function.comp_def, shiftedHankel,
        completedGreenParityOrder, greenWronskianMomentKernel] using hshift

/-- All-order semidefinite form of the two canonical completed-native Hankel
towers.  This deliberately does not assert the strict positivity required by
`CanonicalCompletedNativeStieltjesPositivity`. -/
def CanonicalCompletedNativeStieltjesPosSemidefinite : Prop :=
  ∀ N : ℕ,
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).PosSemidef ∧
      (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N).PosSemidef

/-- A positive-semidefinite completed-native `dslope` kernel on every finite
real sampling grid gives the all-order semidefinite Hankel pair. -/
theorem canonicalCompletedNativeStieltjesPosSemidefinite_of_dslopeSamples
    (hdslope : CanonicalCompletedNativeDslopeSamplePosSemidefinite) :
    CanonicalCompletedNativeStieltjesPosSemidefinite := by
  intro N
  exact canonicalCompletedNativeHankelPair_posSemidef_of_dslopeSamples
    hdslope N

/-- Minimal eventual sample positivity already gives the all-order
semidefinite Stieltjes pair. -/
theorem
    canonicalCompletedNativeStieltjesPosSemidefinite_of_eventually_dslopeSamples
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite) :
    CanonicalCompletedNativeStieltjesPosSemidefinite := by
  intro N
  exact
    canonicalCompletedNativeHankelPair_posSemidef_of_eventually_dslopeSamples
      hdslope N

/-! ## Exact strictness gate -/

/-- Nondegeneracy of every finite section of the two completed-native Hankel
towers.  Once semidefiniteness is known, this is exactly the additional
condition required for strict positivity; no convergence claim is hidden in
the definition. -/
def CanonicalCompletedNativeHankelPairNondegenerate : Prop :=
  ∀ N : ℕ,
    (hankelGram canonicalCompletedNativeLogDerivativeMoment N).det ≠ 0 ∧
      (shiftedHankel
        canonicalCompletedNativeLogDerivativeMoment N).det ≠ 0

/-- Coefficient-space form of finite Hankel nondegeneracy.  It states that no
nonzero finite coefficient vector is annihilated by all moment readouts in
the same prefix.  This is the form intended for exact geometric or
Vandermonde readouts. -/
def CanonicalCompletedNativeHankelPairMulVecInjective : Prop :=
  ∀ N : ℕ,
    Function.Injective
        (hankelGram canonicalCompletedNativeLogDerivativeMoment N).mulVec ∧
      Function.Injective
        (shiftedHankel
          canonicalCompletedNativeLogDerivativeMoment N).mulVec

/-- Determinant nonvanishing and absence of finite moment annihilators are
exactly the same strictness gate. -/
theorem
    canonicalCompletedNativeHankelPairNondegenerate_iff_mulVecInjective :
    CanonicalCompletedNativeHankelPairNondegenerate ↔
      CanonicalCompletedNativeHankelPairMulVecInjective := by
  constructor
  · intro hnondegenerate N
    constructor
    · rw [Matrix.mulVec_injective_iff_isUnit,
        Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr (hnondegenerate N).1
    · rw [Matrix.mulVec_injective_iff_isUnit,
        Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr (hnondegenerate N).2
  · intro hinjective N
    constructor
    · exact isUnit_iff_ne_zero.mp
        ((Matrix.isUnit_iff_isUnit_det _).mp
          (Matrix.mulVec_injective_iff_isUnit.mp (hinjective N).1))
    · exact isUnit_iff_ne_zero.mp
        ((Matrix.isUnit_iff_isUnit_det _).mp
          (Matrix.mulVec_injective_iff_isUnit.mp (hinjective N).2))

/-- Strict Stieltjes positivity is precisely semidefiniteness plus the absence
of a finite null direction in either Hankel tower. -/
theorem
    canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate :
    CanonicalCompletedNativeStieltjesPositivity ↔
      CanonicalCompletedNativeStieltjesPosSemidefinite ∧
        CanonicalCompletedNativeHankelPairNondegenerate := by
  constructor
  · intro hpos
    constructor
    · intro N
      exact ⟨(hpos N).1.posSemidef, (hpos N).2.posSemidef⟩
    · intro N
      exact
        ⟨((hpos N).1.posSemidef.posDef_iff_det_ne_zero).mp (hpos N).1,
          ((hpos N).2.posSemidef.posDef_iff_det_ne_zero).mp (hpos N).2⟩
  · rintro ⟨hsemidef, hnondegenerate⟩ N
    exact
      ⟨((hsemidef N).1.posDef_iff_det_ne_zero).mpr
          (hnondegenerate N).1,
        ((hsemidef N).2.posDef_iff_det_ne_zero).mpr
          (hnondegenerate N).2⟩

/-- The sampled-kernel route has no further analytic loss: eventual
semidefiniteness supplies the closed inequalities, and finite-section
nondegeneracy upgrades them to the exact all-order Stieltjes gate. -/
theorem canonicalCompletedNativeStieltjesPositivity_of_eventually_dslopeSamples
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CanonicalCompletedNativeStieltjesPositivity := by
  rw [
    canonicalCompletedNativeStieltjesPositivity_iff_posSemidefinite_and_nondegenerate]
  exact
    ⟨canonicalCompletedNativeStieltjesPosSemidefinite_of_eventually_dslopeSamples
        hdslope,
      hnondegenerate⟩

/-! ## Direct canonical HP endpoint -/

/-- Eventual positivity of the concrete shrinking-grid `dslope` samples and
finite-section nondegeneracy construct the canonical completed-native HP
carrier without any auxiliary Green, Gamma, or BR2 state. -/
theorem completedNativeRealHPCarrierCertificate_of_eventually_dslopeSamples
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_eventually_dslopeSamples
          hdslope hnondegenerate)) :=
  completedNativeRealHPCarrierCertificate_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_eventually_dslopeSamples
      hdslope hnondegenerate)

/-- Readout-facing form of the same endpoint: finite injectivity of the two
moment operators replaces explicit determinant calculations. -/
theorem
    completedNativeRealHPCarrierCertificate_of_eventually_dslopeSamples_of_mulVecInjective
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite)
    (hinjective : CanonicalCompletedNativeHankelPairMulVecInjective) :
    CompletedNativeRealHPCarrierCertificate
      (canonicalCompletedNativeStieltjesJet
        (canonicalCompletedNativeStieltjesPositivity_of_eventually_dslopeSamples
          hdslope
          (canonicalCompletedNativeHankelPairNondegenerate_iff_mulVecInjective.mpr
            hinjective))) :=
  completedNativeRealHPCarrierCertificate_of_eventually_dslopeSamples
    hdslope
    (canonicalCompletedNativeHankelPairNondegenerate_iff_mulVecInjective.mpr
      hinjective)

/-- The two isolated finite gates feed the already formalized canonical
Jacobi resolvent and hence completed-native confinement. -/
theorem completedNativeOperator_zero_im_eq_zero_of_eventually_dslopeSamples
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite)
    (hnondegenerate : CanonicalCompletedNativeHankelPairNondegenerate)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_stieltjesPositivity
    (canonicalCompletedNativeStieltjesPositivity_of_eventually_dslopeSamples
      hdslope hnondegenerate)
    hzDomain hzero

/-- Confinement endpoint in the same coefficient-injectivity interface. -/
theorem
    completedNativeOperator_zero_im_eq_zero_of_eventually_dslopeSamples_of_mulVecInjective
    (hdslope :
      CanonicalCompletedNativeDslopeSampleEventuallyPosSemidefinite)
    (hinjective : CanonicalCompletedNativeHankelPairMulVecInjective)
    {z : ℂ}
    (hzDomain : z ∈ completedNativeHeightDomain)
    (hzero : completedNativeOperatorCharacteristic z = 0) :
    z.im = 0 :=
  completedNativeOperator_zero_im_eq_zero_of_eventually_dslopeSamples
    hdslope
    (canonicalCompletedNativeHankelPairNondegenerate_iff_mulVecInjective.mpr
      hinjective)
    hzDomain hzero

end

end CarrySelfAdjointOperator

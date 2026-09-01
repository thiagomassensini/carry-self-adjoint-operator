import CarrySelfAdjointOperator.CompletedNativeChiralPickFactorization
import CarrySelfAdjointOperator.CompletedNativeRadialTiltSamplePositivity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# From radial chiral Pick samples to the completed Hankel towers

This module supplies the finite-dimensional part of route B.  A shifted
complex forward-difference stencil is a triangular congruence of the kernel
sample matrix.  Therefore positive radial `dslope` samples remain positive
after every finite all-order extraction.  The already proved radial Taylor
limit then gives the two canonical completed-native Hankel towers.

No Gamma sewing, characteristic zero, Jacobi operator, or spectral premise is
used.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace CarrySelfAdjointOperator

open Filter Topology

noncomputable section

/-! ## Shifted complex finite-difference congruence -/

/-- Signed-binomial coefficient of the normalized complex forward difference
of order `order`, evaluated at the shifted sample `index + 1`. -/
def completedGreenComplexForwardDifferenceCoefficient
    (step : ℂ) (order index : ℕ) : ℂ :=
  (((order.factorial : ℂ) * step ^ order)⁻¹) *
    ((((-1 : ℤ) ^ (order - index) * order.choose index : ℤ) : ℂ))

@[simp] theorem conj_completedGreenComplexForwardDifferenceCoefficient
    (step : ℂ) (order index : ℕ) :
    conj (completedGreenComplexForwardDifferenceCoefficient
      step order index) =
      completedGreenComplexForwardDifferenceCoefficient
        (conj step) order index := by
  unfold completedGreenComplexForwardDifferenceCoefficient
  simp only [map_mul, map_inv₀, map_pow, map_natCast, map_intCast]

@[simp] theorem completedGreenComplexForwardDifferenceCoefficient_eq_zero_of_lt
    {step : ℂ} {order index : ℕ} (h : order < index) :
    completedGreenComplexForwardDifferenceCoefficient step order index = 0 := by
  simp [completedGreenComplexForwardDifferenceCoefficient,
    Nat.choose_eq_zero_of_lt h]

theorem sum_range_completedGreenComplexForwardDifferenceCoefficient_mul
    {N : ℕ} (step : ℂ) (order : Fin N) (f : ℕ → ℂ) :
    (∑ index ∈ Finset.range N,
        completedGreenComplexForwardDifferenceCoefficient
          step order index * f index) =
      ∑ index ∈ Finset.range ((order : ℕ) + 1),
        completedGreenComplexForwardDifferenceCoefficient
          step order index * f index := by
  symm
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_iff.mpr order.isLt)
  · intro index hindexN hindexOrder
    have hlt : (order : ℕ) < index := by
      have hnot : ¬index < (order : ℕ) + 1 := by
        simpa only [Finset.mem_range] using hindexOrder
      omega
    simp [completedGreenComplexForwardDifferenceCoefficient_eq_zero_of_lt hlt]

theorem sum_fin_completedGreenComplexForwardDifferenceCoefficient_mul
    {N : ℕ} (step : ℂ) (order : Fin N) (f : ℕ → ℂ) :
    (∑ index : Fin N,
        completedGreenComplexForwardDifferenceCoefficient
          step order index * f index) =
      ∑ index ∈ Finset.range ((order : ℕ) + 1),
        completedGreenComplexForwardDifferenceCoefficient
          step order index * f index := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ index ∈ Finset.range N,
        if h : index < N then
          completedGreenComplexForwardDifferenceCoefficient
            step order (⟨index, h⟩ : Fin N) * f (⟨index, h⟩ : Fin N)
        else 0) =
      ∑ index ∈ Finset.range N,
        completedGreenComplexForwardDifferenceCoefficient
          step order index * f index := by
            apply Finset.sum_congr rfl
            intro index hindex
            rw [dif_pos (Finset.mem_range.mp hindex)]
    _ = _ :=
      sum_range_completedGreenComplexForwardDifferenceCoefficient_mul
        step order f

/-- Triangular transform from the shifted kernel samples to normalized
forward-difference orders. -/
def completedGreenComplexForwardDifferenceTransform
    (step : ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun index order =>
    completedGreenComplexForwardDifferenceCoefficient step order index

/-- Kernel matrix on the shifted grid `step, 2*step, ...`. -/
def completedGreenComplexShiftedKernelSampleMatrix
    (kernel : ℂ → ℂ → ℂ) (step : ℂ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    kernel (((i : ℕ) + 1 : ℕ) * step)
      (((j : ℕ) + 1 : ℕ) * step)

/-- Congruence of the shifted complex sample matrix by all normalized
forward-difference orders below `N`. -/
def completedGreenComplexShiftedKernelForwardDifferenceMatrix
    (kernel : ℂ → ℂ → ℂ) (step : ℂ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let transform := completedGreenComplexForwardDifferenceTransform step N
  transform.conjTranspose *
    completedGreenComplexShiftedKernelSampleMatrix kernel step N * transform

theorem completedGreenComplexShiftedKernelForwardDifferenceMatrix_posSemidef
    {kernel : ℂ → ℂ → ℂ} {step : ℂ} {N : ℕ}
    (hsample :
      (completedGreenComplexShiftedKernelSampleMatrix
        kernel step N).PosSemidef) :
    (completedGreenComplexShiftedKernelForwardDifferenceMatrix
      kernel step N).PosSemidef := by
  simpa [completedGreenComplexShiftedKernelForwardDifferenceMatrix] using
    hsample.conjTranspose_mul_mul_same
      (completedGreenComplexForwardDifferenceTransform step N)

/-- The entrywise real part of a complex positive-semidefinite matrix is a
real positive-semidefinite matrix.  This is restriction of its Hermitian
quadratic form to real coordinate vectors. -/
theorem complexMatrixRealPart_posSemidef
    {n : Type*} [Finite n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) :
    Matrix.PosSemidef ((fun i j => (A i j).re) : Matrix n n ℝ) := by
  letI := Fintype.ofFinite n
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    have h := congrArg Complex.re (hA.isHermitian.apply i j)
    simpa using h
  · intro x
    have h := hA.re_dotProduct_nonneg (fun i => (x i : ℂ))
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      Complex.mul_re] using h

/-- Every entry of the triangular congruence is the corresponding shifted
normalized mixed forward difference of the original kernel. -/
theorem completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply
    (kernel : ℂ → ℂ → ℂ) (step : ℂ) (N : ℕ) (p q : Fin N) :
    completedGreenComplexShiftedKernelForwardDifferenceMatrix
        kernel step N p q =
      completedGreenKernelTwoStepShiftedForwardDifference
        kernel step step p q := by
  classical
  unfold completedGreenComplexShiftedKernelForwardDifferenceMatrix
    completedGreenComplexForwardDifferenceTransform
    completedGreenComplexShiftedKernelSampleMatrix
    completedGreenKernelTwoStepShiftedForwardDifference
    completedGreenKernelTwoStepShiftedRawDifference
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  let sample : ℕ → ℕ → ℂ := fun i j =>
    kernel (((i : ℕ) + 1 : ℕ) * step)
      (((j : ℕ) + 1 : ℕ) * step)
  change
    (∑ j : Fin N,
        (∑ i : Fin N,
          conj (completedGreenComplexForwardDifferenceCoefficient
            step p i) * sample i j) *
          completedGreenComplexForwardDifferenceCoefficient step q j) = _
  rw [show (∑ j : Fin N,
        (∑ i : Fin N,
          conj (completedGreenComplexForwardDifferenceCoefficient
            step p i) * sample i j) *
          completedGreenComplexForwardDifferenceCoefficient step q j) =
      ∑ j : Fin N,
        completedGreenComplexForwardDifferenceCoefficient step q j *
          (∑ i : Fin N,
            completedGreenComplexForwardDifferenceCoefficient
              (conj step) p i * sample i j) by
        apply Finset.sum_congr rfl
        intro j _
        calc
          (∑ i : Fin N,
              conj (completedGreenComplexForwardDifferenceCoefficient
                step p i) * sample i j) *
              completedGreenComplexForwardDifferenceCoefficient step q j =
            completedGreenComplexForwardDifferenceCoefficient step q j *
              (∑ i : Fin N,
                conj (completedGreenComplexForwardDifferenceCoefficient
                  step p i) * sample i j) := mul_comm _ _
          _ = completedGreenComplexForwardDifferenceCoefficient step q j *
              (∑ i : Fin N,
                completedGreenComplexForwardDifferenceCoefficient
                  (conj step) p i * sample i j) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            rw [conj_completedGreenComplexForwardDifferenceCoefficient]]
  rw [sum_fin_completedGreenComplexForwardDifferenceCoefficient_mul
    step q (fun j => ∑ i : Fin N,
      completedGreenComplexForwardDifferenceCoefficient
        (conj step) p i * sample i j)]
  have hinner :
      (∑ j ∈ Finset.range ((q : ℕ) + 1),
        completedGreenComplexForwardDifferenceCoefficient step q j *
          ∑ i : Fin N,
            completedGreenComplexForwardDifferenceCoefficient
              (conj step) p i * sample i j) =
        ∑ j ∈ Finset.range ((q : ℕ) + 1),
          completedGreenComplexForwardDifferenceCoefficient step q j *
            ∑ i ∈ Finset.range ((p : ℕ) + 1),
              completedGreenComplexForwardDifferenceCoefficient
                (conj step) p i * sample i j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [sum_fin_completedGreenComplexForwardDifferenceCoefficient_mul
      (conj step) p (fun i => sample i j)]
  rw [hinner]
  rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp_rw [completedGreenForwardDifference_iter_eq_sum_shift]
  simp only [zsmul_eq_mul, map_inv₀, map_mul, map_pow, map_natCast]
  unfold completedGreenComplexForwardDifferenceCoefficient sample
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

/-! ## Radial Pick consequence -/

/-- Radial Pick positivity gives both canonical completed-native Hankel
towers as closed positive forms. -/
theorem canonicalCompletedNativeStieltjesPosSemidefinite_of_radialChiralPick
    (hPick :
      CanonicalCompletedNativeRadialChiralPickEventuallyPosSemidefinite) :
    CanonicalCompletedNativeStieltjesPosSemidefinite := by
  intro N
  let orderCount := 2 * N
  let transformed (k : ℕ) : Matrix (Fin orderCount) (Fin orderCount) ℂ :=
    completedGreenComplexShiftedKernelForwardDifferenceMatrix
      canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialSecondStep k) orderCount
  have htransformed : ∀ᶠ k : ℕ in atTop,
      (transformed k).PosSemidef := by
    filter_upwards [
      canonicalCompletedNativeRadialDslopeSampleMatrix_eventually_posSemidef_of_chiralPick
        hPick orderCount] with k hk
    apply completedGreenComplexShiftedKernelForwardDifferenceMatrix_posSemidef
    change (canonicalCompletedNativeRadialDslopeSampleMatrix
      k orderCount).PosSemidef
    exact hk
  obtain ⟨K, hK⟩ := eventually_atTop.1 htransformed
  let shiftedTransformed (k : ℕ) := transformed (k + K)
  have hshiftedTransformed (k : ℕ) :
      (shiftedTransformed k).PosSemidef := by
    exact hK (k + K) (by omega)
  constructor
  · let evenMatrix (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      fun i j => (shiftedTransformed k
        (completedGreenEvenOrderIndex i)
        (completedGreenEvenOrderIndex j)).re
    apply matrixPosSemidef_of_tendsto_entrywise (A := evenMatrix)
    · intro k
      have hsub := (hshiftedTransformed k).submatrix
        (fun i : Fin N => completedGreenEvenOrderIndex i)
      exact complexMatrixRealPart_posSemidef hsub
    · intro i j
      have hlimit := completedNativePolarizedDslope_shiftedRadial_tendsto
        (2 * (i : ℕ)) (2 * (j : ℕ))
      have hdiag : Tendsto (fun k : ℕ => (k + K, k + K)) atTop atTop := by
        rw [← prod_atTop_atTop_eq]
        exact (tendsto_add_atTop_nat K).prodMk
          (tendsto_add_atTop_nat K)
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp
        (hlimit.comp hdiag)
      simpa [evenMatrix, shiftedTransformed, transformed,
        Function.comp_def,
        completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply,
        completedGreenEvenOrderIndex, hankelGram,
        completedGreenParityOrder,
        greenWronskianMomentKernel] using hreal
  · let oddMatrix (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      fun i j => (shiftedTransformed k
        (completedGreenOddOrderIndex i)
        (completedGreenOddOrderIndex j)).re
    apply matrixPosSemidef_of_tendsto_entrywise (A := oddMatrix)
    · intro k
      have hsub := (hshiftedTransformed k).submatrix
        (fun i : Fin N => completedGreenOddOrderIndex i)
      exact complexMatrixRealPart_posSemidef hsub
    · intro i j
      have hlimit := completedNativePolarizedDslope_shiftedRadial_tendsto
        (2 * (i : ℕ) + 1) (2 * (j : ℕ) + 1)
      have hdiag : Tendsto (fun k : ℕ => (k + K, k + K)) atTop atTop := by
        rw [← prod_atTop_atTop_eq]
        exact (tendsto_add_atTop_nat K).prodMk
          (tendsto_add_atTop_nat K)
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp
        (hlimit.comp hdiag)
      simpa [oddMatrix, shiftedTransformed, transformed,
        Function.comp_def,
        completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply,
        completedGreenOddOrderIndex, shiftedHankel,
        completedGreenParityOrder,
        greenWronskianMomentKernel] using hreal

end

end CarrySelfAdjointOperator

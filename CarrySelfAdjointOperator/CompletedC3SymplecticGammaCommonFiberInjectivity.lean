import CarrySelfAdjointOperator.CompletedC3SymplecticGammaCentralSpectralFiberAudit
import NativeCarrySpectralWeyl.Finite.Gram
import NativeCarrySpectralWeyl.Infinite.Kolmogorov
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

open scoped BigOperators Matrix

noncomputable section

def sixCameraPeriodicMeanRat : Matrix (Fin 6) (Fin 6) ℚ :=
  !![3 / 2, 0,   5 / 2, 0,   4 / 3, 0;
     0,   2,   0,   0,   2,   0;
     5 / 2, 0,  11 / 2, 0,   4 / 3, 0;
     0,   0,   0,   4,   0,   0;
     4 / 3, 2,   4 / 3, 0,  22 / 3, 0;
     0,   0,   0,   0,   0,   6]

def sixCameraPeriodicMean : Matrix (Fin 6) (Fin 6) ℝ :=
  (Rat.castHom ℝ).mapMatrix sixCameraPeriodicMeanRat

theorem sixCameraPeriodicMean_eq :
    NativeCarrySpectralWeyl.Finite.periodicMeanMatrix
        420 NativeCarrySpectralWeyl.Finite.sixCamera =
      sixCameraPeriodicMean := by
  ext i j
  rw [periodicMeanMatrix_apply]
  have hsum := congr_fun (congr_fun sixCameraProductSum_eq i) j
  simp only [periodicProductMean]
  rw [hsum]
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCamera, sixCameraPeriodicMean,
      sixCameraPeriodicMeanRat, sixCameraProductSum]

def sixCameraPeriodicMeanLDLLower : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1,   0,    0,   0, 0, 0;
     0,   1,    0,   0, 0, 0;
     5 / 3, 0,  1,   0, 0, 0;
     0,   0,    0,   1, 0, 0;
     8 / 9, 1, -2 / 3, 0, 1, 0;
     0,   0,    0,   0, 0, 1]

def sixCameraPeriodicMeanLDDiagonal : Matrix (Fin 6) (Fin 6) ℚ :=
  Matrix.diagonal ![3 / 2, 2, 4 / 3, 4, 32 / 9, 6]

private theorem sixCameraPeriodicMeanRat_ldl :
    sixCameraPeriodicMeanRat =
      sixCameraPeriodicMeanLDLLower *
        sixCameraPeriodicMeanLDDiagonal *
          sixCameraPeriodicMeanLDLLowerᵀ := by
  ext i j
  simp only [sixCameraPeriodicMeanLDDiagonal, Matrix.mul_apply,
    Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [sixCameraPeriodicMeanRat,
      sixCameraPeriodicMeanLDLLower, Matrix.diagonal_apply,
      Fin.sum_univ_succ]

private theorem sixCameraPeriodicMeanLDLLower_det :
    sixCameraPeriodicMeanLDLLower.det = 1 := by
  have htri :
      sixCameraPeriodicMeanLDLLower.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    fin_cases i <;> fin_cases j <;>
      simp_all [sixCameraPeriodicMeanLDLLower]
  rw [Matrix.det_of_lowerTriangular sixCameraPeriodicMeanLDLLower htri]
  norm_num [sixCameraPeriodicMeanLDLLower, Fin.prod_univ_succ]

private theorem sixCameraPeriodicMeanLDDiagonal_det :
    sixCameraPeriodicMeanLDDiagonal.det = 1024 / 3 := by
  rw [sixCameraPeriodicMeanLDDiagonal, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

theorem sixCameraPeriodicMean_det :
    sixCameraPeriodicMean.det = 1024 / 3 := by
  have hdet : sixCameraPeriodicMeanRat.det = (1024 / 3 : ℚ) := by
    rw [sixCameraPeriodicMeanRat_ldl, Matrix.det_mul, Matrix.det_mul,
      sixCameraPeriodicMeanLDLLower_det,
      sixCameraPeriodicMeanLDDiagonal_det, Matrix.det_transpose,
      sixCameraPeriodicMeanLDLLower_det]
    norm_num
  rw [sixCameraPeriodicMean]
  change (sixCameraPeriodicMeanRat.map fun x => (x : ℝ)).det = _
  rw [← Rat.cast_det, hdet]
  norm_num

def sixCameraIndex (i : Fin 6) : CameraIndex :=
  ⟨NativeCarrySpectralWeyl.Finite.sixCamera i, by
    fin_cases i <;>
      norm_num [NativeCarrySpectralWeyl.Finite.sixCamera]⟩

def sixCameraKolmogorovFamily (i : Fin 6) :=
  NativeCarrySpectralWeyl.Infinite.kolmogorovVector (sixCameraIndex i)

theorem gram_sixCameraKolmogorovFamily :
    Matrix.gram ℝ sixCameraKolmogorovFamily =
      sixCameraPeriodicMean := by
  ext i j
  change
    inner ℝ (NativeCarrySpectralWeyl.Infinite.kolmogorovVector
      (sixCameraIndex i))
      (NativeCarrySpectralWeyl.Infinite.kolmogorovVector
        (sixCameraIndex j)) = sixCameraPeriodicMean i j
  rw [inner_kolmogorovVector]
  unfold periodicMeanKernel
  have hperiod :
      pairPeriod (sixCameraIndex i) (sixCameraIndex j) ∣ 420 := by
    unfold pairPeriod
    apply Nat.lcm_dvd
    · simpa [sixCameraIndex, cameraLabel] using
        (sixCamera_commonPeriod i)
    · simpa [sixCameraIndex, cameraLabel] using
        (sixCamera_commonPeriod j)
  rw [← periodicProductMean_eq_pairPeriod
    (sixCameraIndex i) (sixCameraIndex j) hperiod (by norm_num)]
  have hmean := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M i j)
    sixCameraPeriodicMean_eq
  rw [← hmean, periodicMeanMatrix_apply]
  rfl

theorem sixCameraKolmogorovFamily_linearIndependent :
    LinearIndependent ℝ sixCameraKolmogorovFamily := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  rw [gram_sixCameraKolmogorovFamily, sixCameraPeriodicMean_det]
  norm_num

noncomputable def canonicalC3RealCoordinateEquivFin6 :
    CanonicalC3RealCoordinate ≃ Fin 6 :=
  finCongr finiteC3GreenBoundarySpace_real_finrank_eq_six

theorem canonicalC3KolmogorovFamily_linearIndependent :
    LinearIndependent ℝ
      (fun j : CanonicalC3RealCoordinate =>
        NativeCarrySpectralWeyl.Infinite.kolmogorovVector
          (canonicalC3RealCoordinateCameraIndex j)) := by
  have hli := sixCameraKolmogorovFamily_linearIndependent.comp
    canonicalC3RealCoordinateEquivFin6
    canonicalC3RealCoordinateEquivFin6.injective
  convert hli using 1
  funext j
  simp [sixCameraKolmogorovFamily, sixCameraIndex,
    canonicalC3RealCoordinateEquivFin6,
    canonicalC3RealCoordinateCameraIndex, sixCamera]

def canonicalC3RawCameraSpan : Submodule ℝ CameraHilbert :=
  Submodule.span ℝ (Set.range canonicalC3RawCameraVector)

def canonicalC3KolmogorovSpan :
    Submodule ℝ NativeCarrySpectralWeyl.Infinite.KolmogorovSpace :=
  Submodule.span ℝ
    (Set.range (fun j : CanonicalC3RealCoordinate =>
      NativeCarrySpectralWeyl.Infinite.kolmogorovVector
        (canonicalC3RealCoordinateCameraIndex j)))

noncomputable def canonicalC3CommonFiberEquiv :
    canonicalC3RawCameraSpan ≃ₗ[ℝ] canonicalC3KolmogorovSpan :=
  (Module.Basis.span canonicalC3RawCameraVector_linearIndependent).repr.trans
    (Module.Basis.span canonicalC3KolmogorovFamily_linearIndependent).repr.symm

@[simp] theorem canonicalC3CommonFiberEquiv_raw
    (j : CanonicalC3RealCoordinate) :
    canonicalC3CommonFiberEquiv
        ⟨canonicalC3RawCameraVector j,
          Submodule.subset_span (Set.mem_range_self j)⟩ =
      ⟨NativeCarrySpectralWeyl.Infinite.kolmogorovVector
          (canonicalC3RealCoordinateCameraIndex j),
        Submodule.subset_span (Set.mem_range_self j)⟩ := by
  apply Subtype.ext
  unfold canonicalC3CommonFiberEquiv canonicalC3RawCameraSpan canonicalC3KolmogorovSpan
  rw [LinearEquiv.trans_apply]
  rw [Module.Basis.span_repr_eq_single]
  rw [Module.Basis.repr_symm_single_one]
  simp [Module.Basis.span]

theorem canonicalC3CommonFiberEquiv_injective :
    Function.Injective canonicalC3CommonFiberEquiv :=
  canonicalC3CommonFiberEquiv.injective

theorem canonicalC3CommonFiber_of_orthonormal_ne_zero
    (j : CanonicalC3RealCoordinate) :
    canonicalC3CommonFiberEquiv
        ⟨canonicalC3OrthonormalCameraVector j,
          canonicalC3OrthonormalCameraVector_mem_span_raw j⟩ ≠ 0 := by
  intro hzero
  have hsourcezero :
      (⟨canonicalC3OrthonormalCameraVector j,
        canonicalC3OrthonormalCameraVector_mem_span_raw j⟩ :
        canonicalC3RawCameraSpan) = 0 := by
    apply canonicalC3CommonFiberEquiv_injective
    simpa using hzero
  have hvectorzero : canonicalC3OrthonormalCameraVector j = 0 := by
    exact congrArg Subtype.val hsourcezero
  exact canonicalC3OrthonormalCameraVector_orthonormal.ne_zero j
    hvectorzero

#print axioms sixCameraPeriodicMean_eq
#print axioms sixCameraPeriodicMeanRat_ldl
#print axioms sixCameraPeriodicMeanLDLLower_det
#print axioms sixCameraPeriodicMeanLDDiagonal_det
#print axioms sixCameraPeriodicMean_det
#print axioms gram_sixCameraKolmogorovFamily
#print axioms sixCameraKolmogorovFamily_linearIndependent
#print axioms canonicalC3KolmogorovFamily_linearIndependent
#print axioms canonicalC3CommonFiberEquiv_raw
#print axioms canonicalC3CommonFiberEquiv_injective
#print axioms canonicalC3CommonFiber_of_orthonormal_ne_zero

end

end CarrySelfAdjointOperator

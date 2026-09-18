import CarrySelfAdjointOperator.CompletedC3SymplecticGammaState
import CarrySelfAdjointOperator.CompletedNativeRadialTiltSamplePositivity
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

namespace CarrySelfAdjointOperator

open scoped ComplexConjugate ComplexOrder

noncomputable section

def canonicalCompletedC3SymplecticRadialGammaSampleMatrix
    (k N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    canonicalCompletedC3SymplecticGammaKernel
      (canonicalCompletedC3RadialTiltPoint k i)
      (canonicalCompletedC3RadialTiltPoint k j)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
      (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j)

theorem
canonicalCompletedC3SymplecticRadialGammaSampleMatrix_posSemidef
    (k N : ℕ) :
    (canonicalCompletedC3SymplecticRadialGammaSampleMatrix k N).PosSemidef := by
  simpa [canonicalCompletedC3SymplecticRadialGammaSampleMatrix] using
    canonicalCompletedC3SymplecticGammaKernel_posSemidef
      (point := fun i : Fin N =>
        canonicalCompletedC3RadialTiltPoint k i)
      (hoffAxis := fun i =>
        canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)

theorem
canonicalCompletedC3SymplecticRadialGammaBoundaryReadout_eq_separation_mul_kernel
    (k i j : ℕ) :
    canonicalCompletedC3SymplecticGammaBoundaryReadout
        (canonicalCompletedC3RadialTiltPoint k i)
        (canonicalCompletedC3RadialTiltPoint k j)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
        (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) =
      (canonicalCompletedC3RadialTiltPoint k j -
          conj (canonicalCompletedC3RadialTiltPoint k i)) *
        canonicalCompletedC3SymplecticGammaKernel
          (canonicalCompletedC3RadialTiltPoint k i)
          (canonicalCompletedC3RadialTiltPoint k j)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k i)
          (canonicalCompletedC3RadialTiltPoint_im_ne_zero k j) := by
  exact canonicalCompletedC3SymplecticGammaBoundaryReadout_eq_kernel
    _ _ _ _

end

end CarrySelfAdjointOperator

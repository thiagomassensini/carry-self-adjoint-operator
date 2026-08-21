import CPFormal.Analytic.CpInfiniteRealSpectralGenerator

/-!
# Native logarithmic evolution

This module fixes the operator-theoretic origin of the height construction.
The starting operator is the maximal multiplication operator

`L e_n = log(n+1) e_n`

already proved self-adjoint in `CPFormal`.  The moment/Hankel/Jacobi layers do
not replace this generator by a zero table: they reorganize the completed
scalar response generated from its logarithmic jets.
-/

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp

noncomputable section

/-- Hilbert space carrying the maximal native logarithmic generator. -/
abbrev NativeLogHilbert := InfiniteRealSpectralHilbert

/-- The fixed maximal logarithmic generator from the native evolution. -/
def nativeLogGenerator :
    NativeLogHilbert →ₗ.[ℂ] NativeLogHilbert :=
  infiniteRealSpectralGenerator

/-- The native logarithmic generator is self-adjoint on its maximal domain. -/
theorem nativeLogGenerator_isSelfAdjoint :
    IsSelfAdjoint nativeLogGenerator := by
  simpa [nativeLogGenerator] using
    infiniteRealSpectralGenerator_isSelfAdjoint

/-- Every canonical coordinate belongs to the maximal logarithmic domain. -/
theorem nativeLogBasisVector_mem_domain (n : ℕ) :
    infiniteRealSpectralBasisVector n ∈ nativeLogGenerator.domain := by
  simpa [nativeLogGenerator] using
    infiniteRealSpectralBasisVector_mem_domain n

/-- In native coordinates the fixed generator has eigenvalue `log(n+1)`. -/
theorem nativeLogGenerator_basisVector (n : ℕ) :
    nativeLogGenerator
        ⟨infiniteRealSpectralBasisVector n,
          nativeLogBasisVector_mem_domain n⟩ =
      (infiniteRealSpectralFrequency n : ℂ) •
        infiniteRealSpectralBasisVector n := by
  simpa [nativeLogGenerator] using
    infiniteRealSpectralGenerator_basisVector n

end

end CarrySelfAdjointOperator

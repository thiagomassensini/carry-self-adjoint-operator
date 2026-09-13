import CarrySelfAdjointOperator.CompletedC3SeededClockBoundaryReduction
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-!
# Clock-to-Green moment gate

The seeded material clock already proves the interior polarized shift.  This
file records the exact remaining boundary calibration against the completed
Green ledger.  No Hankel matrix, Cholesky factor, or Jacobi operator is used.
-/

/-- Taylor coefficient of the completed ledger at its fixed central leg. -/
def canonicalCompletedC3LedgerBoundaryTaylorCoefficient
    (M p : ℕ) : ℂ :=
  iteratedDeriv (p + 1)
      (fun w : ℂ =>
        canonicalCompletedC3AllCutoffPolarizedLedgerNumerator M 0 w) 0 /
    ((p + 1).factorial : ℂ)

/-- Direct-sum Hilbert realization of a finite seeded clock atlas.  Each
block keeps its four reconstructed nodal coordinates; the atlas coefficient
is therefore a literal inner product in this carrier. -/
def seededClockAtlasJet
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (n : ℕ) :
    WithLp 2 (ι → EuclideanSpace ℂ (Fin 4)) :=
  WithLp.toLp 2 (fun i =>
    seededClockMaterialRawJet
      (block i).d (block i).a (block i).b (block i).c (block i).state n)

theorem seededClockAtlasCoefficient_eq_inner
    {ι : Type*} [Fintype ι]
    (block : ι → SeededClockBlock) (p q : ℕ) :
    inner ℂ (seededClockAtlasJet block p) (seededClockAtlasJet block q) =
      seededClockAtlasCoefficient block p q := by
  rw [PiLp.inner_apply]
  unfold seededClockAtlasJet seededClockAtlasCoefficient
  rfl

/-- The completed ledger first column is exactly the odd response coefficient.
The even orders vanish by parity and the odd orders are the native moments. -/
theorem canonicalCompletedC3LedgerBoundaryTaylorCoefficient_eq_boundaryTarget
    (M p : ℕ) :
    canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p =
      oddMomentResponseCoefficient
        canonicalCompletedNativeLogDerivativeMoment (p + 1) := by
  unfold canonicalCompletedC3LedgerBoundaryTaylorCoefficient
  rw [completedC3LedgerFixedCenterTaylorCoefficient_eq_response]
  rcases Nat.even_or_odd p with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [show n + n = 2 * n by omega,
      completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
      oddMomentResponseCoefficient_odd]
  · rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
      completedNativeGreenResponseTaylorCoefficient_even_eq_zero,
      oddMomentResponseCoefficient_even]

/-- Once the clock atlas first column is identified with the completed ledger,
the exact material-clock shift closes the full polarized coefficient equation.
This is the natural pre-Hankel gate: only the atlas-to-ledger boundary
calibration remains to instantiate it. -/
theorem seededClockAtlasCoefficient_equation_of_completedLedgerBoundary
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (hboundary : ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p) :
    IsPolarizedGreenCoefficientEquation
      canonicalCompletedNativeLogDerivativeMoment
      (seededClockAtlasCoefficient block) := by
  apply (seededClockAtlasCoefficientEquation_iff_boundary
    canonicalCompletedNativeLogDerivativeMoment block).2
  intro p
  rw [hboundary p,
    canonicalCompletedC3LedgerBoundaryTaylorCoefficient_eq_boundaryTarget]

/-- The calibrated clock atlas then supplies the complex Green moment kernel
directly in its own native direct-sum Hilbert carrier. -/
theorem seededClockAtlasGreenMomentKernel_of_completedLedgerBoundary
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (hboundary : ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p) :
    IsComplexGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  apply complexGreenWronskianMomentKernel_of_vectorCoefficientEquation
  rw [show HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      (seededClockAtlasJet block) ↔
      IsPolarizedGreenCoefficientEquation
        canonicalCompletedNativeLogDerivativeMoment
        (seededClockAtlasCoefficient block) by
    constructor <;> intro h p q
    · simpa [HasPolarizedCoefficientVectorEquation,
        seededClockAtlasCoefficient_eq_inner] using h p q
    · simpa [HasPolarizedCoefficientVectorEquation,
        seededClockAtlasCoefficient_eq_inner] using h p q]
  exact seededClockAtlasCoefficient_equation_of_completedLedgerBoundary
    M block hboundary

/-- The calibrated clock atlas is already sufficient for the carrier-correct
HP certificate once its two parity families are known independent. -/
theorem completedNativeRealHPCarrierCertificate_of_calibratedSeededClockAtlas
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (hboundary : ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p)
    (heven : LinearIndependent ℂ
      (fun n : ℕ => seededClockAtlasJet block (2 * n)))
    (hodd : LinearIndependent ℂ
      (fun n : ℕ => seededClockAtlasJet block (2 * n + 1))) :
    letI : InnerProductSpace ℝ
        (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
      InnerProductSpace.rclikeToReal ℂ _
    CompletedNativeRealHPCarrierCertificate
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  letI : InnerProductSpace ℝ
      (WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))) :=
    InnerProductSpace.rclikeToReal ℂ _
  have hcoeff : HasPolarizedCoefficientVectorEquation
      canonicalCompletedNativeLogDerivativeMoment
      (seededClockAtlasJet block) := by
    simpa [HasPolarizedCoefficientVectorEquation,
      seededClockAtlasCoefficient_eq_inner] using
      (seededClockAtlasCoefficient_equation_of_completedLedgerBoundary
        M block hboundary)
  exact completedNativeRealHPCarrierCertificate_of_vectorCoefficientEquation
    hcoeff heven hodd

end

end CarrySelfAdjointOperator

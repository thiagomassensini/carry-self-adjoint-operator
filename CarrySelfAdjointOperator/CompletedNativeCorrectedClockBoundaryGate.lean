import CarrySelfAdjointOperator.CompletedNativeCorrectedCausalChiralGate
import CarrySelfAdjointOperator.CompletedNativeSameEdgeGreenClockTransport
import Mathlib.Tactic

/-!
# Corrected-native boundary transport gate

The corrected causal/chiral readout is the native pre-Hankel object.  The
material seeded clock has an exact interior shift, so the only remaining
identification is its first column with that corrected readout.  This file
states that handoff in the corrected-native vocabulary and transports it to
the existing Green coefficient, moment-kernel, and HP-certificate theorems.

No Gram, Cholesky, Jacobi matrix, or fitted normalization is introduced.  The
raw one-block no-go is also restated for the corrected target, so a future
construction must change the material carrier rather than rescale the old
one.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-! ## The corrected-native first-column target -/

/-- The exact material-to-native handoff: every clock first-column coefficient
is the coefficient of the corrected native causal/chiral boundary readout. -/
def HasCorrectedNativeChiralBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) : Prop :=
  ∀ p : ℕ,
    seededClockAtlasCoefficient block p 0 =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p

/-- The corrected-native handoff is exactly the existing same-edge Green
transport, because the corrected coefficient is definitionally identified
with the completed full Wronskian response. -/
theorem hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeGreenToClockBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) :
    HasCorrectedNativeChiralBoundaryTransport M block ↔
      HasSameEdgeGreenToClockBoundaryTransport M block := by
  constructor
  · intro h p
    calc
      seededClockAtlasCoefficient block p 0 =
          canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
        h p
      _ = canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (p + 1) :=
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response
          M p
  · intro h p
    calc
      seededClockAtlasCoefficient block p 0 =
          canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
            M (p + 1) := h p
      _ = canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
        (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_response
          M p).symm

/-- The corrected-native boundary handoff gives the exact completed ledger
first column consumed by the material-clock reduction. -/
theorem canonicalCompletedC3LedgerBoundary_of_correctedNativeChiralBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p := by
  exact canonicalCompletedC3LedgerBoundary_of_sameEdgeGreenToClockBoundaryTransport
    M block
    ((hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeGreenToClockBoundaryTransport
      M block).mp htransport)

/-- The corrected-native first column is already the polarized Green moment
column, before any Hankel or Jacobi construction. -/
theorem seededClockAtlasCoefficient_firstColumn_eq_correctedNativePolarizedMoment
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) (p : ℕ)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    seededClockAtlasCoefficient block p 0 =
      polarizedGreenMomentCoefficient
        canonicalCompletedNativeLogDerivativeMoment p 0 := by
  calc
    seededClockAtlasCoefficient block p 0 =
        canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p :=
      htransport p
    _ = polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p 0 := by
      simpa using
        (canonicalCompletedNativeCorrectedChiralBoundaryCoefficient_eq_polarizedMoment
          M p 0)

/-- The corrected-native handoff closes the complete complex Green moment
kernel in the literal seeded-clock direct-sum carrier. -/
theorem seededClockAtlasGreenMomentKernel_of_correctedNativeChiralBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block) :
    IsComplexGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  exact seededClockAtlasGreenMomentKernel_of_sameEdgeGreenToClockBoundaryTransport
    M block
    ((hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeGreenToClockBoundaryTransport
      M block).mp htransport)

/-- With the two parity independence certificates, the corrected-native handoff
reaches the existing real HP carrier certificate. -/
theorem completedNativeRealHPCarrierCertificate_of_correctedNativeChiralBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeChiralBoundaryTransport M block)
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
  exact completedNativeRealHPCarrierCertificate_of_sameEdgeGreenToClockBoundaryTransport
    M block
    ((hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeGreenToClockBoundaryTransport
      M block).mp htransport)
    heven hodd

/-! ## The raw block no-go in the corrected vocabulary -/

/-- The material one-block native seed still fails the corrected-native
boundary handoff at the central coefficient.  This is a carrier no-go, not a
failure of the corrected causal/chiral readout. -/
theorem nativeZeroSeededClockBlock_not_correctedNativeChiralBoundaryTransport
    (M : ℕ) (s : ℂ) :
    ¬ HasCorrectedNativeChiralBoundaryTransport M
        (fun _ : Fin 1 => nativeZeroSeededClockBlock s) := by
  intro htransport
  exact nativeZeroSeededClockBlock_not_sameEdgeTransport M s
    ((hasCorrectedNativeChiralBoundaryTransport_iff_sameEdgeGreenToClockBoundaryTransport
      M (fun _ : Fin 1 => nativeZeroSeededClockBlock s)).mp htransport)

end

end CarrySelfAdjointOperator

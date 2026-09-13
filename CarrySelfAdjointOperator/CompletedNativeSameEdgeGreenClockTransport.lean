import CarrySelfAdjointOperator.CompletedNativeClockGreenMomentGate
import CarrySelfAdjointOperator.CompletedNativeCausalGreenProvenance
import CarrySelfAdjointOperator.CompletedC3TfvdBesselGateBridge
import CPFormal.Analytic.CpTfvdSameEdgeCompletedPrecompressionCollapse
import CPFormal.Analytic.CpTfvdSameEdgeReflectedEnergyFixedTimeNoGo
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics

noncomputable section

/-!
# Same-edge G_pre transport into the completed clock gate

The canonical same-edge construction has two logically distinct outputs.  The
completed precompression source keeps the visible fixed-time slot at zero and
stores the recovered Green energy in the residual slot.  Its reflected
readout is already the prime Green bulk.  The remaining transport to a common
fixed-time source is therefore stated separately, instead of identifying the
raw positive energy state with a fixed-time native moment state.

Once the causal Green/Wronskian coefficient is used, the clock gate needs only
one boundary equality: the clock first column must equal the corresponding
completed chiral Wronskian coefficient.  The interior coefficient equation and
the HP carrier certificate then follow from the existing clock theorems.

No Hankel matrix, Cholesky factor, Jacobi operator, or fitted positive proxy is
introduced here.
-/

/-! ## The exact same-edge source and readout -/

theorem canonicalSameEdgeCompletedPrecompressionSource_eq_greenEnergy
    (M : ℕ) (s : ℂ) :
    seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s =
      (0, nativeGpreGreenEnergyFirstLevelState (3 * M) s) := by
  exact seededTfvdGpreCompletedPrecompressionSource_sameEdge M s

theorem canonicalSameEdgeCompletedPrecompressionPrimeReadout_eq_greenBulk
    (M : ℕ) (s : ℂ) (p : Nat.Primes) :
    nativeGpreTfvdCompletedPrecompressionPrimeReadout p s
        (seededTfvdGpreCompletedPrecompressionSource
          (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
          M s) =
      (0, primeCarryGreenBulkCutoffProfile (3 * M) s p) := by
  exact nativeGpreTfvdCompletedPrecompressionPrimeReadout_sameEdge M s p

/-! ## The raw energy state is not the fixed-time transport -/

theorem canonicalSameEdgeRawEnergyTransport_not_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    ¬ SameEdgeReflectedEnergyTransportsToFixedTimeAt M s := by
  exact sameEdgeReflectedEnergyTransportsToFixedTimeAt_not_of_critical
    p hM hs hcritical

theorem canonicalSameEdgeRawCollapse_not_fixedTime_of_critical
    (p : Nat.Primes) {M : ℕ} (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hcritical : criticalDisplacement s.re = 0) :
    ¬ IsSeededTfvdGpreMomentCollapseAt
        (nativeGpreTfvdSameEdgeReflectedEnergyCollapseAt (3 * M)) M s := by
  exact isSeededTfvdGpreMomentCollapseAt_sameEdgeReflectedEnergy_not_of_critical
    p hM hs hcritical

/-! ## The corrected fixed-time transport discharges the C3 no-leak gate -/

theorem canonicalC3StructuralNoLeakAt_of_sameEdgeFixedTimeTransport
    (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (htransport :
      NativeGpreReflectedGapHasFixedTimeMomentStateAt (3 * N) s) :
    CanonicalC3StructuralNoLeakAt s := by
  rcases
      (nativeGpreReflectedGapHasFixedTimeMomentStateAt_iff_nativeRealization
        (3 * N) s).mp htransport with ⟨x, hx⟩
  exact canonicalC3StructuralNoLeakAt_of_nativeMomentSource
    N hN hs hzero x hx

/-! ## Wronskian-to-clock boundary transport -/

/-- The sole boundary calibration needed to feed the already proved causal
Green/Wronskian coefficients into a finite material-clock atlas. -/
def HasSameEdgeGreenToClockBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock) : Prop :=
  ∀ p : ℕ,
    seededClockAtlasCoefficient block p 0 =
      canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
        M (p + 1)

/-- The Wronskian boundary transport is exactly the completed ledger boundary
calibration consumed by the clock reduction. -/
theorem canonicalCompletedC3LedgerBoundary_of_sameEdgeGreenToClockBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    ∀ p : ℕ,
      seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p := by
  intro p
  calc
    seededClockAtlasCoefficient block p 0 =
        canonicalCompletedC3FullWronskianChiralResponseTaylorCoefficient
          M (p + 1) := htransport p
    _ = polarizedGreenMomentCoefficient
          canonicalCompletedNativeLogDerivativeMoment p 0 := by
      exact canonicalCompletedNativeCarryGreenChiralResponse_succCoefficient_eq_polarizedMoment
        M p 0
    _ = oddMomentResponseCoefficient
          canonicalCompletedNativeLogDerivativeMoment (p + 1) := by
      simp [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient,
        oddMomentResponseCoefficient]
    _ = canonicalCompletedC3LedgerBoundaryTaylorCoefficient M p := by
      exact
        (canonicalCompletedC3LedgerBoundaryTaylorCoefficient_eq_boundaryTarget
          M p).symm

/-- The same transport closes the full polarized Green coefficient equation
without introducing a Hankel or Jacobi layer. -/
theorem seededClockAtlasGreenMomentKernel_of_sameEdgeGreenToClockBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block) :
    IsComplexGreenWronskianMomentKernelGramRepresentation
      canonicalCompletedNativeLogDerivativeMoment
      (polarizedCoefficientParityJet (seededClockAtlasJet block)) := by
  exact seededClockAtlasGreenMomentKernel_of_completedLedgerBoundary
    M block
    (canonicalCompletedC3LedgerBoundary_of_sameEdgeGreenToClockBoundaryTransport
      M block htransport)

/-- Once the two parity families are independent, the Wronskian-to-clock
boundary transport reaches the existing real HP carrier certificate. -/
theorem completedNativeRealHPCarrierCertificate_of_sameEdgeGreenToClockBoundaryTransport
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasSameEdgeGreenToClockBoundaryTransport M block)
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
  exact completedNativeRealHPCarrierCertificate_of_calibratedSeededClockAtlas
    M block
    (canonicalCompletedC3LedgerBoundary_of_sameEdgeGreenToClockBoundaryTransport
      M block htransport)
    heven hodd

end

end CarrySelfAdjointOperator

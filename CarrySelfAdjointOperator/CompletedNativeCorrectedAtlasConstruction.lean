import CarrySelfAdjointOperator.CompletedNativeCorrectedClockBoundaryGate
import CarrySelfAdjointOperator.CompletedNativeCentralCarryAtlasEnergy
import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Tactic

/-!
# The corrected native atlas

This module packages the atlas that is already present in the native
construction.  Its positive coordinate carrier is the canonical all-bases
Parseval Green-frame carrier; its boundary coordinate is the corrected
causal/chiral state.  The two coordinates are kept separate, because the
first is the camera-free Hilbert atlas and the second is the signed native
readout used by the boundary gate.

No finite atomic clock block is reconstructed from moments here.  The clock
calibration remains the explicit first-column transport in
`CompletedNativeCorrectedClockBoundaryGate`.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open C3TraceDynamics
open GreenFrame.Concrete

noncomputable section

/-! ## Positive camera-free atlas coordinate -/

/-- The positive coordinate of the corrected native atlas.  This is only a
named view of the existing all-bases Parseval realization; no new carrier or
normalization is introduced. -/
abbrev CanonicalCompletedNativeCorrectedAtlasCarrier :=
  CanonicalCompletedGreenFrameCarrier

def canonicalCompletedNativeCorrectedAtlasState
    (s : ℂ) (hs : 0 < s.re) :
    CanonicalCompletedNativeCorrectedAtlasCarrier :=
  canonicalCompletedC3GradientParsevalAtlasState s hs

/-- The atlas keeps the external coordinate as a compatible datum in the
canonical concrete Green frame. -/
def canonicalCompletedNativeCorrectedAtlasExternal
    (s : ℂ) (hs : 0 < s.re) :
    CompatibleExternal
      (concreteAnalysisOperator canonicalCarryInfinitePartition) :=
  canonicalCompletedC3GradientCompatibleExternal s hs

theorem canonicalCompletedNativeCorrectedAtlasState_fst_eq_external
    (s : ℂ) (hs : 0 < s.re) :
    (canonicalCompletedNativeCorrectedAtlasState s hs).fst =
      (canonicalCompletedNativeCorrectedAtlasExternal s hs :
        ConcreteExternalSpace) := by
  exact canonicalCompletedC3GradientParsevalAtlasState_fst_eq_external s hs

theorem canonicalCompletedNativeCorrectedAtlasState_snd_eq_poisson
    (s : ℂ) (hs : 0 < s.re) :
    (canonicalCompletedNativeCorrectedAtlasState s hs).snd =
      restrictedPoisson
          (concreteSplitFrameBounds canonicalCarryInfinitePartition)
        (canonicalCompletedNativeCorrectedAtlasExternal s hs) := by
  exact canonicalCompletedC3GradientParsevalAtlasState_snd_eq_poisson s hs

/-- Parseval transport makes the atlas coordinate preserve the complete
complex Green inner product. -/
theorem canonicalCompletedNativeCorrectedAtlasState_inner_eq_gradient_inner
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) :
    inner ℂ
        (canonicalCompletedNativeCorrectedAtlasState r hr)
        (canonicalCompletedNativeCorrectedAtlasState s hs) =
      inner ℂ
        (canonicalCompletedC3DirichletGradientState r hr)
        (canonicalCompletedC3DirichletGradientState s hs) := by
  unfold canonicalCompletedNativeCorrectedAtlasState
  exact canonicalCompletedGreenFrameParsevalAnalysis_inner _ _

/-- The atlas inner product is the completed native Green Gram, before any
moment, Hankel, Cholesky, or Jacobi construction. -/
theorem canonicalCompletedNativeCorrectedAtlasState_inner_eq_rawGammaGram
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) :
    inner ℂ
        (canonicalCompletedNativeCorrectedAtlasState r hr)
        (canonicalCompletedNativeCorrectedAtlasState s hs) =
      canonicalCompletedC3RawGammaGram r s hr hs := by
  rw [canonicalCompletedNativeCorrectedAtlasState_inner_eq_gradient_inner
    r s hr hs]
  rfl

/-- Every finite sample of the positive atlas coordinate is positive
semidefinite.  Positivity comes from the actual native Hilbert state. -/
theorem canonicalCompletedNativeCorrectedAtlasState_sample_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hpoint : ∀ i, 0 < (point i).re) :
    (Matrix.of fun i j =>
      inner ℂ
        (canonicalCompletedNativeCorrectedAtlasState (point i) (hpoint i))
        (canonicalCompletedNativeCorrectedAtlasState (point j) (hpoint j))).PosSemidef := by
  rw [show (Matrix.of fun i j =>
      inner ℂ
        (canonicalCompletedNativeCorrectedAtlasState (point i) (hpoint i))
        (canonicalCompletedNativeCorrectedAtlasState (point j) (hpoint j))) =
      Matrix.gram ℂ (fun i =>
        canonicalCompletedNativeCorrectedAtlasState (point i) (hpoint i)) by
    ext i j
    rfl]
  exact Matrix.posSemidef_gram ℂ _

/-- The atlas retains all four causal Green channels.  The response-only
camera Gram is not substituted for the completed state. -/
theorem canonicalCompletedNativeCorrectedAtlasState_inner_eq_causalFourChannel
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) :
    inner ℂ
        (canonicalCompletedNativeCorrectedAtlasState r hr)
        (canonicalCompletedNativeCorrectedAtlasState s hs) =
      inner ℂ
          (canonicalCompletedC3DirichletGradientCausalGreenState base r hr)
          (canonicalCompletedC3DirichletGradientCausalGreenState base s hs) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientCausalGreenState base r hr)
          (canonicalCompletedC3DirichletGradientBoundaryReturnState
            hbase s hs) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientBoundaryReturnState
            hbase r hr)
          (canonicalCompletedC3DirichletGradientCausalGreenState base s hs) +
        inner ℂ
          (canonicalCompletedC3DirichletGradientBoundaryReturnState
            hbase r hr)
          (canonicalCompletedC3DirichletGradientBoundaryReturnState
            hbase s hs) := by
  rw [canonicalCompletedNativeCorrectedAtlasState_inner_eq_rawGammaGram,
    canonicalCompletedC3RawGammaGram_eq_causalFourChannel hbase r s hr hs]

/-! ## Central energy and corrected boundary coordinate -/

/-- At the self-dual point the positive atlas state carries exactly the
completed reflected Green energy. -/
theorem infiniteReflectedGreenEnergy_half_eq_correctedAtlas_norm_sq :
    infiniteReflectedGreenEnergy (1 / 2 : ℂ) =
      ‖canonicalCompletedNativeCorrectedAtlasState
          (1 / 2 : ℂ) (by norm_num)‖ ^ 2 := by
  change infiniteReflectedGreenEnergy (1 / 2 : ℂ) =
    ‖canonicalCentralCompletedGradientParsevalAtlasState‖ ^ 2
  exact infiniteReflectedGreenEnergy_half_eq_parsevalAtlas_norm_sq

/-- The boundary coordinate of the same corrected native atlas is the
existing causal/chiral state, not a positive proxy for it. -/
def canonicalCompletedNativeCorrectedAtlasBoundaryState
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    CanonicalCompletedC3CausalChiralBoundaryCarrier :=
  canonicalCompletedNativeCorrectedCausalChiralBoundaryState M z hzStrip.1

theorem canonicalCompletedNativeCorrectedAtlasBoundaryState_source_readout
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedC3EnrichedCausalChiralBoundaryReadout z
        (canonicalCompletedC3EnrichedChiralSourceState z hzStrip) =
      canonicalCompletedNativeCorrectedAtlasBoundaryState M z hzStrip := by
  exact canonicalCompletedNativeCorrectedCausalChiralBoundaryState_sourceState
    M z hzStrip

theorem canonicalCompletedNativeCorrectedAtlasBoundaryState_mem_relation
    (M : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedNativeCorrectedAtlasBoundaryState M z hzStrip ∈
      canonicalCompletedC3CausalChiralBoundaryRelation z := by
  exact canonicalCompletedNativeCorrectedCausalChiralBoundaryState_mem_relation
    M z hzStrip

theorem canonicalCompletedNativeCorrectedAtlasBoundaryState_cutoff_independent
    (M N : ℕ) (z : ℂ)
    (hzStrip : operatorHeightParameter z ∈ genuineCriticalStrip) :
    canonicalCompletedNativeCorrectedAtlasBoundaryState M z hzStrip =
      canonicalCompletedNativeCorrectedAtlasBoundaryState N z hzStrip := by
  exact canonicalCompletedNativeCorrectedCausalChiralBoundaryState_cutoff_independent
    M N z hzStrip

/-! ## The remaining material handoff -/

/-- The atlas exposes, without changing its carrier, the exact first-column
transport still required by the material seeded clock. -/
theorem canonicalCompletedNativeCorrectedAtlas_firstColumn_eq_boundary
    {ι : Type*} [Fintype ι]
    (M : ℕ) (block : ι → SeededClockBlock)
    (htransport : HasCorrectedNativeSeededClockBoundaryTransport M block)
    (p : ℕ) :
    seededClockAtlasCoefficient block p 0 =
      canonicalCompletedNativeCorrectedChiralBoundaryCoefficient M p := by
  exact htransport p

end

end CarrySelfAdjointOperator

import CarrySelfAdjointOperator.CompletedNativeCentralFiniteGreenVariation
import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
import CarrySelfAdjointOperator.CompletedC3CausalGreenGramSewing
import GreenFrame.Concrete.Analysis.RestrictedGraph
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Central carry energy in the canonical all-bases atlas

At the self-dual parameter, reflection fixes the ordinary Dirichlet-gradient
state.  Consequently the infinite reflected Green energy is its Hilbert norm
square.  The canonical all-bases Parseval analysis transports this same vector
isometrically and retains its seed, residual, depth-one, and bulk coordinates.

This is the lossless local-to-global statement supplied by the carry atlas.  It
does not identify the resulting radial energy with the completed-native zeroth
moment; the latter also contains the completed scalar boundary and product
channels.
-/

open scoped ComplexConjugate ComplexOrder InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter
open GreenFrame.Concrete

noncomputable section

/-- The completed ordinary-gradient state at the self-dual parameter. -/
def canonicalCentralCompletedDirichletGradientState : CarryVerticalL2 :=
  canonicalCompletedC3DirichletGradientState (1 / 2 : ℂ) (by norm_num)

/-- The same state analyzed by the canonical all-bases Parseval map. -/
def canonicalCentralCompletedGradientParsevalAtlasState :
    CanonicalCompletedGreenFrameCarrier :=
  canonicalCompletedGreenFrameParsevalAnalysis
    canonicalCentralCompletedDirichletGradientState

@[simp] theorem reflectedParameter_half :
    reflectedParameter (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  apply Complex.ext <;> norm_num [reflectedParameter]

/-- At the self-dual point, the reflected Green limit is exactly the norm
square of the completed ordinary-gradient state. -/
theorem infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq :
    infiniteReflectedGreenEnergy (1 / 2 : ℂ) =
      ‖canonicalCentralCompletedDirichletGradientState‖ ^ 2 := by
  have hstrip : (1 / 2 : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [genuineCriticalStrip]
  have hgreen :=
    finiteReflectedGradientPairing_re_tendsto_infiniteEnergy hstrip
  have hprefix :=
    canonicalCompletedC3DirichletGradientPrefixState_tendsto
      (s := (1 / 2 : ℂ)) (by norm_num)
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ) hprefix hprefix
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp hinner
  have hnorm : Tendsto
      (fun M : ℕ => (finiteReflectedGradientPairing M (1 / 2 : ℂ)).re)
      atTop
      (nhds (‖canonicalCentralCompletedDirichletGradientState‖ ^ 2)) := by
    convert hreal using 1
    · funext M
      simp only [Function.comp_apply]
      rw [finiteReflectedGradientPairing_eq_inner_completedC3Prefixes,
        reflectedParameter_half]
    · rw [inner_self_eq_norm_sq_to_K]
      norm_cast
  exact tendsto_nhds_unique hgreen hnorm

/-- Parseval analysis loses none of the centered reflected Green energy. -/
theorem infiniteReflectedGreenEnergy_half_eq_parsevalAtlas_norm_sq :
    infiniteReflectedGreenEnergy (1 / 2 : ℂ) =
      ‖canonicalCentralCompletedGradientParsevalAtlasState‖ ^ 2 := by
  rw [infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq]
  unfold canonicalCentralCompletedGradientParsevalAtlasState
  rw [canonicalCompletedGreenFrameParsevalAnalysis.norm_map]

/-- The complete complex inner product of the atlas state is the orthogonal
sum of its four literal channels: seed, residual, depth one, and bulk. -/
theorem inner_canonicalCentralCompletedGradientParsevalAtlasState_eq_channels :
    let state := canonicalCentralCompletedGradientParsevalAtlasState
    inner ℂ state state =
      inner ℂ state.fst.fst.fst state.fst.fst.fst +
        inner ℂ state.fst.fst.snd state.fst.fst.snd +
        inner ℂ state.fst.snd state.fst.snd +
        inner ℂ state.snd state.snd := by
  dsimp only
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    WithLp.prod_inner_apply]
  rfl

/-- Channel-separated atlas form of the positive infinite C3 bulk
sensitivity.  No camera coordinate is scalarized before this identity. -/
theorem canonicalCentralInfiniteGreenBulkFirstVariation_eq_atlasChannelSum :
    (canonicalCentralInfiniteGreenBulkFirstVariation : ℂ) =
      ((2 * Real.log 3 : ℝ) : ℂ) *
        (let state := canonicalCentralCompletedGradientParsevalAtlasState
         inner ℂ state.fst.fst.fst state.fst.fst.fst +
          inner ℂ state.fst.fst.snd state.fst.fst.snd +
          inner ℂ state.fst.snd state.fst.snd +
          inner ℂ state.snd state.snd) := by
  rw [show canonicalCentralInfiniteGreenBulkFirstVariation =
      2 * Real.log 3 * infiniteReflectedGreenEnergy (1 / 2 : ℂ) by
    rfl]
  rw [infiniteReflectedGreenEnergy_half_eq_parsevalAtlas_norm_sq]
  push_cast
  rw [show ((‖canonicalCentralCompletedGradientParsevalAtlasState‖ : ℂ) ^ 2) =
      inner ℂ canonicalCentralCompletedGradientParsevalAtlasState
        canonicalCentralCompletedGradientParsevalAtlasState by
    rw [inner_self_eq_norm_sq_to_K]
    rfl]
  rw [inner_canonicalCentralCompletedGradientParsevalAtlasState_eq_channels]

/-! ## The same atlas state on the exact compatible Poisson graph -/

/-- Source presentation used by the concrete Green frame. -/
def canonicalCentralCompletedGradientGreenFrameSource : State :=
  carryVerticalL2GreenFrameStateEquiv
    canonicalCentralCompletedDirichletGradientState

/-- External coordinate equipped with the proof that it comes from one
global source. -/
def canonicalCentralCompletedGradientCompatibleExternal :
    CompatibleExternal
      (concreteAnalysisOperator canonicalCarryInfinitePartition) :=
  (normalizedExternal
      (concreteAnalysisOperator canonicalCarryInfinitePartition)).rangeRestrict
    canonicalCentralCompletedGradientGreenFrameSource

/-- The external component of the Parseval atlas is exactly the compatible
external datum above. -/
theorem canonicalCentralCompletedGradientParsevalAtlasState_fst_eq_external :
    canonicalCentralCompletedGradientParsevalAtlasState.fst =
      (canonicalCentralCompletedGradientCompatibleExternal :
        ConcreteExternalSpace) := by
  rfl

/-- The bulk component is not independent data: it is reconstructed exactly
from the compatible external coordinate by the canonical Poisson operator. -/
theorem canonicalCentralCompletedGradientParsevalAtlasState_snd_eq_poisson :
    canonicalCentralCompletedGradientParsevalAtlasState.snd =
      restrictedPoisson
          (concreteSplitFrameBounds canonicalCarryInfinitePartition)
        canonicalCentralCompletedGradientCompatibleExternal := by
  symm
  exact restrictedPoisson_apply_external
    (concreteSplitFrameBounds canonicalCarryInfinitePartition)
    canonicalCentralCompletedGradientGreenFrameSource

/-- Exact graph-norm form of the centered reflected Green energy.  The first
term contains seed, residual, and depth-one channels; the second is the bulk
reconstructed from those compatible data. -/
theorem infiniteReflectedGreenEnergy_half_eq_compatiblePoissonGraphEnergy :
    infiniteReflectedGreenEnergy (1 / 2 : ℂ) =
      ‖(canonicalCentralCompletedGradientCompatibleExternal :
          ConcreteExternalSpace)‖ ^ 2 +
        ‖restrictedPoisson
            (concreteSplitFrameBounds canonicalCarryInfinitePartition)
          canonicalCentralCompletedGradientCompatibleExternal‖ ^ 2 := by
  calc
    infiniteReflectedGreenEnergy (1 / 2 : ℂ) =
        ‖canonicalCentralCompletedDirichletGradientState‖ ^ 2 :=
      infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq
    _ = ‖canonicalCentralCompletedGradientGreenFrameSource‖ ^ 2 := by
      unfold canonicalCentralCompletedGradientGreenFrameSource
      rw [carryVerticalL2GreenFrameStateEquiv.norm_map]
    _ = ‖normalizedExternal
          (concreteAnalysisOperator canonicalCarryInfinitePartition)
          canonicalCentralCompletedGradientGreenFrameSource‖ ^ 2 +
        ‖normalizedBulk
          (concreteAnalysisOperator canonicalCarryInfinitePartition)
          canonicalCentralCompletedGradientGreenFrameSource‖ ^ 2 :=
      (normalized_split_energy
        (concreteSplitFrameBounds
          canonicalCarryInfinitePartition).toComplexFrameBounds
        canonicalCentralCompletedGradientGreenFrameSource).symm
    _ = _ := by
      unfold canonicalCentralCompletedGradientCompatibleExternal
      rw [restrictedPoisson_apply_external]
      rfl

/-! ## Polarized compatible-graph kernel -/

/-- Source presentation of the completed ordinary-gradient state at an
arbitrary point of the positive half-plane. -/
def canonicalCompletedC3GradientGreenFrameSource
    (s : ℂ) (hs : 0 < s.re) : State :=
  carryVerticalL2GreenFrameStateEquiv
    (canonicalCompletedC3DirichletGradientState s hs)

/-- Canonical all-bases Parseval state of an arbitrary completed ordinary
gradient. -/
def canonicalCompletedC3GradientParsevalAtlasState
    (s : ℂ) (hs : 0 < s.re) : CanonicalCompletedGreenFrameCarrier :=
  canonicalCompletedGreenFrameParsevalAnalysis
    (canonicalCompletedC3DirichletGradientState s hs)

/-- Compatible external datum of an arbitrary completed ordinary gradient. -/
def canonicalCompletedC3GradientCompatibleExternal
    (s : ℂ) (hs : 0 < s.re) :
    CompatibleExternal
      (concreteAnalysisOperator canonicalCarryInfinitePartition) :=
  (normalizedExternal
      (concreteAnalysisOperator canonicalCarryInfinitePartition)).rangeRestrict
    (canonicalCompletedC3GradientGreenFrameSource s hs)

/-- The external coordinate of the parameterized Parseval atlas is exactly
the compatible datum reconstructed from the same global source. -/
theorem canonicalCompletedC3GradientParsevalAtlasState_fst_eq_external
    (s : ℂ) (hs : 0 < s.re) :
    (canonicalCompletedC3GradientParsevalAtlasState s hs).fst =
      (canonicalCompletedC3GradientCompatibleExternal s hs :
        ConcreteExternalSpace) := by
  rfl

/-- The bulk coordinate is the exact Poisson return of the compatible
external datum. -/
theorem canonicalCompletedC3GradientParsevalAtlasState_snd_eq_poisson
    (s : ℂ) (hs : 0 < s.re) :
    (canonicalCompletedC3GradientParsevalAtlasState s hs).snd =
      restrictedPoisson
          (concreteSplitFrameBounds canonicalCarryInfinitePartition)
        (canonicalCompletedC3GradientCompatibleExternal s hs) := by
  symm
  exact restrictedPoisson_apply_external
    (concreteSplitFrameBounds canonicalCarryInfinitePartition)
    (canonicalCompletedC3GradientGreenFrameSource s hs)

/-- Polarized inner product on the exact compatible Poisson graph.  Both the
external and reconstructed bulk channels remain present. -/
def canonicalCompletedC3GradientCompatiblePoissonGraphKernel
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) : ℂ :=
  inner ℂ
      (canonicalCompletedC3GradientCompatibleExternal r hr :
        ConcreteExternalSpace)
      (canonicalCompletedC3GradientCompatibleExternal s hs :
        ConcreteExternalSpace) +
    inner ℂ
      (restrictedPoisson
          (concreteSplitFrameBounds canonicalCarryInfinitePartition)
        (canonicalCompletedC3GradientCompatibleExternal r hr))
      (restrictedPoisson
          (concreteSplitFrameBounds canonicalCarryInfinitePartition)
        (canonicalCompletedC3GradientCompatibleExternal s hs))

/-- The compatible-graph kernel is exactly the completed raw C3 Green Gram,
as a complex polarized identity rather than only a diagonal norm equality. -/
theorem canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_rawGammaGram
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) :
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel r s hr hs =
      canonicalCompletedC3RawGammaGram r s hr hs := by
  unfold canonicalCompletedC3GradientCompatiblePoissonGraphKernel
    canonicalCompletedC3RawGammaGram
  rw [← canonicalCompletedC3GradientParsevalAtlasState_fst_eq_external,
    ← canonicalCompletedC3GradientParsevalAtlasState_fst_eq_external,
    ← canonicalCompletedC3GradientParsevalAtlasState_snd_eq_poisson,
    ← canonicalCompletedC3GradientParsevalAtlasState_snd_eq_poisson]
  rw [← canonicalCompletedGreenFrameParsevalAnalysis_inner
    (canonicalCompletedC3DirichletGradientState r hr)
    (canonicalCompletedC3DirichletGradientState s hs)]
  change
    inner ℂ (canonicalCompletedC3GradientParsevalAtlasState r hr).fst
          (canonicalCompletedC3GradientParsevalAtlasState s hs).fst +
        inner ℂ (canonicalCompletedC3GradientParsevalAtlasState r hr).snd
          (canonicalCompletedC3GradientParsevalAtlasState s hs).snd =
      inner ℂ (canonicalCompletedC3GradientParsevalAtlasState r hr)
        (canonicalCompletedC3GradientParsevalAtlasState s hs)
  exact (WithLp.prod_inner_apply _ _).symm

/-- Every finite sample of the compatible Poisson graph kernel is positive
semidefinite.  Positivity comes from the reconstructed global state, not from
a scalar Green readout. -/
theorem canonicalCompletedC3GradientCompatiblePoissonGraphKernel_posSemidef
    {ι : Type*} [Finite ι]
    (point : ι → ℂ) (hpoint : ∀ i, 0 < (point i).re) :
    (Matrix.of fun i j =>
      canonicalCompletedC3GradientCompatiblePoissonGraphKernel
        (point i) (point j) (hpoint i) (hpoint j)).PosSemidef := by
  rw [show (Matrix.of fun i j =>
      canonicalCompletedC3GradientCompatiblePoissonGraphKernel
        (point i) (point j) (hpoint i) (hpoint j)) =
      Matrix.gram ℂ (fun i =>
        canonicalCompletedC3DirichletGradientState (point i) (hpoint i)) by
    ext i j
    exact
      canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_rawGammaGram
        (point i) (point j) (hpoint i) (hpoint j)]
  exact Matrix.posSemidef_gram ℂ _

/-- The same compatible-graph kernel is the positive adjoint-square of the
complete causal response-plus-boundary readout.  Thus the Poisson graph does
not silently discard the boundary return or its two cross terms. -/
theorem
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_causalAdjointSquare
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) :
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel r s hr hs =
      inner ℂ
        (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
          hbase r hr)
        (ContinuousLinearMap.adjoint
          canonicalCompletedC3CausalGreenBoundarySum
          (canonicalCompletedC3CausalGreenBoundarySum
            (canonicalCompletedC3DirichletGradientCausalGreenBoundaryState
              hbase s hs))) := by
  rw [canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_rawGammaGram]
  exact canonicalCompletedC3RawGammaGram_eq_causalAdjointSquare
    hbase r s hr hs

/-- Fully expanded response/boundary form of the compatible Poisson graph
kernel.  In particular, neither mixed boundary term is treated as a defect to
be canceled. -/
theorem
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_causalFourChannel
    {base : ℕ} (hbase : FiniteNativeCarryOperator.Camera.IsSupported base)
    (r s : ℂ) (hr : 0 < r.re) (hs : 0 < s.re) :
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel r s hr hs =
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
  rw [canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_rawGammaGram]
  exact canonicalCompletedC3RawGammaGram_eq_causalFourChannel
    hbase r s hr hs

/-- Central specialization of the polarized graph identity. -/
theorem infiniteReflectedGreenEnergy_half_eq_compatiblePoissonGraphKernel :
    (infiniteReflectedGreenEnergy (1 / 2 : ℂ) : ℂ) =
      canonicalCompletedC3GradientCompatiblePoissonGraphKernel
        (1 / 2 : ℂ) (1 / 2 : ℂ) (by norm_num) (by norm_num) := by
  rw [canonicalCompletedC3GradientCompatiblePoissonGraphKernel_eq_rawGammaGram]
  unfold canonicalCompletedC3RawGammaGram
  rw [inner_self_eq_norm_sq_to_K]
  have h := congrArg (fun x : ℝ => (x : ℂ))
    infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq
  simpa [canonicalCentralCompletedDirichletGradientState] using h

/-- The diagonal compatible-graph readout at the self-dual point is strictly
positive. -/
theorem
    canonicalCompletedC3GradientCompatiblePoissonGraphKernel_half_re_pos :
    0 < (canonicalCompletedC3GradientCompatiblePoissonGraphKernel
      (1 / 2 : ℂ) (1 / 2 : ℂ) (by norm_num) (by norm_num)).re := by
  rw [← infiniteReflectedGreenEnergy_half_eq_compatiblePoissonGraphKernel]
  simp only [Complex.ofReal_re]
  exact infiniteReflectedGreenEnergy_pos (by
    constructor <;> norm_num [genuineCriticalStrip])

end

end CarrySelfAdjointOperator

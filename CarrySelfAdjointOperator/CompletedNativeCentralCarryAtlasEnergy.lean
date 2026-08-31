import CarrySelfAdjointOperator.CompletedNativeCentralFiniteGreenVariation
import CarrySelfAdjointOperator.BR2GreenFrameDslopeLimitBridge
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

open scoped ComplexConjugate InnerProductSpace

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open Filter

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

end

end CarrySelfAdjointOperator

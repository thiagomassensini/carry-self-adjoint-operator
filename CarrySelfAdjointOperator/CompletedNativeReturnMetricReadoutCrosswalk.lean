import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.ReturnMetricPolarizedKernel
import GreenFrame.Concrete.Analysis.AmbientPoisson
import GreenFrame.Concrete.Analysis.StaticPoisson
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# Completed native return-metric readout crosswalk

The finite `ReturnMetric` API in `NativeCarrySpectralWeyl` is matrix-valued and
requires finite endpoint and bulk types.  The completed Green frame has a
canonical Hilbert-valued analogue already forced by its normalized Parseval
split:

* endpoint: `normalizedExternal`;
* bulk: `normalizedBulk`;
* return: `ambientPoisson`;
* Poisson graph: `ambientPoisson` itself;
* return metric: `1 + P† P`.

This file proves the corresponding continuous-linear-map cancellation and its
positive graph kernel.  It does not invent a finite matrix specialization and
does not identify this Green-frame graph kernel with the completed-native
`dslope` kernel.  In fact its central value is strictly larger than the native
zeroth moment, so the concrete ordinary-gradient realization is an explicit
failed sewing candidate.  This is a transport obstruction for this state and
metric, not a no-go theorem for another native return realization.
-/

open scoped InnerProduct InnerProductSpace ComplexOrder

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open GreenFrame.Concrete

noncomputable section

variable {H E B : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- Hilbert-valued return metric `I + P†P`, the continuous-linear-map lift of
`NativeCarrySpectralWeyl.Finite.returnMetric`. -/
def clmReturnMetric (poisson : E →L[ℂ] B) : E →L[ℂ] E :=
  (1 : E →L[ℂ] E) + poisson† ∘L poisson

/-- The return metric is self-adjoint. -/
theorem clmReturnMetric_isSelfAdjoint (poisson : E →L[ℂ] B) :
    IsSelfAdjoint (clmReturnMetric poisson) := by
  unfold clmReturnMetric
  apply IsSelfAdjoint.add (IsSelfAdjoint.one _)
  apply IsSelfAdjoint.of_nonneg
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self poisson)

/-- The return metric is positive in the continuous-linear-map order. -/
theorem clmReturnMetric_isPositive (poisson : E →L[ℂ] B) :
    (clmReturnMetric poisson).IsPositive := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  apply add_nonneg
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      ContinuousLinearMap.isPositive_one
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self poisson)

/-- Continuous-linear-map form of the finite return-metric cancellation.
The two assumptions are exactly `P E = B` and `E†E+B†B=I`. -/
theorem clmEndpoint_returnMetric_pullback_isometry
    (endpointMap : H →L[ℂ] E) (bulkMap : H →L[ℂ] B)
    (poisson : E →L[ℂ] B)
    (hpoisson : poisson ∘L endpointMap = bulkMap)
    (hisometry : endpointMap† ∘L endpointMap + bulkMap† ∘L bulkMap =
      (1 : H →L[ℂ] H)) :
    endpointMap† ∘L clmReturnMetric poisson ∘L endpointMap =
      (1 : H →L[ℂ] H) := by
  unfold clmReturnMetric
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, one_apply_eq_self]
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]
  have hpoissonX := congrArg (fun f : H →L[ℂ] B => f x) hpoisson
  have hpoissonY := congrArg (fun f : H →L[ℂ] B => f y) hpoisson
  have hpoissonX' : poisson (endpointMap x) = bulkMap x := by
    simpa only [ContinuousLinearMap.comp_apply] using hpoissonX
  have hpoissonY' : poisson (endpointMap y) = bulkMap y := by
    simpa only [ContinuousLinearMap.comp_apply] using hpoissonY
  rw [hpoissonX', hpoissonY']
  have hisometryInner :=
    congrArg (fun f : H →L[ℂ] H => inner ℂ (f x) y) hisometry
  simp only [add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self] at hisometryInner
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left] at hisometryInner
  exact hisometryInner

/-- Canonical completed Green analysis used below.  Its source is `State` and
its codomain is the full paper coefficient space. -/
abbrev canonicalNativeGreenFrameOperator :
    State →L[ℂ] ConcreteAnalysisSpace :=
  concreteAnalysisOperator canonicalCarryInfinitePartition

/-- Native endpoint map: normalized external (seed/residual/depth-one) data. -/
abbrev canonicalNativeGreenFrameExternal :
    State →L[ℂ] ConcreteExternalSpace :=
  normalizedExternal canonicalNativeGreenFrameOperator

/-- Native bulk map: normalized depth-at-least-two data. -/
abbrev canonicalNativeGreenFrameBulk :
    State →L[ℂ] BulkGreenSpace :=
  normalizedBulk canonicalNativeGreenFrameOperator

/-- Native Poisson return from external to bulk data. -/
abbrev canonicalNativeGreenFramePoisson :
    ConcreteExternalSpace →L[ℂ] BulkGreenSpace :=
  ambientPoisson canonicalNativeGreenFrameOperator

/-- The graph return metric forced by the canonical completed Green frame. -/
def canonicalNativeGreenFrameReturnMetric :
    ConcreteExternalSpace →L[ℂ] ConcreteExternalSpace :=
  clmReturnMetric canonicalNativeGreenFramePoisson

/-- The normalized Green split has the exact Parseval Gram identity. -/
theorem canonicalNativeGreenFrameParsevalSplit :
    canonicalNativeGreenFrameExternal† ∘L canonicalNativeGreenFrameExternal +
        canonicalNativeGreenFrameBulk† ∘L canonicalNativeGreenFrameBulk =
      (1 : State →L[ℂ] State) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  have hinner := (canonicalParseval
    (concreteSplitFrameBounds canonicalCarryInfinitePartition).toComplexFrameBounds).inner_map_map x y
  simpa [canonicalParseval_apply, canonicalAnalysis, normalizedExternal, normalizedBulk,
    rawExternal, rawBulk, concreteAnalysisOperator_apply,
    WithLp.prod_inner_apply, ContinuousLinearMap.comp_apply] using hinner

/-- The canonical ambient Poisson return reconstructs the normalized bulk map. -/
theorem canonicalNativeGreenFramePoisson_intertwines :
    canonicalNativeGreenFramePoisson ∘L canonicalNativeGreenFrameExternal =
      canonicalNativeGreenFrameBulk := by
  simpa only [canonicalNativeGreenFramePoisson, canonicalNativeGreenFrameExternal,
    canonicalNativeGreenFrameBulk, canonicalNativeGreenFrameOperator] using
    ambientPoisson_intertwining
      (concreteSplitFrameBounds canonicalCarryInfinitePartition)

/-- The concrete Green-frame return metric is self-adjoint. -/
theorem canonicalNativeGreenFrameReturnMetric_isSelfAdjoint :
    IsSelfAdjoint canonicalNativeGreenFrameReturnMetric := by
  exact clmReturnMetric_isSelfAdjoint canonicalNativeGreenFramePoisson

/-- The concrete Green-frame return metric is positive. -/
theorem canonicalNativeGreenFrameReturnMetric_isPositive :
    canonicalNativeGreenFrameReturnMetric.IsPositive := by
  exact clmReturnMetric_isPositive canonicalNativeGreenFramePoisson

/-- Concrete return-metric isometry for the completed native Green frame. -/
theorem canonicalNativeGreenFrameReturnMetric_isometry :
    canonicalNativeGreenFrameExternal† ∘L canonicalNativeGreenFrameReturnMetric ∘L
          canonicalNativeGreenFrameExternal =
      (1 : State →L[ℂ] State) := by
  apply clmEndpoint_returnMetric_pullback_isometry
    canonicalNativeGreenFrameExternal canonicalNativeGreenFrameBulk
    canonicalNativeGreenFramePoisson canonicalNativeGreenFramePoisson_intertwines
    canonicalNativeGreenFrameParsevalSplit

/-- The native endpoint-plus-Poisson graph kernel. -/
def canonicalNativeGreenFrameReturnReadout (x y : State) : ℂ :=
  inner ℂ (canonicalNativeGreenFrameExternal x)
    (canonicalNativeGreenFrameReturnMetric (canonicalNativeGreenFrameExternal y))

/-- Expanded Gram factorization of the graph kernel. -/
def canonicalNativeGreenFrameReturnKernel (x y : State) : ℂ :=
  inner ℂ (canonicalNativeGreenFrameExternal x)
    (canonicalNativeGreenFrameExternal y) +
  inner ℂ (canonicalNativeGreenFramePoisson (canonicalNativeGreenFrameExternal x))
    (canonicalNativeGreenFramePoisson (canonicalNativeGreenFrameExternal y))

/-- The return-metric readout is exactly the endpoint-plus-bulk Gram. -/
theorem canonicalNativeGreenFrameReturnReadout_eq_kernel (x y : State) :
    canonicalNativeGreenFrameReturnReadout x y =
      canonicalNativeGreenFrameReturnKernel x y := by
  unfold canonicalNativeGreenFrameReturnReadout canonicalNativeGreenFrameReturnMetric
    clmReturnMetric canonicalNativeGreenFrameReturnKernel
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  rw [inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The graph kernel is the inner product of the original completed state. -/
theorem canonicalNativeGreenFrameReturnKernel_eq_state_inner (x y : State) :
    canonicalNativeGreenFrameReturnKernel x y = inner ℂ x y := by
  unfold canonicalNativeGreenFrameReturnKernel
  have hpoisson := canonicalNativeGreenFramePoisson_intertwines
  have hpoissonX := congrArg (fun f : State →L[ℂ] BulkGreenSpace => f x) hpoisson
  have hpoissonY := congrArg (fun f : State →L[ℂ] BulkGreenSpace => f y) hpoisson
  have hpoissonX' : canonicalNativeGreenFramePoisson
        (canonicalNativeGreenFrameExternal x) =
      canonicalNativeGreenFrameBulk x := by
    simpa only [ContinuousLinearMap.comp_apply] using hpoissonX
  have hpoissonY' : canonicalNativeGreenFramePoisson
        (canonicalNativeGreenFrameExternal y) =
      canonicalNativeGreenFrameBulk y := by
    simpa only [ContinuousLinearMap.comp_apply] using hpoissonY
  rw [hpoissonX', hpoissonY']
  have hsplit := canonicalNativeGreenFrameParsevalSplit
  have hsplitInner := congrArg (fun f : State →L[ℂ] State => inner ℂ (f x) y) hsplit
  simp only [add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self] at hsplitInner
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left] at hsplitInner
  exact hsplitInner

/-- The compressed return readout is consequently the original state Gram. -/
theorem canonicalNativeGreenFrameReturnReadout_eq_state_inner (x y : State) :
    canonicalNativeGreenFrameReturnReadout x y = inner ℂ x y := by
  rw [canonicalNativeGreenFrameReturnReadout_eq_kernel,
    canonicalNativeGreenFrameReturnKernel_eq_state_inner]

/-- Every finite section of the native graph kernel is a Gram matrix. -/
theorem canonicalNativeGreenFrameReturnKernel_posSemidef
    {ι : Type*} [Finite ι] (point : ι → State) :
    (Matrix.of fun i j => canonicalNativeGreenFrameReturnKernel
      (point i) (point j)).PosSemidef := by
  have hgram : (Matrix.of fun i j => canonicalNativeGreenFrameReturnKernel
      (point i) (point j)) = Matrix.gram ℂ point := by
    ext i j
    simp only [Matrix.gram, Matrix.of_apply]
    rw [canonicalNativeGreenFrameReturnKernel_eq_state_inner]
  rw [hgram]
  exact Matrix.posSemidef_gram ℂ point

/-- Central defect of the canonical graph return kernel from the native zeroth
logarithmic moment. -/
def canonicalNativeReturnMetricCentralDefect : ℝ :=
  (canonicalNativeGreenFrameReturnKernel
      canonicalCentralCompletedGradientGreenFrameSource
      canonicalCentralCompletedGradientGreenFrameSource).re -
    canonicalCompletedNativeLogDerivativeMoment 0

/-- At the center, the canonical graph kernel is exactly the completed
ordinary reflected Green energy. -/
theorem canonicalNativeReturnMetricCentralKernel_eq_gradient_energy :
    (canonicalNativeGreenFrameReturnKernel
      canonicalCentralCompletedGradientGreenFrameSource
      canonicalCentralCompletedGradientGreenFrameSource).re =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) := by
  rw [canonicalNativeGreenFrameReturnKernel_eq_state_inner]
  unfold canonicalCentralCompletedGradientGreenFrameSource
  rw [inner_self_eq_norm_sq_to_K]
  have hnorm := infiniteReflectedGreenEnergy_half_eq_gradient_norm_sq
  calc
    (((‖carryVerticalL2GreenFrameStateEquiv
        canonicalCentralCompletedDirichletGradientState‖ : ℝ) : ℂ) ^ 2).re =
        ‖carryVerticalL2GreenFrameStateEquiv
          canonicalCentralCompletedDirichletGradientState‖ ^ 2 := by
            rw [← Complex.ofReal_pow, Complex.ofReal_re]
    _ = ‖canonicalCentralCompletedDirichletGradientState‖ ^ 2 := by
          rw [carryVerticalL2GreenFrameStateEquiv.norm_map]
    _ = infiniteReflectedGreenEnergy (1 / 2 : ℂ) := hnorm.symm

/-- The central return graph is strictly above the native zeroth moment. -/
theorem canonicalNativeReturnMetricCentralDefect_pos :
    0 < canonicalNativeReturnMetricCentralDefect := by
  unfold canonicalNativeReturnMetricCentralDefect
  rw [canonicalNativeReturnMetricCentralKernel_eq_gradient_energy]
  have hE := infiniteReflectedGreenEnergy_half_gt_sixteenth
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- Equivalent explicit inequality for the center mismatch. -/
theorem canonicalNativeReturnMetricCentralKernel_gt_nativeMoment :
    canonicalCompletedNativeLogDerivativeMoment 0 <
      (canonicalNativeGreenFrameReturnKernel
      canonicalCentralCompletedGradientGreenFrameSource
      canonicalCentralCompletedGradientGreenFrameSource).re := by
  rw [canonicalNativeReturnMetricCentralKernel_eq_gradient_energy]
  have hE := infiniteReflectedGreenEnergy_half_gt_sixteenth
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

/-- The central graph readout cannot equal the native zeroth moment for this
ordinary-gradient return realization. -/
theorem canonicalNativeReturnMetricCentralKernel_ne_nativeMoment :
    (canonicalNativeGreenFrameReturnKernel
      canonicalCentralCompletedGradientGreenFrameSource
      canonicalCentralCompletedGradientGreenFrameSource).re ≠
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  exact (ne_of_gt canonicalNativeReturnMetricCentralKernel_gt_nativeMoment)

/-- The real central defect is exactly the graph energy minus the native
zeroth moment. -/
theorem canonicalNativeReturnMetricCentralDefect_eq_energy_sub_native :
    canonicalNativeReturnMetricCentralDefect =
      infiniteReflectedGreenEnergy (1 / 2 : ℂ) -
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  unfold canonicalNativeReturnMetricCentralDefect
  rw [canonicalNativeReturnMetricCentralKernel_eq_gradient_energy]

end
end CarrySelfAdjointOperator

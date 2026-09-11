import CarrySelfAdjointOperator.CompletedC3MixedGreenWronskianDefect
import CarrySelfAdjointOperator.CompletedNativeTfvdGreenShiftedHankelFactorization
import Mathlib.Tactic

/-!
# Polarized native TFVD--Green moment-kernel ledger

This module packages the already-proved two-parameter TFVD/Green ledger as a
camera-free native crosswalk.  It keeps the local Green provenance, ordered
cross provenance, four readout residuals, and the independent head--tail
completion correction visible.  No moment sequence, Hankel matrix, or
pre-existing Green-kernel hypothesis is used to define any of these objects.

The resulting theorem is deliberately a residual theorem: the existing
finite ledger gives Wronskian = finite Green + explicit defect, and its
completion limit is Wronskian - completed Green.  A positive Hilbert vector
factorization of the completed native Wronskian is not manufactured here.
-/

open scoped BigOperators ComplexConjugate Topology

namespace CarrySelfAdjointOperator

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- The four named aggregate channels retained by the native two-parameter ledger.
The first three are the finite structural channels (the readout field contains
the four local residual legs); `completion` is the independent head--tail
correction. -/
structure CanonicalNativePolarizedTfvdGreenLedger where
  greenProvenance : ℂ
  crossProvenance : ℂ
  readoutResidual : ℂ
  completion : ℂ

/-- Camera-free specialization of the mixed two-parameter TFVD/Green ledger.
The parameters remain independent: `z` supplies the reflected/log-jet leg and
`w` supplies the direct value leg. -/
def canonicalNativePolarizedTfvdGreenLedger
    (M : ℕ) (z w : ℂ) : CanonicalNativePolarizedTfvdGreenLedger :=
  { greenProvenance :=
      canonicalMixedBoundaryGreenProvenance
        M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
    crossProvenance :=
      canonicalMixedBoundaryCrossProvenance
        M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
    readoutResidual :=
      canonicalMixedBoundaryReadoutResidualCorrection
        M tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) z w
    completion := canonicalC3MixedTailCompletionDefect M z w }

/-- The structural part of the ledger is exactly the sum of the three
independently defined finite channels. -/
theorem canonicalNativePolarizedTfvdGreenLedger_structural_eq
    (M : ℕ) (z w : ℂ) :
    (canonicalNativePolarizedTfvdGreenLedger M z w).greenProvenance +
        (canonicalNativePolarizedTfvdGreenLedger M z w).crossProvenance +
        (canonicalNativePolarizedTfvdGreenLedger M z w).readoutResidual =
      canonicalC3FiniteMixedStructuralDefect M z w := by
  rfl

/-- The completed raw mixed Wronskian is the finite reflected Green form plus
all retained ledger channels. -/
theorem canonicalNativePolarizedTfvdGreenLedger_identity
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter z)) +
        (canonicalNativePolarizedTfvdGreenLedger M z w).greenProvenance +
        (canonicalNativePolarizedTfvdGreenLedger M z w).crossProvenance +
        (canonicalNativePolarizedTfvdGreenLedger M z w).readoutResidual +
        (canonicalNativePolarizedTfvdGreenLedger M z w).completion := by
  rw [canonicalCompletedC3RawMixedWronskian_eq_green_add_totalDefect
    M hz hw]
  unfold canonicalC3FiniteMixedTotalDefect
  rw [← canonicalNativePolarizedTfvdGreenLedger_structural_eq M z w]
  simp only [canonicalNativePolarizedTfvdGreenLedger]
  ring

/-- Universal local two-parameter identity.  The four local legs and their
cross provenance are preserved before any finite or completed summation. -/
theorem canonicalNativePolarizedTfvdGreen_local_identity
    {ι : Type*} [Fintype ι]
    (valueZ companionZ valueW companionW : ℂ)
    (legs : ReflectedBoundarySynthesisData ι) :
    mixedScalarBoundaryWedge valueZ companionZ valueW companionW =
      (∑ i : ι,
        sameSEdgeBoundaryWedge
          (legs.left i) (legs.right i)
          (legs.jetLeft i) (legs.jetRight i)) +
        twoLegBoundaryCrossProvenance
          legs.left legs.right legs.jetLeft legs.jetRight +
        mixedBoundaryResidualCorrection
          valueZ companionZ valueW companionW legs := by
  exact mixedScalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    valueZ companionZ valueW companionW legs

/-- Exact canonical finite head identity, with the finite Green provenance,
ordered cross provenance, and four-leg readout residual kept explicit. -/
theorem canonicalNativePolarizedTfvdGreen_head_identity
    (M : ℕ) (z w : ℂ) :
    mixedScalarBoundaryWedge
        (finiteBracketedDirichletChart 3 M z)
        (finiteCanonicalLogBracketChart M z)
        (finiteBracketedDirichletChart 3 M w)
        (finiteCanonicalLogBracketChart M w) =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter z)) +
        canonicalC3FiniteMixedStructuralDefect M z w := by
  exact canonicalC3FiniteMixedHeadWronskian_eq_green_add_structuralDefect M z w

/-- The independent completion correction is exactly the mixed wedge change
when the two parameter-dependent tails are added. -/
theorem canonicalNativePolarizedTfvdGreen_completion_identity
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
      mixedScalarBoundaryWedge
          (finiteBracketedDirichletChart 3 M z)
          (finiteCanonicalLogBracketChart M z)
          (finiteBracketedDirichletChart 3 M w)
          (finiteCanonicalLogBracketChart M w) +
        canonicalC3MixedTailCompletionDefect M z w := by
  exact canonicalCompletedC3RawMixedWronskian_eq_head_add_tailDefect M hz hw

/-- Explicit native polarized defect: it is defined by the TFVD/Green ledger,
not as a moment or Hankel difference. -/
def canonicalNativePolarizedTfvdGreenMomentKernelDefect
    (M : ℕ) (z w : ℂ) : ℂ :=
  canonicalC3FiniteMixedTotalDefect M z w

/-- The total defect is the sum of the three structural channels and the
independent completion channel, with no moment-side definition. -/
theorem canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_ledger_total
    (M : ℕ) (z w : ℂ) :
    canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w =
      (canonicalNativePolarizedTfvdGreenLedger M z w).greenProvenance +
        (canonicalNativePolarizedTfvdGreenLedger M z w).crossProvenance +
        (canonicalNativePolarizedTfvdGreenLedger M z w).readoutResidual +
        (canonicalNativePolarizedTfvdGreenLedger M z w).completion := by
  unfold canonicalNativePolarizedTfvdGreenMomentKernelDefect
    canonicalC3FiniteMixedTotalDefect
    canonicalC3FiniteMixedStructuralDefect
    canonicalMixedBoundaryStructuralDefect
  simp only [canonicalNativePolarizedTfvdGreenLedger]

/-- The named defect is exactly the completed raw Wronskian minus the finite
reflected Green form. -/
theorem canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_wronskian_sub_green
    (M : ℕ) {z w : ℂ} (hz : -1 < z.re) (hw : -1 < w.re) :
    canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w =
      canonicalCompletedC3RawMixedWronskian z w -
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) w)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter z)) := by
  exact canonicalC3FiniteMixedTotalDefect_eq_wronskian_sub_green M hz hw

/-- The completed native defect exposed by the finite ledger converges to one
explicit residual: completed raw Wronskian minus completed reflected Green.
No vanishing is inserted. -/
theorem canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto
    {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1)
    (hw : 0 < w.re) :
    Tendsto
      (fun M : ℕ =>
        canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w)
      atTop
      (nhds
        (canonicalCompletedC3RawMixedWronskian z w -
          canonicalCompletedC3MixedRadialGreenKernel z w hw
            (by simpa [reflectedParameter] using sub_pos.mpr hzUpper))) := by
  exact canonicalC3FiniteMixedTotalDefect_tendsto hz hzUpper hw

/-- The native completed Wronskian/Green kernel equality is equivalent to the
vanishing of the displayed TFVD/Green defect limit. -/
theorem canonicalNativePolarizedTfvdGreenMomentKernel_eq_iff_defect_limit_zero
    {z w : ℂ} (hz : 0 < z.re) (hzUpper : z.re < 1)
    (hw : 0 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
        canonicalCompletedC3MixedRadialGreenKernel z w hw
          (by simpa [reflectedParameter] using sub_pos.mpr hzUpper) ↔
      Tendsto
        (fun M : ℕ =>
          canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w)
        atTop (nhds 0) := by
  exact (canonicalC3FiniteMixedTotalDefect_tendsto_zero_iff
    hz hzUpper hw).symm

/-- If a genuine native Hilbert jet Gram is supplied independently, the
existing odd-prefix factorization consumes it.  This adapter makes explicit
that the present ledger does not itself discharge that Gram hypothesis. -/
theorem canonicalNativePolarizedTfvdGreenMomentKernel_implies_shiftedFactorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsGreenWronskianMomentKernelGramRepresentation moments jet)
    (N : ℕ) :
    greenJetOddPrefixGram jet N = shiftedHankel moments N := by
  exact greenJetOddPrefixGram_eq_shiftedHankel_of_greenRepresentation hrep N

end

end CarrySelfAdjointOperator

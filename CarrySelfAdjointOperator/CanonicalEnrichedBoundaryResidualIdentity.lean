import CarrySelfAdjointOperator.EnrichedTfvdBoundaryEdgeFlattening
import CarrySelfAdjointOperator.ReflectedScalarBoundaryResidual
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import Mathlib.Tactic

/-!
# Canonical enriched boundary identity with explicit residuals

The canonical arithmetic pair is flattened into its two retained edges per C3
block.  No claim is made that those local edge sums equal the two synthesized
scalar readouts.  Their mismatch is retained in four linear residuals, whose
exact bilinear contribution was derived in
`ReflectedScalarBoundaryResidual`.

Combining that universal identity with the public provenance-resolved C3 Green
identity gives, before any zero or critical-line hypothesis,

`scalar Wronskian = reflected C3 Green form`

plus exactly three explicit channels:

1. public Green provenance;
2. ordered cross-edge synthesis provenance;
3. four-leg readout residual correction.

Hence the remaining scalar boundary seam is equivalent to cancellation of
those three channels.  This is an unconditional identity, not a synthesis
premise disguised as notation.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

/-- Canonical arithmetic value/log-jet pair. -/
def canonicalBoundaryResidualPair
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    EnrichedTfvdValueLogJetPair :=
  canonicalEnrichedTfvdValueLogJetPair kappa omega s

/-- Canonical transported pair data. -/
def canonicalBoundaryResidualData
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    FiniteC3EnrichedTfvdPairTransportData M :=
  finiteC3EnrichedTfvdPairTransport M kappa omega s
    (canonicalBoundaryResidualPair kappa omega s)

/-- Actual two-edge flattening of the canonical pair. -/
def canonicalBoundaryResidualLegs
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    ReflectedBoundarySynthesisData (Fin M × Fin 2) :=
  let pair := canonicalBoundaryResidualPair kappa omega s
  {
    left := enrichedTfvdBoundaryEdgeLeft M kappa omega pair
    right := enrichedTfvdBoundaryEdgeRight M kappa omega pair
    jetLeft := enrichedTfvdBoundaryEdgeJetLeft M kappa omega pair
    jetRight := enrichedTfvdBoundaryEdgeJetRight M kappa omega pair
  }

/-- Canonical ordered cross-edge provenance. -/
def canonicalBoundaryCrossProvenance
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  let legs := canonicalBoundaryResidualLegs M kappa omega s
  twoLegBoundaryCrossProvenance
    legs.left legs.right legs.jetLeft legs.jetRight

/-- Canonical correction contributed by the four linear readout residuals. -/
def canonicalBoundaryReadoutResidualCorrection
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  let data := canonicalBoundaryResidualData M kappa omega s
  let legs := canonicalBoundaryResidualLegs M kappa omega s
  reflectedBoundaryResidualCorrection
    data.valueReadout data.logJetReadout legs

/-- Unconditional canonical scalar boundary decomposition. -/
theorem canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    scalarBoundaryWedge
        (canonicalBoundaryResidualData M kappa omega s).valueReadout
        (canonicalBoundaryResidualData M kappa omega s).logJetReadout =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        (finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
          canonicalBoundaryCrossProvenance M kappa omega s +
          canonicalBoundaryReadoutResidualCorrection
            M kappa omega s) := by
  let pair := canonicalBoundaryResidualPair kappa omega s
  let data := canonicalBoundaryResidualData M kappa omega s
  let legs := canonicalBoundaryResidualLegs M kappa omega s
  have hlocal :
      (∑ mr : Fin M × Fin 2,
        sameSEdgeBoundaryWedge
          (legs.left mr) (legs.right mr)
          (legs.jetLeft mr) (legs.jetRight mr)) =
        finiteC3EnrichedTfvdPairBoundaryForm M data := by
    simpa [pair, data, legs,
      canonicalBoundaryResidualPair,
      canonicalBoundaryResidualData,
      canonicalBoundaryResidualLegs] using
      (sum_enrichedTfvdBoundaryEdges_eq_pairBoundaryForm
        M kappa omega s pair)
  have htrace :
      scalarBoundaryWedge data.valueReadout data.logJetReadout =
        finiteC3EnrichedTfvdPairBoundaryForm M data +
          twoLegBoundaryCrossProvenance
              legs.left legs.right legs.jetLeft legs.jetRight +
            reflectedBoundaryResidualCorrection
              data.valueReadout data.logJetReadout legs := by
    rw [scalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection,
      hlocal]
  have hgreen :
      finiteC3EnrichedTfvdPairBoundaryForm M data -
          finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) := by
    simpa [data, pair,
      canonicalBoundaryResidualData,
      canonicalBoundaryResidualPair] using
      (finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
        M hkappa omega homega s)
  change scalarBoundaryWedge data.valueReadout data.logJetReadout = _
  rw [htrace]
  unfold canonicalBoundaryCrossProvenance
    canonicalBoundaryReadoutResidualCorrection
  dsimp only
  linear_combination hgreen

/-- Exact residual criterion: the canonical scalar trace equals the reflected
C3 Green form iff the three explicit defect channels cancel. -/
theorem canonicalEnrichedScalarBoundary_eq_green_iff_explicitDefects_cancel
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    scalarBoundaryWedge
        (canonicalBoundaryResidualData M kappa omega s).valueReadout
        (canonicalBoundaryResidualData M kappa omega s).logJetReadout =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) ↔
      finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
        canonicalBoundaryCrossProvenance M kappa omega s +
        canonicalBoundaryReadoutResidualCorrection M kappa omega s = 0 := by
  rw [canonicalEnrichedScalarBoundary_eq_green_add_explicitDefects
    M hkappa omega homega s]
  constructor
  · intro h
    apply add_left_cancel
    simpa using h
  · intro h
    rw [h, add_zero]

end

end CarrySelfAdjointOperator

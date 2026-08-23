import CarrySelfAdjointOperator.EnrichedTfvdBoundaryEdgeFlattening
import CarrySelfAdjointOperator.ReflectedScalarBoundaryTrace
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import Mathlib.Tactic

/-!
# Canonical enriched TFVD scalar-trace reduction

This module specializes the reflected four-leg boundary trace to the canonical
arithmetic value/log-jet pair and its exact `Fin M × Fin 2` edge flattening.

The existing public theorem already proves

`pair boundary - Green provenance = reflected C3 Green form`.

Consequently the scalar Wronskian of the synthesized readouts is the reflected
C3 Green form plus exactly two retained channels:

1. the public Green provenance defect;
2. the ordered cross-edge provenance introduced by scalar synthesis.

Thus the remaining scalar boundary seam is equivalent to cancellation of
those two explicit channels.  No zero, positivity, or confinement assumption
is used.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary

/-- Canonical arithmetic enriched pair. -/
def canonicalEnrichedTfvdScalarTracePair
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    EnrichedTfvdValueLogJetPair :=
  canonicalEnrichedTfvdValueLogJetPair kappa omega s

/-- Canonical transported pair data. -/
def canonicalEnrichedTfvdScalarTraceData
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    FiniteC3EnrichedTfvdPairTransportData M :=
  finiteC3EnrichedTfvdPairTransport M kappa omega s
    (canonicalEnrichedTfvdScalarTracePair kappa omega s)

/-- The four edge legs before scalar synthesis. -/
def canonicalEnrichedTfvdReflectedLegs
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    ReflectedBoundarySynthesisData (Fin M × Fin 2) :=
  let pair := canonicalEnrichedTfvdScalarTracePair kappa omega s
  {
    left := enrichedTfvdBoundaryEdgeLeft M kappa omega pair
    right := enrichedTfvdBoundaryEdgeRight M kappa omega pair
    jetLeft := enrichedTfvdBoundaryEdgeJetLeft M kappa omega pair
    jetRight := enrichedTfvdBoundaryEdgeJetRight M kappa omega pair
  }

/-- Exact four synthesis equalities still required to identify the scalar
readouts with the reflected edge ledger.  The statement contains no Green or
positivity conclusion. -/
structure HasCanonicalEnrichedTfvdReflectedSynthesis
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : Prop where
  left_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalEnrichedTfvdReflectedLegs M kappa omega s).left mr) =
      (starRingEnd ℂ)
        (canonicalEnrichedTfvdScalarTraceData M kappa omega s).logJetReadout
  right_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalEnrichedTfvdReflectedLegs M kappa omega s).right mr) =
      (starRingEnd ℂ)
        (canonicalEnrichedTfvdScalarTraceData M kappa omega s).valueReadout
  jetLeft_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalEnrichedTfvdReflectedLegs M kappa omega s).jetLeft mr) =
      (canonicalEnrichedTfvdScalarTraceData M kappa omega s).logJetReadout
  jetRight_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalEnrichedTfvdReflectedLegs M kappa omega s).jetRight mr) =
      (canonicalEnrichedTfvdScalarTraceData M kappa omega s).valueReadout

/-- Canonical ordered cross-edge synthesis provenance. -/
def canonicalEnrichedTfvdScalarCrossProvenance
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  let legs := canonicalEnrichedTfvdReflectedLegs M kappa omega s
  twoLegBoundaryCrossProvenance
    legs.left legs.right legs.jetLeft legs.jetRight

/-- Under the four explicit synthesis equalities, the canonical scalar trace
is the public reflected C3 Green form plus Green provenance and cross-edge
provenance. -/
theorem canonicalEnrichedTfvdScalarTrace_eq_green_add_provenance
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ)
    (hsynth :
      HasCanonicalEnrichedTfvdReflectedSynthesis M kappa omega s) :
    scalarBoundaryWedge
        (canonicalEnrichedTfvdScalarTraceData M kappa omega s).valueReadout
        (canonicalEnrichedTfvdScalarTraceData M kappa omega s).logJetReadout =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        (finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
          canonicalEnrichedTfvdScalarCrossProvenance
            M kappa omega s) := by
  let pair := canonicalEnrichedTfvdScalarTracePair kappa omega s
  let data := canonicalEnrichedTfvdScalarTraceData M kappa omega s
  let legs := canonicalEnrichedTfvdReflectedLegs M kappa omega s
  have hlocal :
      (∑ mr : Fin M × Fin 2,
        sameSEdgeBoundaryWedge
          (legs.left mr) (legs.right mr)
          (legs.jetLeft mr) (legs.jetRight mr)) =
        finiteC3EnrichedTfvdPairBoundaryForm M data := by
    simpa [pair, data, legs,
      canonicalEnrichedTfvdScalarTracePair,
      canonicalEnrichedTfvdScalarTraceData,
      canonicalEnrichedTfvdReflectedLegs] using
      (sum_enrichedTfvdBoundaryEdges_eq_pairBoundaryForm
        M kappa omega s pair)
  have htrace :=
    scalarBoundaryWedge_eq_enrichedTfvdBoundary_add_crossProvenance
      M data legs hsynth.left_sum hsynth.right_sum
        hsynth.jetLeft_sum hsynth.jetRight_sum hlocal
  have hgreen :=
    finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
      M hkappa omega homega s
  unfold finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary at hgreen
  unfold canonicalEnrichedTfvdScalarCrossProvenance
  dsimp only
  change scalarBoundaryWedge data.valueReadout data.logJetReadout = _
  rw [htrace]
  linear_combination hgreen

/-- Exact canonical boundary criterion: scalar trace equals the reflected C3
Green form iff the two explicit provenance channels cancel. -/
theorem canonicalEnrichedTfvdScalarTrace_eq_green_iff_provenance_cancel
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ)
    (hsynth :
      HasCanonicalEnrichedTfvdReflectedSynthesis M kappa omega s) :
    scalarBoundaryWedge
        (canonicalEnrichedTfvdScalarTraceData M kappa omega s).valueReadout
        (canonicalEnrichedTfvdScalarTraceData M kappa omega s).logJetReadout =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) ↔
      finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s +
        canonicalEnrichedTfvdScalarCrossProvenance M kappa omega s = 0 := by
  rw [canonicalEnrichedTfvdScalarTrace_eq_green_add_provenance
    M hkappa omega homega s hsynth]
  constructor
  · intro h
    apply add_left_cancel
    simpa using h
  · intro h
    rw [h, add_zero]

end

end CarrySelfAdjointOperator

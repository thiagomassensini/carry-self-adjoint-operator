import CarrySelfAdjointOperator.EnrichedTfvdBoundaryEdgeFlattening
import CarrySelfAdjointOperator.ReflectedScalarBoundaryTrace
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import Mathlib.Tactic

/-!
# Canonical enriched boundary synthesis probe

This file asks whether the actual two-edge flattening of the canonical
arithmetic value/log-jet pair already synthesizes the four reflected scalar
legs used by the completed scalar Wronskian.

No synthesis premise is introduced.  The declaration is intentionally a
kernel probe: if definitional reduction and the existing canonical readout
theorems do not close it, GitHub Actions exposes the exact four residual
identities.
-/

open scoped BigOperators ComplexConjugate

namespace CarrySelfAdjointOperator

noncomputable section

open CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk

/-- Canonical arithmetic pair used by the probe. -/
def canonicalBoundarySynthesisPair
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    EnrichedTfvdValueLogJetPair :=
  canonicalEnrichedTfvdValueLogJetPair kappa omega s

/-- Canonical finite transport data used by the probe. -/
def canonicalBoundarySynthesisData
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    FiniteC3EnrichedTfvdPairTransportData M :=
  finiteC3EnrichedTfvdPairTransport M kappa omega s
    (canonicalBoundarySynthesisPair kappa omega s)

/-- Actual flattened edge legs of the canonical arithmetic pair. -/
def canonicalBoundarySynthesisLegs
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    ReflectedBoundarySynthesisData (Fin M × Fin 2) :=
  let pair := canonicalBoundarySynthesisPair kappa omega s
  {
    left := enrichedTfvdBoundaryEdgeLeft M kappa omega pair
    right := enrichedTfvdBoundaryEdgeRight M kappa omega pair
    jetLeft := enrichedTfvdBoundaryEdgeJetLeft M kappa omega pair
    jetRight := enrichedTfvdBoundaryEdgeJetRight M kappa omega pair
  }

/-- Exact four synthesis identities under test. -/
structure CanonicalBoundarySynthesisIdentities
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : Prop where
  left_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalBoundarySynthesisLegs M kappa omega s).left mr) =
      (starRingEnd ℂ)
        (canonicalBoundarySynthesisData M kappa omega s).logJetReadout
  right_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalBoundarySynthesisLegs M kappa omega s).right mr) =
      (starRingEnd ℂ)
        (canonicalBoundarySynthesisData M kappa omega s).valueReadout
  jetLeft_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalBoundarySynthesisLegs M kappa omega s).jetLeft mr) =
      (canonicalBoundarySynthesisData M kappa omega s).logJetReadout
  jetRight_sum :
    (∑ mr : Fin M × Fin 2,
      (canonicalBoundarySynthesisLegs M kappa omega s).jetRight mr) =
      (canonicalBoundarySynthesisData M kappa omega s).valueReadout

/-- Unconditional kernel probe.  GitHub Actions should either prove the four
identities from the pinned graph or stop at their literal residual forms. -/
theorem canonicalBoundarySynthesisIdentities_unconditional_probe
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    CanonicalBoundarySynthesisIdentities M kappa omega s := by
  constructor <;>
    simp [canonicalBoundarySynthesisLegs,
      canonicalBoundarySynthesisData,
      canonicalBoundarySynthesisPair,
      finiteC3EnrichedTfvdPairTransport,
      enrichedTfvdBoundaryEdgeLeft,
      enrichedTfvdBoundaryEdgeRight,
      enrichedTfvdBoundaryEdgeJetLeft,
      enrichedTfvdBoundaryEdgeJetRight]

end

end CarrySelfAdjointOperator
